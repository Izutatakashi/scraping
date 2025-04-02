import tkinter as tk
from tkinter import ttk, scrolledtext, filedialog, messagebox, Menu, Text, font
import threading
import queue
import requests
from bs4 import BeautifulSoup
from bs4.element import Comment
import re
import os
import time
import datetime
import json
import csv
import random
import hashlib
import urllib.parse
import socket
import ssl
import logging
import zipfile
import shutil
import io
from urllib.parse import urlparse, urljoin, urlsplit, urlunsplit
from collections import defaultdict, Counter
import tempfile
import webbrowser
import platform
try:
    from PIL import Image, ImageTk
except ImportError:
    pass
from io import BytesIO
import traceback
import signal
try:
    import ctypes
except ImportError:
    pass
from functools import lru_cache, partial
import pickle

# 必要なライブラリがインストールされていない場合、インストールする関数
def install_required_packages():
    required_packages = [
        'beautifulsoup4', 'requests', 'Pillow', 'PyPDF2', 
        'lxml', 'chardet'
    ]
    
    try:
        import pip
        for package in required_packages:
            try:
                __import__(package)
            except ImportError:
                print(f"Installing {package}...")
                pip.main(['install', package])
    except Exception as e:
        print(f"Error installing packages: {e}")
        return False
    return True

# PyPDF2をインポートして、PDFサポートを追加
try:
    import PyPDF2
    PDF_SUPPORT = True
except ImportError:
    PDF_SUPPORT = False
    print("PyPDF2 not installed. PDF extraction features will be limited.")

# ロギングの設定
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    filename='web_extractor.log'
)
logger = logging.getLogger('WebExtractor')

# キャッシュディレクトリの設定
CACHE_DIR = os.path.join(os.path.expanduser("~"), ".web_extractor_cache")
if not os.path.exists(CACHE_DIR):
    os.makedirs(CACHE_DIR)

# ユーザーエージェントのリスト（ランダムローテーション用）
USER_AGENTS = [
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/14.1.1 Safari/605.1.15',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:90.0) Gecko/20100101 Firefox/90.0',
    'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/92.0.4515.107 Safari/537.36',
    'Mozilla/5.0 (iPhone; CPU iPhone OS 14_6 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/14.0 Mobile/15E148 Safari/604.1'
]

# グローバルキャッシュ
url_cache = {}
dns_cache = {}
content_type_cache = {}

def get_random_user_agent():
    return random.choice(USER_AGENTS)

class URL:
    """URLの正規化と検証を行うクラス"""
    
    @staticmethod
    def normalize(url):
        """URLを正規化する"""
        if not url:
            return None
            
        url = url.strip()
        
        # プロトコルの追加
        if not url.startswith(('http://', 'https://')):
            url = 'https://' + url
        
        try:
            # URLをパースして再構築（正規化）
            parsed = urlsplit(url)
            
            # ドメイン部分の正規化（大文字を小文字に、末尾のドットを削除）
            netloc = parsed.netloc.lower().rstrip('.')
            
            # www.のあるなしを統一（www.なしに統一）
            if netloc.startswith('www.'):
                netloc = netloc[4:]
            
            # パスの正規化（重複するスラッシュの除去、相対パスの解決）
            path = re.sub(r'/+', '/', parsed.path)
            if not path:
                path = '/'
            elif path != '/' and path.endswith('/'):
                path = path.rstrip('/')
            
            # 余分なクエリパラメータの削除（トラッキングパラメータなど）
            query_params = urllib.parse.parse_qsl(parsed.query)
            filtered_params = [(k, v) for k, v in query_params if k.lower() not in 
                              ['utm_source', 'utm_medium', 'utm_campaign', 'utm_term', 'utm_content']]
            query = urllib.parse.urlencode(filtered_params)
            
            # フラグメントの除去（通常はページ内リンクなので）
            fragment = ''
            
            # 正規化されたURLを再構築
            normalized_url = urlunsplit((parsed.scheme, netloc, path, query, fragment))
            
            return normalized_url
        except Exception as e:
            logger.error(f"URL正規化エラー: {e} - URL: {url}")
            return None
    
    @staticmethod
    def is_valid(url):
        """URLが有効かどうかを判定"""
        if not url:
            return False
            
        try:
            result = urlparse(url)
            return all([result.scheme, result.netloc])
        except:
            return False
    
    @staticmethod
    def get_domain(url):
        """URLのドメイン部分を取得"""
        try:
            return urlparse(url).netloc
        except:
            return None
    
    @staticmethod
    def get_url_hash(url):
        """URLのハッシュ値を取得（重複チェック用）"""
        return hashlib.md5(url.encode('utf-8')).hexdigest()
    
    @staticmethod
    def is_same_url(url1, url2):
        """2つのURLが実質的に同じかどうかを判定"""
        norm1 = URL.normalize(url1)
        norm2 = URL.normalize(url2)
        return norm1 == norm2
    
    @staticmethod
    def resolve_relative_url(base_url, relative_url):
        """相対URLを絶対URLに変換"""
        return urljoin(base_url, relative_url)
    
    @staticmethod
    @lru_cache(maxsize=1024)
    def get_content_type(url, timeout=5):
        """URLのコンテンツタイプを取得"""
        # キャッシュを確認
        if url in content_type_cache:
            return content_type_cache[url]
            
        try:
            # HEADリクエストでコンテンツタイプを確認
            headers = {'User-Agent': get_random_user_agent()}
            response = requests.head(url, headers=headers, timeout=timeout, allow_redirects=True)
            
            # レスポンスヘッダーからコンテンツタイプを取得
            content_type = response.headers.get('Content-Type', '').lower()
            
            # キャッシュに保存
            content_type_cache[url] = content_type
            
            return content_type
        except Exception as e:
            logger.error(f"コンテンツタイプ取得エラー: {e} - URL: {url}")
            return None
    
    @staticmethod
    def is_pdf_url(url):
        """URLがPDFファイルを指すかどうかを判定"""
        # URL拡張子ベースの判定
        if url.lower().endswith('.pdf'):
            return True
            
        # コンテンツタイプベースの判定
        content_type = URL.get_content_type(url)
        if content_type and 'application/pdf' in content_type:
            return True
            
        return False
    
    @staticmethod
    def categorize_url(url):
        """URLのカテゴリを判定（文書、画像、動画など）"""
        url_lower = url.lower()
        
        # 拡張子ベースの判定
        if re.search(r'\.(pdf|doc|docx|xls|xlsx|ppt|pptx|txt|rtf|odt|ods|odp)$', url_lower):
            return 'document'
        elif re.search(r'\.(jpg|jpeg|png|gif|bmp|svg|webp|ico|tiff)$', url_lower):
            return 'image'
        elif re.search(r'\.(mp4|avi|mov|wmv|flv|mkv|webm|m4v|mpg|mpeg)$', url_lower):
            return 'video'
        elif re.search(r'\.(mp3|wav|ogg|flac|aac|wma|m4a)$', url_lower):
            return 'audio'
        elif re.search(r'\.(zip|rar|7z|tar|gz|bz2|tgz|xz)$', url_lower):
            return 'archive'
        
        # コンテンツタイプベースの判定
        content_type = URL.get_content_type(url)
        if content_type:
            if 'text/html' in content_type:
                return 'html'
            elif 'application/pdf' in content_type:
                return 'document'
            elif content_type.startswith('image/'):
                return 'image'
            elif content_type.startswith('video/'):
                return 'video'
            elif content_type.startswith('audio/'):
                return 'audio'
            elif 'application/x-zip' in content_type or 'application/x-rar' in content_type:
                return 'archive'
        
        # デフォルトはHTML
        return 'html'

class WebContentExtractor:
    """Webページの本文を抽出するクラス（高度な実装）"""
    
    def __init__(self, options=None):
        # オプション設定
        self.options = {
            'remove_ads': True,
            'remove_navigation': True, 
            'remove_footer': True,
            'remove_related': True,
            'remove_empty_lines': True,
            'normalize_spaces': True,
            'multilingual_support': True,
            'extraction_mode': 'auto',
            'continue_on_error': True,
            'exclude_ecommerce': False,
            'exclude_adult': False,
            'exclude_duplicates': True,  # 重複URL除外フラグを追加
            'extract_metadata': True,    # メタデータ抽出フラグ
            'extract_images': False,     # 画像抽出フラグ
            'max_connections': 10,       # 同時接続数
            'timeout': 30,               # タイムアウト（秒）
            'cache_enabled': True,       # キャッシュ有効化フラグ
            'user_agent_rotation': True, # UAローテーションフラグ
            'extract_pdf_text': True     # PDF抽出フラグ
        }
        
        # ユーザー指定のオプションを適用
        if options:
            self.options.update(options)
        
        # セッション（再利用可能なHTTP接続）
        self.session = requests.Session()
        
        # 本文検出に用いる優先セレクタ（日本語サイトと一般サイト両方に対応）
        self.content_selectors = [
            # 一般的な記事コンテナ
            'article', 'main', '[role="main"]', '.article', '.post', '.entry',
            '.article-body', '.article-content', '.post-content', '.entry-content',
            '.main-content', '.content', '.page-content', '.blog-content',
            # 日本語サイト向け
            '.article-body', '.entry-body', '.post-body', '.content-area',
            '.article-detail', '.post-content', '.post-entry',
            # 技術ブログなど特殊なサイト向け
            '.markdown-body', '.post-detail', '.post-text', '.post__content',
            '.story-body', '.story-content', '.news-detail', '.news-content'
        ]
        
        # 除外するタグ（不要な要素）
        self.exclude_tags = [
            'script', 'style', 'noscript', 'iframe', 'form', 'nav', 'header', 'footer',
            'aside', 'button', 'svg', 'template', 'meta', 'link'
        ]
        
        # 除外するクラス名/ID（部分一致で判定）
        self.exclude_classes = [
            'ad', 'ads', 'advertisement', 'banner', 'share', 'sidebar', 'widget',
            'footer', 'header', 'menu', 'nav', 'related', 'recommend', 'promotion',
            'social', 'comment', 'meta', 'tag', 'cookie', 'popup', 'subscribe',
            'breadcrumb', 'pager', 'pagination', 'author-info', 'author-bio',
            # 日本語サイト向け
            'サイドバー', 'ヘッダー', 'フッター', '広告', 'シェア', '関連記事',
            'おすすめ', 'メニュー', 'ナビ', 'コメント'
        ]
        
        # 本文に含まれない可能性が高いテキストパターン
        self.boilerplate_patterns = [
            # コピーライト、ライセンス
            r'copyright|©|\(c\)|\d{4}[-\d{4}]?\s+all\s+rights\s+reserved',
            r'プライバシーポリシー|利用規約|サイトマップ',
            r'privacy policy|terms of (use|service)|site map',
            # SNSシェア関連
            r'share|tweet|facebook|twitter|pocket|hatena|line',
            r'シェア|ツイート|いいね',
            # ナビゲーション関連
            r'previous|next|home|top|back to top',
            r'前へ|次へ|ホーム|トップ|ページトップへ',
            # 広告、プロモーション
            r'\[PR\]|\[広告\]|\[Advertisement\]|\[Sponsored\]',
            # 日付関連
            r'投稿日|公開日|更新日|作成日',
            r'published (on|at)|posted (on|at)|updated (on|at)'
        ]

        # Eコマースサイト判定用ドメインパターン
        self.ecommerce_patterns = [
            'amazon', 'rakuten', 'yahoo.co.jp/shopping', 'shopping.yahoo',
            'ebay', 'aliexpress', 'mercari', 'paypay.ne.jp', 'zozo', 
            'qoo10', 'ponpare', 'auction', 'store', 'shop.', 'cart', 
            'checkout', 'payment', 'order', 'shop', 'mall', 'market'
        ]
        
        # アダルトサイト判定用ドメインパターン
        self.adult_patterns = [
            'porn', 'xxx', 'adult', 'sex', 'hentai', 'xvideos', 'pornhub',
            'xhamster', 'youporn', 'redtube', 'tube8', 'dmm.co.jp/adult',
            'r18', 'javhd', 'fc2.com/adult', 'dlsite.com/maniax'
        ]
        
        # サイト特化型抽出ルール
        self.site_specific_rules = {
            'wikipedia.org': {
                'content_selector': '#mw-content-text',
                'exclude_selectors': ['.mw-editsection', '.reference', '.noprint'],
                'exclude_texts': ['Jump to navigation', 'Jump to search']
            },
            'news.yahoo.co.jp': {
                'content_selector': '.article_body, .highLightSearchTarget',
                'exclude_selectors': ['.promotion_module', '.sns_module', '.recommend_module'],
                'exclude_texts': ['関連記事', 'あなたにおすすめの記事']
            },
            'qiita.com': {
                'content_selector': '.it-MdContent',
                'exclude_selectors': ['.it-Footer', '.toc-container', '.socialButtons'],
                'exclude_texts': ['この記事は最終更新日から', 'あとで読む']
            },
            'note.com': {
                'content_selector': '.note-common-styles__textnote-body',
                'exclude_selectors': ['.o-noteContentText__footer', '.o-noteStatusLabelGroup'],
                'exclude_texts': ['この記事が気に入ったら、サポートをしてみませんか']
            },
            'hatena.ne.jp': {
                'content_selector': '.entry-content',
                'exclude_selectors': ['.share-buttons', '.entry-footer-section'],
                'exclude_texts': ['この記事に', 'ブックマークしている']
            },
            'github.com': {
                'content_selector': '.markdown-body',
                'exclude_selectors': ['.anchor', '.user-mention', '.gist'],
                'exclude_texts': []
            },
            'zenn.dev': {
                'content_selector': '.znc',
                'exclude_selectors': ['.commentContainer', '.articleActions'],
                'exclude_texts': ['この記事は', '前へ']
            }
        }

        # HTTPリクエスト用のヘッダー
        self.base_headers = {
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8',
            'Accept-Language': 'ja,en-US;q=0.9,en;q=0.8',
            'Accept-Encoding': 'gzip, deflate, br',
            'Upgrade-Insecure-Requests': '1',
            'Sec-Fetch-Dest': 'document',
            'Sec-Fetch-Mode': 'navigate',
            'Sec-Fetch-Site': 'none',
            'Sec-Fetch-User': '?1'
        }
        
        # 処理済みURLのハッシュセット（重複検出用）
        self.processed_url_hashes = set()
        
        # URL分類用のコンテナ
        self.categorized_urls = {
            'html': set(),
            'document': set(),
            'pdf': set(),
            'image': set(),
            'video': set(),
            'audio': set(),
            'archive': set(),
            'ecommerce': set(),
            'adult': set(),
            'invalid': set(),
            'duplicate': set()
        }
        
        # キャッシュシステム初期化
        self.cache = {}
        if self.options['cache_enabled']:
            self.load_cache()
    
    def get_headers(self):
        """リクエスト用のヘッダーを生成"""
        headers = self.base_headers.copy()
        if self.options['user_agent_rotation']:
            headers['User-Agent'] = get_random_user_agent()
        else:
            headers['User-Agent'] = USER_AGENTS[0]
        return headers
    
    def load_cache(self):
        """キャッシュをロード"""
        cache_file = os.path.join(CACHE_DIR, 'extractor_cache.pkl')
        try:
            if os.path.exists(cache_file):
                with open(cache_file, 'rb') as f:
                    self.cache = pickle.load(f)
                logger.info(f"キャッシュをロードしました: {len(self.cache)}件")
        except Exception as e:
            logger.error(f"キャッシュのロード中にエラーが発生しました: {e}")
            self.cache = {}
    
    def save_cache(self):
        """キャッシュを保存"""
        cache_file = os.path.join(CACHE_DIR, 'extractor_cache.pkl')
        try:
            # キャッシュが大きくなりすぎないようにする（最大1000件）
            if len(self.cache) > 1000:
                # 古い順に削除
                cache_items = sorted(self.cache.items(), key=lambda x: x[1].get('timestamp', 0))
                self.cache = dict(cache_items[-1000:])
            
            with open(cache_file, 'wb') as f:
                pickle.dump(self.cache, f)
            logger.info(f"キャッシュを保存しました: {len(self.cache)}件")
        except Exception as e:
            logger.error(f"キャッシュの保存中にエラーが発生しました: {e}")
    
    def fetch_url(self, url, timeout=None):
        """URLからHTMLコンテンツを取得（キャッシュ対応）"""
        if timeout is None:
            timeout = self.options['timeout']
        
        # URL正規化
        normalized_url = URL.normalize(url)
        if not normalized_url:
            raise ValueError(f"無効なURL形式です: {url}")
        
        # キャッシュチェック
        url_hash = URL.get_url_hash(normalized_url)
        if self.options['cache_enabled'] and url_hash in self.cache:
            cache_entry = self.cache[url_hash]
            # キャッシュの有効期限（1日）
            if time.time() - cache_entry.get('timestamp', 0) < 86400:
                logger.info(f"キャッシュから取得: {normalized_url}")
                return cache_entry['content']
        
        # URLのカテゴリをチェック
        url_category = URL.categorize_url(normalized_url)
        
        # PDFの場合、別処理
        if url_category == 'document' and URL.is_pdf_url(normalized_url):
            if self.options['extract_pdf_text'] and PDF_SUPPORT:
                return self.extract_pdf_text(normalized_url)
            else:
                raise ValueError(f"PDFからのテキスト抽出が無効化されています: {normalized_url}")
        
        # HTML以外のドキュメントの場合はエラー
        if url_category != 'html' and url_category != 'document':
            raise ValueError(f"このURLタイプはサポートされていません: {url_category} - {normalized_url}")
        
        try:
            # ヘッダーの準備
            headers = self.get_headers()
            
            # リクエスト送信（エラーハンドリング強化版）
            try:
                response = self.session.get(
                    normalized_url, 
                    headers=headers, 
                    timeout=timeout,
                    verify=True  # SSL証明書を検証
                )
                response.raise_for_status()  # エラーチェック
            except requests.exceptions.SSLError:
                # SSL証明書エラーの場合、検証をスキップして再試行
                logger.warning(f"SSL証明書エラーのため検証をスキップして再試行: {normalized_url}")
                response = self.session.get(
                    normalized_url, 
                    headers=headers, 
                    timeout=timeout,
                    verify=False
                )
                response.raise_for_status()
            
            # エンコーディングの検出と設定
            if 'charset=' in response.headers.get('Content-Type', '').lower():
                # Content-Typeヘッダーからエンコーディングを取得
                pass  # requestsが自動的に検出します
            else:
                # エンコーディングを自動検出
                response.encoding = response.apparent_encoding
            
            # レスポンスボディを取得
            html_content = response.text
            
            # キャッシュに保存
            if self.options['cache_enabled']:
                self.cache[url_hash] = {
                    'content': html_content,
                    'timestamp': time.time(),
                    'headers': dict(response.headers)
                }
                # 定期的にキャッシュを保存
                if len(self.cache) % 10 == 0:
                    self.save_cache()
            
            return html_content
            
        except requests.exceptions.Timeout:
            raise TimeoutError(f"タイムアウト: {timeout}秒以内に応答がありませんでした。")
        except requests.exceptions.TooManyRedirects:
            raise ValueError(f"リダイレクトが多すぎます: {normalized_url}")
        except requests.exceptions.RequestException as e:
            raise Exception(f"URLの取得に失敗しました: {e}")
    
    def extract_pdf_text(self, url):
        """PDFからテキストを抽出"""
        if not PDF_SUPPORT:
            raise ValueError("PDFサポートが有効ではありません。PyPDF2をインストールしてください。")
        
        try:
            # PDFファイルをダウンロード
            headers = self.get_headers()
            response = requests.get(url, headers=headers, timeout=self.options['timeout'])
            response.raise_for_status()
        
            # PDFをメモリ上で開く
            pdf_file = io.BytesIO(response.content)
        
            # PyPDF2でテキスト抽出
            pdf_reader = PyPDF2.PdfFileReader(pdf_file)
        
            # ページ数取得
            num_pages = pdf_reader.getNumPages()
        
            # 各ページからテキストを抽出
            text_content = ""
            for page_num in range(num_pages):
                page = pdf_reader.getPage(page_num)
                text_content += page.extractText() + "\n\n"
        
            # テキストがほとんど抽出できなかった場合
            if len(text_content.strip()) < 100:
                raise ValueError("PDFからのテキスト抽出に失敗しました。テキストレイヤーがないか、スキャンされたPDFの可能性があります。")
        
            # HTMLタグ風のフォーマットを作成
            html_content = f"""
    <!DOCTYPE html>
    <html>
    <head>
        <title>PDF抽出テキスト: {url}</title>
    </head>
    <body>
        <div class="pdf-content">
            {text_content}
        </div>
    </body>
    </html>
    """

            return html_content
        
        except Exception as e:
            raise Exception(f"PDFの処理中にエラーが発生しました: {e}")
    
    def is_ecommerce_site(self, url):
        """URLがEコマースサイトかどうかを判定"""
        if not self.options.get('exclude_ecommerce'):
            return False
            
        try:
            domain = URL.get_domain(url).lower()
            return any(pattern in domain for pattern in self.ecommerce_patterns)
        except:
            return False

    def is_adult_site(self, url):
        """URLがアダルトサイトかどうかを判定"""
        if not self.options.get('exclude_adult'):
            return False
            
        try:
            domain = URL.get_domain(url).lower()
            path = urlparse(url).path.lower()
            return any(pattern in domain or pattern in path for pattern in self.adult_patterns)
        except:
            return False
    
    def is_duplicate_url(self, url):
        """URLが重複しているかどうかを判定"""
        if not self.options.get('exclude_duplicates'):
            return False
            
        normalized_url = URL.normalize(url)
        if not normalized_url:
            return False
            
        url_hash = URL.get_url_hash(normalized_url)
        is_duplicate = url_hash in self.processed_url_hashes
        
        # 重複でなければハッシュを追加
        if not is_duplicate:
            self.processed_url_hashes.add(url_hash)
            
        return is_duplicate
    
    def extract_main_content(self, html, url):
        """HTMLから記事の本文を抽出する"""
        if not html:
            return None
            
        soup = BeautifulSoup(html, 'html.parser')
        
        # タイトルの抽出
        title = self.extract_title(soup)
        
        # メタデータから説明文を抽出
        metadata = self.extract_metadata(soup) if self.options.get('extract_metadata') else {}
        description = metadata.get('description') or self.extract_description(soup)
        
        # 不要な要素を削除
        self.clean_soup(soup)
        
        # 本文候補を取得（抽出モードに基づいて処理）
        extraction_mode = self.options.get('extraction_mode', 'auto')
        content_element = None
        
        if extraction_mode == 'auto' or extraction_mode == 'readability':
            # Readabilityアルゴリズムライクな抽出
            content_element = self.find_content_element(soup, url)
        
        if not content_element and (extraction_mode == 'auto' or extraction_mode == 'content'):
            # コンテンツセレクタ優先の抽出
            content_element = self.find_content_by_selectors(soup)
        
        if not content_element or extraction_mode == 'fullpage':
            # 全ページコンテンツの抽出
            text = self.extract_full_page_content(soup)
        else:
            # 本文要素が見つかった場合
            text = self.extract_formatted_text(content_element)
        
        # テキストのクリーニング
        text = self.clean_text(text)
        
        # 結果を組み立て
        result = {}
        
        # タイトルと説明を追加
        if title:
            result['title'] = title
        
        if description:
            result['description'] = description
        
        # メタデータを追加
        if self.options.get('extract_metadata') and metadata:
            result['metadata'] = metadata
        
        # 本文を追加
        result['content'] = text
        
        # 画像情報を抽出
        if self.options.get('extract_images') and content_element:
            result['images'] = self.extract_image_info(content_element, url)
        
        # リンク情報を抽出
        if self.options.get('extract_links') and content_element:
            result['links'] = self.extract_link_info(content_element, url)
        
        # フォーマット化されたテキストを構築
        formatted_text = ""
        if title:
            formatted_text += f"{title}\n\n"
        if description:
            formatted_text += f"{description}\n\n"
        formatted_text += text
        
        result['formatted_text'] = formatted_text
        
        return result

    def extract_title(self, soup):
        """ページタイトルを抽出（高度な実装）"""
        title = None
        
        # 最も適切なタイトル要素を探す
        # 1. OGPタイトル (Open Graph Protocol)
        og_title = soup.find('meta', property='og:title')
        if og_title and og_title.get('content'):
            title = og_title.get('content').strip()
        
        # 2. ツイッターカードタイトル
        if not title:
            twitter_title = soup.find('meta', attrs={'name': 'twitter:title'})
            if twitter_title and twitter_title.get('content'):
                title = twitter_title.get('content').strip()
        
        # 3. H1タグ（最初のもののみ）
        if not title:
            h1_tag = soup.find('h1')
            if h1_tag and h1_tag.get_text(strip=True):
                title = h1_tag.get_text(strip=True)
        
        # 4. titleタグ（最後の手段）
        if not title:
            title_tag = soup.find('title')
            if title_tag and title_tag.get_text(strip=True):
                # サイト名を除去する試み
                title_text = title_tag.get_text(strip=True)
                
                # 一般的なセパレータを探す
                separators = [' | ', ' - ', ' :: ', ' » ', ' / ', ' > ']
                for sep in separators:
                    if sep in title_text:
                        parts = title_text.split(sep)
                        # 通常、最初の部分が記事タイトル
                        if len(parts[0]) > 5:  # 短すぎる場合は除外
                            return parts[0].strip()
                
                # セパレータが見つからなければ全体を返す
                title = title_text
        
        # タイトルがなければNone
        return title

    def extract_description(self, soup):
        """メタデータから説明文を抽出（高度な実装）"""
        description = None
        
        # 1. 標準的なmeta description
        meta_desc = soup.find('meta', attrs={'name': 'description'})
        if meta_desc and meta_desc.get('content'):
            description = meta_desc.get('content').strip()
        
        # 2. OGP説明文
        if not description:
            og_desc = soup.find('meta', property='og:description')
            if og_desc and og_desc.get('content'):
                description = og_desc.get('content').strip()
        
        # 3. ツイッターカード説明文
        if not description:
            twitter_desc = soup.find('meta', attrs={'name': 'twitter:description'})
            if twitter_desc and twitter_desc.get('content'):
                description = twitter_desc.get('content').strip()
        
        # 4. 冒頭の段落を探す（最後の手段）
        if not description:
            first_para = soup.find('p')
            if first_para and first_para.get_text(strip=True):
                text = first_para.get_text(strip=True)
                # 短すぎたり長すぎたりする場合は除外
                if 50 <= len(text) <= 300:
                    description = text
                    
        return description
    
    def extract_metadata(self, soup):
        """ページからメタデータを抽出"""
        metadata = {}
        
        # 基本メタデータ
        # タイトル
        metadata['title'] = self.extract_title(soup)
        
        # 説明
        metadata['description'] = self.extract_description(soup)
        
        # 著者
        author_meta = soup.find('meta', attrs={'name': 'author'}) or soup.find('meta', property='article:author')
        if author_meta and author_meta.get('content'):
            metadata['author'] = author_meta.get('content').strip()
        
        # 公開日
        published_meta = (
            soup.find('meta', property='article:published_time') or 
            soup.find('meta', attrs={'name': 'pubdate'}) or
            soup.find('meta', attrs={'name': 'date'})
        )
        if published_meta and published_meta.get('content'):
            metadata['published_date'] = published_meta.get('content').strip()
        
        # 更新日
        modified_meta = soup.find('meta', property='article:modified_time') or soup.find('meta', attrs={'name': 'lastmod'})
        if modified_meta and modified_meta.get('content'):
            metadata['modified_date'] = modified_meta.get('content').strip()
        
        # キーワード
        keywords_meta = soup.find('meta', attrs={'name': 'keywords'})
        if keywords_meta and keywords_meta.get('content'):
            metadata['keywords'] = keywords_meta.get('content').strip()
        
        # ページタイプ
        og_type = soup.find('meta', property='og:type')
        if og_type and og_type.get('content'):
            metadata['type'] = og_type.get('content').strip()
        
        # 言語
        lang_attr = soup.find('html').get('lang') if soup.find('html') else None
        if lang_attr:
            metadata['language'] = lang_attr.strip()
        
        # OGP画像
        og_image = soup.find('meta', property='og:image')
        if og_image and og_image.get('content'):
            metadata['image'] = og_image.get('content').strip()
        
        # カノニカルURL
        canonical = soup.find('link', rel='canonical')
        if canonical and canonical.get('href'):
            metadata['canonical_url'] = canonical.get('href').strip()
        
        # ファビコン
        favicon = (
            soup.find('link', rel='icon') or 
            soup.find('link', rel='shortcut icon') or
            soup.find('link', rel='apple-touch-icon')
        )
        if favicon and favicon.get('href'):
            metadata['favicon'] = favicon.get('href').strip()
        
        # JSON-LD 構造化データ
        jsonld_scripts = soup.find_all('script', type='application/ld+json')
        if jsonld_scripts:
            structured_data = []
            for script in jsonld_scripts:
                try:
                    json_data = json.loads(script.string)
                    structured_data.append(json_data)
                except:
                    pass
            if structured_data:
                metadata['structured_data'] = structured_data
        
        return metadata
    
    def extract_image_info(self, element, base_url):
        """画像情報を抽出"""
        images = []
        
        # 画像要素を検索
        for img in element.find_all('img'):
            try:
                # 画像のsrc属性を取得
                src = img.get('src')
                if not src:
                    continue
                
                # 相対URLを絶対URLに変換
                img_url = URL.resolve_relative_url(base_url, src)
                
                # 画像情報を抽出
                image_info = {
                    'url': img_url,
                    'alt': img.get('alt', ''),
                    'title': img.get('title', '')
                }
                
                # サイズ情報があれば追加
                if img.get('width'):
                    image_info['width'] = img.get('width')
                if img.get('height'):
                    image_info['height'] = img.get('height')
                
                # 画像情報を追加
                images.append(image_info)
            except:
                continue
        
        return images
    
    def extract_link_info(self, element, base_url):
        """リンク情報を抽出"""
        links = []
        
        # リンク要素を検索
        for a in element.find_all('a', href=True):
            try:
                # リンクのhref属性を取得
                href = a.get('href')
                if not href:
                    continue
                
                # 相対URLを絶対URLに変換
                link_url = URL.resolve_relative_url(base_url, href)
                
                # リンク情報を抽出
                link_info = {
                    'url': link_url,
                    'text': a.get_text(strip=True),
                    'title': a.get('title', '')
                }
                
                # target属性があれば追加
                if a.get('target'):
                    link_info['target'] = a.get('target')
                
                # rel属性があれば追加
                if a.get('rel'):
                    link_info['rel'] = a.get('rel')
                
                # リンク情報を追加
                links.append(link_info)
            except:
                continue
        
        return links

    def clean_soup(self, soup):
        """不要な要素をHTML構造から削除（高度な実装）"""
        # スキップするべき無害な要素のセット
        safe_tags = {'html', 'body', 'div', 'span', 'section', 'article', 'main', 'p', 'br', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'ul', 'ol', 'li', 'table', 'tr', 'td', 'th', 'thead', 'tbody', 'a', 'img', 'figure', 'figcaption', 'blockquote', 'pre', 'code', 'em', 'strong', 'mark', 'time'}
        
        # 不要なタグを削除
        for tag in self.exclude_tags:
            for element in soup.find_all(tag):
                element.decompose()
        
        # 不要なクラスやIDを持つ要素を削除
        for exclude_class in self.exclude_classes:
            # クラス名部分一致で削除
            for element in soup.find_all(class_=lambda c: c and exclude_class.lower() in c.lower()):
                if element.name not in safe_tags:
                    element.decompose()
            
            # ID部分一致で削除
            for element in soup.find_all(id=lambda i: i and exclude_class.lower() in i.lower()):
                if element.name not in safe_tags:
                    element.decompose()
        
        # コメントを削除
        for comment in soup.find_all(text=lambda text: isinstance(text, Comment)):
            comment.extract()
        
        # 空のdiv要素を削除（少なくとも意味のある要素が1つ以上含まれているかチェック）
        for div in soup.find_all('div'):
            # 意味のあるタグ
            meaningful_tags = div.find_all(['p', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'ul', 'ol', 'table', 'blockquote', 'pre', 'img'])
            meaningful_text = div.get_text(strip=True)
            
            if not meaningful_tags and len(meaningful_text) < 50:
                div.decompose()
        
        # インラインスタイルを削除
        for element in soup.find_all(style=True):
            del element['style']
        
        # オンクリック属性を削除
        for element in soup.find_all(onclick=True):
            del element['onclick']
            
        return soup

    def find_content_by_selectors(self, soup):
        """セレクタベースで本文要素を検出"""
        # 優先セレクタから検索
        for selector in self.content_selectors:
            try:
                if selector.startswith('.'):
                    # クラス名
                    elements = soup.find_all(class_=selector[1:])
                elif selector.startswith('#'):
                    # ID
                    elements = [soup.find(id=selector[1:])]
                elif selector.startswith('['):
                    # 属性 [role="main"] などの形式
                    attr_name = selector[1:].split('=')[0]
                    attr_value = selector.split('=')[1].strip('"').strip(']')
                    elements = soup.find_all(attrs={attr_name: attr_value})
                else:
                    # タグ名
                    elements = soup.find_all(selector)
                
                # 長いテキストを含む最初の要素を返す
                for element in elements:
                    if element and len(element.get_text(strip=True)) > 200:
                        return element
            except:
                continue
        
        return None

    def find_content_element(self, soup, url):
        """本文要素を検出 (Readabilityアルゴリズムに近い方法)"""
        # ドメイン特化チェック
        domain = URL.get_domain(url)
        special_element = self.check_for_special_domain(soup, domain)
        if special_element:
            return special_element
        
        # セレクタベースの検索
        selector_element = self.find_content_by_selectors(soup)
        if selector_element:
            return selector_element
        
        # スコアリングアルゴリズムで最適な要素を検出
        return self.find_content_by_scoring(soup)

    def extract_full_page_content(self, soup):
        """ページ全体からテキストを抽出"""
        # フォーマットに関係する重要な要素を抽出
        headings = []
        for h in soup.find_all(['h1', 'h2', 'h3', 'h4', 'h5', 'h6']):
            text = h.get_text(strip=True)
            if text and len(text) > 5:
                level = int(h.name[1])
                headings.append((level, text))
        
        paragraphs = []
        for p in soup.find_all('p'):
            text = p.get_text(strip=True)
            if text and len(text) > 20:
                paragraphs.append(text)
        
        # 整形されたテキストを構築
        result = []
        
        # まず見出しを追加（レベル順）
        headings.sort(key=lambda x: x[0])
        for level, text in headings:
            result.append(f"\n{'#' * level} {text}\n")
        
        # 段落を追加
        for text in paragraphs:
            result.append(text)
        
        # 結合
        return '\n\n'.join(result)

    def check_for_special_domain(self, soup, domain):
        """特定のドメイン向け特殊処理"""
        if not domain:
            return None
            
        # サイト特化型のルールを適用
        for site_domain, rules in self.site_specific_rules.items():
            if site_domain in domain:
                # コンテンツセレクタを取得
                content_selector = rules.get('content_selector')
                if content_selector:
                    # セレクタを適用
                    if ',' in content_selector:
                        # 複数のセレクタがある場合はカンマで区切られている
                        selectors = [s.strip() for s in content_selector.split(',')]
                        for selector in selectors:
                            if selector.startswith('.'):
                                element = soup.find(class_=selector[1:])
                            elif selector.startswith('#'):
                                element = soup.find(id=selector[1:])
                            else:
                                element = soup.find(selector)
                            
                            if element:
                                # 除外セレクタを適用
                                exclude_selectors = rules.get('exclude_selectors', [])
                                for exclude_selector in exclude_selectors:
                                    for excluded in element.select(exclude_selector):
                                        excluded.decompose()
                                
                                return element
                    else:
                        # 単一のセレクタ
                        if content_selector.startswith('.'):
                            element = soup.find(class_=content_selector[1:])
                        elif content_selector.startswith('#'):
                            element = soup.find(id=content_selector[1:])
                        else:
                            element = soup.find(content_selector)
                        
                        if element:
                            # 除外セレクタを適用
                            exclude_selectors = rules.get('exclude_selectors', [])
                            for exclude_selector in exclude_selectors:
                                for excluded in element.select(exclude_selector):
                                    excluded.decompose()
                            
                            return element
        
        # 規定のドメイン特化チェック（後方互換性用）
        if 'wikipedia.org' in domain:
            element = soup.find(id='mw-content-text')
            if element:
                return element
        
        if 'news.yahoo.co.jp' in domain:
            element = soup.find(class_=['article_body', 'highLightSearchTarget'])
            if element:
                return element
                
        if 'qiita.com' in domain:
            element = soup.find(class_=['it-MdContent'])
            if element:
                return element
                
        if 'note.com' in domain:
            element = soup.find(class_=['note-common-styles__textnote-body'])
            if element:
                return element
        
        # GitHub READMEファイル
        if 'github.com' in domain:
            element = soup.find(class_=['markdown-body'])
            if element:
                return element
                
        return None

    def find_content_by_scoring(self, soup):
        """スコアリングアルゴリズムで本文候補を検出（高度な実装）"""
        candidates = []
        
        # 段落要素の親要素を候補として収集
        for p in soup.find_all('p'):
            parent = p.parent
            text_length = len(p.get_text(strip=True))
            
            # 長い段落の親要素のみを候補に追加
            if text_length > 100:
                # 既存の候補かどうかをチェック
                existing = next((c for c in candidates if c['element'] == parent), None)
                if existing:
                    existing['paragraphs'] += 1
                    existing['text_length'] += text_length
                else:
                    candidates.append({
                        'element': parent,
                        'paragraphs': 1,
                        'text_length': text_length,
                        'depth': self.get_element_depth(parent)
                    })
        
        # 候補がない場合
        if not candidates:
            # div要素を検索
            for div in soup.find_all('div'):
                text = div.get_text(strip=True)
                if len(text) > 500:
                    candidates.append({
                        'element': div,
                        'paragraphs': 1,
                        'text_length': len(text),
                        'depth': self.get_element_depth(div)
                    })
        
        # スコアを計算して最良の候補を見つける
        best_candidate = None
        best_score = 0
        
        for candidate in candidates:
            # 基本スコア: テキストの長さと段落数による
            score = candidate['text_length'] * 0.5 + candidate['paragraphs'] * 100
            
            # 深さによる調整（浅すぎる/深すぎる要素にはペナルティ）
            depth = candidate['depth']
            if depth < 3:
                score *= 0.5  # 浅すぎる要素には50%のペナルティ
            elif depth > 10:
                score *= 0.8  # 深すぎる要素には20%のペナルティ
            
            # 見出しがあればボーナス
            headings = candidate['element'].find_all(['h1', 'h2', 'h3', 'h4', 'h5', 'h6'])
            score += len(headings) * 50
            
            # 画像があれば若干のボーナス（多すぎるとペナルティ）
            images = candidate['element'].find_all('img')
            if 1 <= len(images) <= 3:
                score += len(images) * 30
            elif len(images) > 5:
                score -= (len(images) - 5) * 20
            
            # フォームがあればペナルティ
            if candidate['element'].find('form'):
                score -= 300
            
            # リンクが多すぎるとペナルティ
            links = candidate['element'].find_all('a')
            if len(links) > 10:
                score -= (len(links) - 10) * 5
            
            # インラインスタイルがあればペナルティ（広告の可能性）
            if candidate['element'].get('style'):
                score -= 50
            
            # class/id名による調整
            element_class = candidate['element'].get('class', [])
            element_id = candidate['element'].get('id', '')
            
            # コンテンツ系の名前ならボーナス
            content_terms = ['content', 'article', 'post', 'entry', 'main', 'body', 'text']
            for term in content_terms:
                if (element_class and any(term in c.lower() for c in element_class)) or (term in element_id.lower()):
                    score += 100
            
            # 不要なキーワードを含む場合はペナルティ
            element_html = str(candidate['element'])
            for pattern in self.boilerplate_patterns:
                if re.search(pattern, element_html, re.IGNORECASE):
                    score -= 100
            
            if score > best_score:
                best_score = score
                best_candidate = candidate['element']
        
        return best_candidate
    
    def get_element_depth(self, element):
        """要素のDOM深さを計算"""
        depth = 0
        current = element
        while current and current.name != 'html':
            depth += 1
            current = current.parent
        return depth

    def extract_formatted_text(self, element):
        """要素から書式を維持したテキストを抽出（高度な実装）"""
        if not element:
            return ""
        
        # 結果のテキスト
        result = []
        
        # 処理済みのIDを記録（重複処理回避）
        processed_ids = set()
        
        # 見出しと段落を順番に処理
        for child in element.find_all(['h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'p', 'blockquote', 'ul', 'ol', 'li', 'pre', 'code', 'table', 'figure', 'div'], recursive=True):
            # 既に処理済みのIDがあればスキップ
            if 'id' in child.attrs:
                if child['id'] in processed_ids:
                    continue
                processed_ids.add(child['id'])
            
            # 空テキストの場合はスキップ
            text = child.get_text(strip=True)
            if not text:
                continue
                
            if child.name in ['h1', 'h2', 'h3', 'h4', 'h5', 'h6']:
                # 見出し（レベルに応じてフォーマット）
                level = int(child.name[1])
                heading_markers = "#" * level
                result.append(f"\n{heading_markers} {text}\n")
                
            elif child.name == 'p':
                # 段落
                if text:
                    result.append(text)
                    
            elif child.name == 'blockquote':
                # 引用
                if text:
                    # 複数行の引用に対応
                    quoted_lines = []
                    for line in text.split('\n'):
                        quoted_lines.append(f"> {line}")
                    result.append('\n'.join(quoted_lines))
                    
            elif child.name == 'ul':
                # 非順序リスト
                # リスト項目はliタグで処理するため、ここでは何もしない
                pass
                
            elif child.name == 'ol':
                # 順序リスト
                # リスト項目はliタグで処理するため、ここでは何もしない
                pass
                
            elif child.name == 'li':
                # リスト項目
                parent = child.parent
                if parent and parent.name == 'ol':
                    # 順序リスト項目の番号を求める
                    index = 1
                    for sibling in child.previous_siblings:
                        if sibling.name == 'li':
                            index += 1
                    result.append(f"{index}. {text}")
                else:
                    # 非順序リスト項目
                    result.append(f"• {text}")
                    
            elif child.name in ['pre', 'code']:
                # コードブロック
                if text:
                    result.append(f"\n```\n{text}\n```\n")
                    
            elif child.name == 'table':
                # テーブル（簡易ASCII形式に変換）
                table_text = self.format_table(child)
                if table_text:
                    result.append(table_text)
                    
            elif child.name == 'figure':
                # 図（キャプションがあれば追加）
                caption = child.find('figcaption')
                if caption and caption.get_text(strip=True):
                    result.append(f"[図: {caption.get_text(strip=True)}]")
                    
            elif child.name == 'div':
                # div要素は特別扱い（一部の重要なdivのみ処理）
                # 意味のある段落要素や見出しを含むdivのみ処理
                if len(text) > 200:  # 十分な長さのテキストがある
                    # すでに処理したタグが含まれていない場合のみ追加
                    if not child.find_all(['h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'p', 'blockquote', 'ul', 'ol']):
                        result.append(text)
        
        # 結果がない場合は通常のテキスト抽出を実行
        if not result:
            return element.get_text(strip=True)
        
        # 結果を結合
        return '\n\n'.join(result)
    
    def format_table(self, table):
        """テーブル要素をASCII形式にフォーマット"""
        rows = []
        
        # テーブルヘッダーを処理
        headers = []
        for th in table.find_all('th'):
            headers.append(th.get_text(strip=True))
        
        if headers:
            rows.append(headers)
        
        # テーブル本体を処理
        for tr in table.find_all('tr'):
            row = []
            # 各セルを処理
            for td in tr.find_all(['td', 'th']):
                row.append(td.get_text(strip=True))
            
            # 空行でなければ追加
            if any(cell for cell in row):
                rows.append(row)
        
        # 列幅を計算
        if not rows:
            return ""
            
        col_widths = []
        for i in range(len(rows[0])):
            col_width = max((len(row[i]) if i < len(row) else 0) for row in rows) + 2
            col_widths.append(col_width)
        
        # テーブルを構築
        result = []
        
        # ヘッダー行
        if headers:
            header_row = "| " + " | ".join(cell.ljust(width - 2) for cell, width in zip(rows[0], col_widths)) + " |"
            result.append(header_row)
            
            # 区切り行
            separator = "| " + " | ".join("-" * (width - 2) for width in col_widths) + " |"
            result.append(separator)
            
            # データ行
            for row in rows[1:]:
                data_row = "| " + " | ".join((cell.ljust(width - 2) if i < len(row) else "".ljust(width - 2)) for i, (cell, width) in enumerate(zip(row, col_widths))) + " |"
                result.append(data_row)
        else:
            # ヘッダーがない場合はデータのみ
            for row in rows:
                data_row = "| " + " | ".join((cell.ljust(width - 2) if i < len(row) else "".ljust(width - 2)) for i, (cell, width) in enumerate(zip(row, col_widths))) + " |"
                result.append(data_row)
        
        return "\n".join(result)

    def clean_text(self, text):
        """抽出したテキストを整形（高度な実装）"""
        if not text:
            return ""
        
        # オプションに基づいて処理
        if self.options.get('remove_ads', True):
            # 広告・プロモーションの削除
            patterns = [
                r'\[PR\]|\[広告\]|\[Advertisement\]|\[Sponsored\]',
                r'広告|スポンサー|PR|プロモーション',
                r'Sponsored|Advertisement|Promotion',
                r'Advertisements?(\s+by\s+\w+)?',
                r'Sponsored\s+Content',
                r'Promoted\s+(Stories|Content)',
                r'Recommended\s+For\s+You'
            ]
            for pattern in patterns:
                text = re.sub(pattern, '', text, flags=re.IGNORECASE)
        
        if self.options.get('remove_navigation', True):
            # ナビゲーション・メニューの削除
            patterns = [
                r'サイトマップ|プライバシーポリシー|利用規約|お問い合わせ',
                r'ログイン|新規登録|パスワードを忘れた',
                r'検索|Search',
                r'メニュー|ナビゲーション',
                r'ホーム|TOP',
                r'Sign\s+(in|up)',
                r'Log\s+(in|out)',
                r'Create\s+an\s+account',
                r'Forgot\s+password',
                r'Navigation|Menu|Sitemap',
                r'Skip\s+to\s+(content|main)'
            ]
            for pattern in patterns:
                text = re.sub(pattern, '', text, flags=re.IGNORECASE)
        
        if self.options.get('remove_footer', True):
            # フッター・コピーライトの削除
            patterns = [
                r'copyright|©|all\s+rights\s+reserved',
                r'\d{4}-\d{4}\s+\w+\.\s+all\s+rights\s+reserved\.',
                r'powered\s+by\s+\w+',
                r'Copyright\s+©\s+\d{4}[-\d{4}]?',
                r'All\s+Rights\s+Reserved',
                r'Terms\s+of\s+(Use|Service)',
                r'Privacy\s+Policy',
                r'Contact\s+Us'
            ]
            for pattern in patterns:
                text = re.sub(pattern, '', text, flags=re.IGNORECASE)
        
        if self.options.get('remove_related', True):
            # 関連記事・おすすめコンテンツの削除
            patterns = [
                r'関連記事|関連情報|こちらもおすすめ|あわせて読みたい',
                r'関連|おすすめ|人気の記事',
                r'Related\s+Articles|Related\s+Posts|You\s+might\s+also\s+like',
                r'Recommended\s+Articles',
                r'More\s+in\s+[A-Za-z\s]+',
                r'Popular\s+in\s+[A-Za-z\s]+',
                r'Trending\s+Now',
                r'Most\s+Read',
                r'From\s+Our\s+Network'
            ]
            for pattern in patterns:
                text = re.sub(pattern, '', text, flags=re.IGNORECASE)
            
        # 正規表現で不要なパターンを削除（共通処理）
        for pattern in self.boilerplate_patterns:
            text = re.sub(pattern, '', text, flags=re.IGNORECASE)
        
        # 余分な改行、スペースの削除
        # 3つ以上の連続する改行を2つに
        text = re.sub(r'\n{3,}', '\n\n', text)
        
        # 行頭と行末の空白を削除
        lines = [line.strip() for line in text.split('\n')]
        text = '\n'.join(lines)
        
        # 連続する空白を1つに
        if self.options.get('normalize_spaces', True):
            text = re.sub(r' {2,}', ' ', text)
        
        # 空行の最適化
        if self.options.get('remove_empty_lines', True):
            # 空行が3行以上続く場合、2行に減らす
            text = re.sub(r'\n{3,}', '\n\n', text)
        
        # テキストの前後のスペースを削除
        text = text.strip()
        
        # URLをリンク形式に変換
        url_pattern = r'https?://(?:[-\w.]|(?:%[\da-fA-F]{2}))+'
        # f-stringエラーの修正: リテラル置換を使用
        text = re.sub(url_pattern, lambda m: '[' + m.group(0) + '](' + m.group(0) + ')', text)
        
        return text

    def extract_from_url(self, url, timeout=None):
        """URLから本文を抽出する（メイン関数）"""
        if timeout is None:
            timeout = self.options['timeout']
        
        # URL正規化と検証
        normalized_url = URL.normalize(url)
        if not normalized_url:
            raise ValueError(f"無効なURL形式です: {url}")
            
        # 重複チェック
        if self.is_duplicate_url(normalized_url):
            # 重複URLに分類
            self.categorized_urls['duplicate'].add(normalized_url)
            raise ValueError(f"重複URLのため除外されました: {normalized_url}")
        
        # Eコマースサイトの判定
        if self.is_ecommerce_site(normalized_url):
            # Eコマースサイトに分類
            self.categorized_urls['ecommerce'].add(normalized_url)
            raise ValueError(f"Eコマースサイトのため除外されました: {normalized_url}")
            
        # アダルトサイトの判定
        if self.is_adult_site(normalized_url):
            # アダルトサイトに分類
            self.categorized_urls['adult'].add(normalized_url)
            raise ValueError(f"アダルトサイトのため除外されました: {normalized_url}")
        
        # URLのカテゴリをチェック
        url_category = URL.categorize_url(normalized_url)
        
        # カテゴリを記録
        if url_category in self.categorized_urls:
            self.categorized_urls[url_category].add(normalized_url)
        
        # PDFの場合、PDFカテゴリにも追加
        if url_category == 'document' and URL.is_pdf_url(normalized_url):
            self.categorized_urls['pdf'].add(normalized_url)
            if not self.options['extract_pdf_text'] or not PDF_SUPPORT:
                raise ValueError(f"PDFからのテキスト抽出が無効化されています: {normalized_url}")
        
        # HTML以外のコンテンツタイプの場合はエラー
        if url_category not in ['html', 'document']:
            raise ValueError(f"このURLタイプは本文抽出に適していません: {url_category} - {normalized_url}")
        
        # HTMLを取得
        html = self.fetch_url(normalized_url, timeout)
        
        if not html:
            raise ValueError(f"{normalized_url} の取得に失敗しました。")
            
        # 本文抽出
        extraction_result = self.extract_main_content(html, normalized_url)
        
        if not extraction_result or not extraction_result.get('content'):
            raise ValueError(f"{normalized_url} から本文を抽出できませんでした。")
            
        return extraction_result
    
    def process_url_batch(self, urls, max_workers=None, callback=None, error_callback=None, progress_callback=None):
        """複数のURLを一括処理（スレッドプール実装）"""
        # 並列処理の制限（デフォルトはシステムに最適化）
        if max_workers is None:
            max_workers = self.options.get('max_connections', 10)
        
        # URL正規化と重複排除
        normalized_urls = []
        skipped_urls = []
        for url in urls:
            normalized_url = URL.normalize(url)
            if not normalized_url:
                skipped_urls.append(url)
                continue
            
            if self.options.get('exclude_duplicates') and self.is_duplicate_url(normalized_url):
                self.categorized_urls['duplicate'].add(normalized_url)
                skipped_urls.append(url)
                continue
            
            normalized_urls.append(normalized_url)
        
        # 処理用のワーカーを起動
        results = []
        total_urls = len(normalized_urls)
        processed = 0
        
        # プログレスコールバックで初期状態を通知
        if progress_callback:
            progress_callback(None, 0, total_urls, "開始中...")
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
            # URLごとにタスクを投入
            future_to_url = {executor.submit(self.process_single_url, url, callback, error_callback, progress_callback): url for url in normalized_urls}
            
            # 完了したタスクを処理
            for future in concurrent.futures.as_completed(future_to_url):
                url = future_to_url[future]
                try:
                    result = future.result()
                    results.append(result)
                except Exception as e:
                    logger.error(f"URL処理エラー: {url} - {e}")
                    # すでに個別のタスクでエラーハンドリングされているので、ここでは何もしない
                
                # 進捗を更新
                processed += 1
                if progress_callback:
                    progress_callback(url, processed, total_urls, f"処理済み: {processed}/{total_urls}")
        
        # 最終的なカテゴリ別の統計情報を生成
        stats = {category: len(urls) for category, urls in self.categorized_urls.items()}
        
        # 完了通知
        if progress_callback:
            progress_callback(None, total_urls, total_urls, "完了", stats)
        
        return results
    
    def process_single_url(self, url, callback=None, error_callback=None, progress_callback=None):
        """単一URLの処理（並列処理用）"""
        try:
            # 進捗コールバック（URL処理開始）
            if progress_callback:
                progress_callback(url, None, None, "処理中")
            
            # URL処理
            extraction_result = self.extract_from_url(url)
            
            # 結果を整形
            if isinstance(extraction_result, dict):
                content = extraction_result.get('formatted_text', extraction_result.get('content', ''))
            else:
                content = extraction_result
            
            # 結果を構築
            result = {
                'url': url,
                'content': content,
                'raw_result': extraction_result,
                'success': True,
                'timestamp': datetime.datetime.now().isoformat(),
                'category': 'html'  # デフォルト値
            }
            
            # URLカテゴリがあれば追加
            for category, urls in self.categorized_urls.items():
                if url in urls:
                    result['category'] = category
                    break
            
            # 成功コールバック
            if callback:
                callback(result)
            
            return result
            
        except Exception as e:
            logger.exception(f"URL処理エラー: {url}")
            
            # カテゴリ判定を試みる
            category = 'invalid'
            for cat, urls in self.categorized_urls.items():
                if url in urls:
                    category = cat
                    break
            
            # エラー情報を構築
            error_result = {
                'url': url,
                'content': f"エラー: {str(e)}",
                'success': False,
                'error': str(e),
                'error_type': type(e).__name__,
                'timestamp': datetime.datetime.now().isoformat(),
                'category': category
            }
            
            # エラーコールバック
            if error_callback:
                error_callback(error_result)
            
            # 進捗コールバック（エラー）
            if progress_callback:
                progress_callback(url, None, None, f"エラー: {str(e)}")
            
            # エラー時の処理継続判定
            if not self.options.get('continue_on_error', True):
                raise
            
            return error_result

    def combine_results_to_single_file(self, results, format_type='txt', include_headers=True, include_errors=False, separate_sections=True):
    """
    複数の抽出結果を1つのファイルにまとめる
    
    Parameters:
    - results: 抽出結果のリスト（process_url_batchの戻り値）
    - format_type: 出力形式（'txt', 'md', 'html'）
    - include_headers: 各コンテンツの前にヘッダー情報（URL、タイトルなど）を含めるかどうか
    - include_errors: エラー結果も含めるかどうか
    - separate_sections: カテゴリごとにセクション分けするかどうか
    
    Returns:
    - コンバインされたテキスト
    """
    combined_text = ""
    
    # 出力ファイルのヘッダー
    timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    
    if format_type == 'html':
        combined_text += f"""<!DOCTYPE html>
<html>
<head>
    <title>Web テキスト抽出結果</title>
    <meta charset="utf-8">
</head>
<body>
    <h1>Web テキスト抽出結果</h1>
    <p>抽出日時: {timestamp}</p>
    <p>URL件数: {len(results)}件</p>
"""
    elif format_type == 'md':
        combined_text += f"# Web テキスト抽出結果\n\n"
        combined_text += f"抽出日時: {timestamp}\n\n"
        combined_text += f"URL件数: {len(results)}件\n\n"
    else:  # txt
        combined_text += f"=== Web テキスト抽出結果 ===\n\n"
        combined_text += f"抽出日時: {timestamp}\n"
        combined_text += f"URL件数: {len(results)}件\n\n"
        combined_text += f"{'=' * 60}\n\n"
        
        # カテゴリ別に分類
if separate_sections:
    categorized_results = {}
    for result in results:
        # エラー結果をスキップ（オプションによる）
        if not result['success'] and not include_errors:
            continue
        
        category = result.get('category', 'html')
        if category not in categorized_results:
            categorized_results[category] = []
        
        categorized_results[category].append(result)
    
    # 通常のHTMLコンテンツを先に表示
    category_order = ['html', 'document', 'pdf', 'image', 'video', 'audio', 'archive', 'ecommerce', 'adult', 'duplicate', 'invalid']
    
    for category in category_order:
        if category not in categorized_results:
            continue
        
        category_results = categorized_results[category]
        if not category_results:
            continue
        
        # カテゴリヘッダー
        if format_type == 'html':
            combined_text += f"""
<section class="category">
<h2>{category.capitalize()} コンテンツ ({len(category_results)}件)</h2>
"""
        elif format_type == 'md':
            combined_text += f"## {category.capitalize()} コンテンツ ({len(category_results)}件)\n\n"
        else:  # txt
            combined_text += f"=== {category.capitalize()} コンテンツ ({len(category_results)}件) ===\n\n"
        
        # 各結果を追加
        for result in category_results:
            combined_text += self._format_single_result(result, format_type, include_headers)
        
        if format_type == 'html':
            combined_text += """
</section>
"""
        else:
            if format_type == 'md':
                combined_text += "\n---\n\n"
            else:  # txt
                combined_text += f"\n{'=' * 60}\n\n"
else:
    # セクション分けなし - 単純に追加
    for result in results:
        # エラー結果をスキップ（オプションによる）
        if not result['success'] and not include_errors:
            continue
        
        combined_text += self._format_single_result(result, format_type, include_headers)
        
        # セパレータ
        if format_type == 'html':
            combined_text += """
<hr>
"""
        elif format_type == 'md':
            combined_text += "\n---\n\n"
        else:  # txt
            combined_text += f"\n{'=' * 60}\n\n"

# フッター
if format_type == 'html':
    combined_text += """
</body>
</html>
"""

return combined_text
    
    def _format_single_result(self, result, format_type, include_headers):
    """単一の結果をフォーマット"""
    formatted_text = ""
    
    url = result.get('url', '')
    timestamp = result.get('timestamp', '')
    
    # 成功か失敗かによって処理を分ける
    if result.get('success', False):
        # 成功結果の場合
        content = result.get('content', '')
        raw_result = result.get('raw_result', {})
        title = raw_result.get('title', '') if isinstance(raw_result, dict) else ''
        
        if include_headers:
            if format_type == 'html':
                formatted_text += f"""
<div class="result">
    <h2><a href="{url}" target="_blank">{url}</a></h2>
    {f"<h3>{title}</h3>" if title else ""}
    <p class="timestamp">抽出日時: {timestamp}</p>
    <div class="content">
        {content}
    </div>
</div>
"""
            elif format_type == 'md':
                formatted_text += f"### [{url}]({url})\n\n"
                if title:
                    formatted_text += f"#### {title}\n\n"
                formatted_text += f"抽出日時: {timestamp}\n\n"
                formatted_text += f"{content}\n\n"
            else:  # txt
                formatted_text += f"URL: {url}\n"
                if title:
                    formatted_text += f"タイトル: {title}\n"
                formatted_text += f"抽出日時: {timestamp}\n\n"
                formatted_text += f"{content}\n\n"
        else:
            # ヘッダーなし（コンテンツのみ）
            if format_type == 'html':
                formatted_text += f"""
<div class="content">
    {content}
</div>
"""
            else:
                formatted_text += f"{content}\n\n"
    else:
        # エラー結果の場合
        error_message = result.get('error', '不明なエラー')
        
        if format_type == 'html':
            formatted_text += f"""
<div class="result error">
    <h2><a href="{url}" target="_blank">{url}</a></h2>
    <p class="timestamp">抽出日時: {timestamp}</p>
    <p class="error-message">エラー: {error_message}</p>
</div>
"""
        elif format_type == 'md':
            formatted_text += f"### [{url}]({url})\n\n"
            formatted_text += f"抽出日時: {timestamp}\n\n"
            formatted_text += f"**エラー**: {error_message}\n\n"
        else:  # txt
            formatted_text += f"URL: {url}\n"
            formatted_text += f"抽出日時: {timestamp}\n"
            formatted_text += f"エラー: {error_message}\n\n"
    
    return formatted_text


class UltimateWebTextExtractorApp:
    """最終的なGUIアプリケーション（すべての機能を統合）"""
    
    def __init__(self, root):
        self.root = root
        self.root.title("究極版 Web テキスト抽出ツール")
        self.root.geometry("1100x800")
        self.root.minsize(900, 700)
        
        # ウィンドウのアイコンを設定
        try:
            if platform.system() == "Windows":
                self.root.iconbitmap(default="icon.ico")
            else:
                # macOS/Linuxの場合
                icon_img = Image.open("icon.png")
                icon = ImageTk.PhotoImage(icon_img)
                self.root.iconphoto(True, icon)
        except:
            # アイコンがない場合は無視
            pass
        
        # アプリケーション状態
        self.is_processing = False
        self.worker_thread = None
        self.current_url_index = -1
        self.results = []
        self.start_time = None
        self.loaded_project = None
        self.saved_settings = {}
        
        # ダークモード設定
        self.dark_mode = tk.BooleanVar(value=False)
        self.dark_mode.trace_add('write', self.apply_theme)
        
        # ロゴとバージョン情報
        self.version = "3.1.0"
        
        # スタイル設定
        self.create_styles()
        
        # メニューバーの作成
        self.create_menu()
        
        # 抽出ツールのインスタンス作成
        self.extractor = WebContentExtractor()
        
        # すべてのフレームを保存（テーマ切り替え用）
        self.all_frames = []
        
        # UIコンポーネントを作成
        self.create_widgets()
        
        # 設定の読み込み
        self.load_settings()
        
        # スプラッシュスクリーン
        self.show_splash_screen()
        
        # 起動時のチェック
        self.check_dependencies()
    
    def create_styles(self):
        """スタイル設定を作成"""
        # デフォルトスタイル（ライトモード）
        self.style = ttk.Style()
        self.style.configure("TFrame", background="#f5f5f5")
        self.style.configure("TNotebook", background="#f5f5f5")
        self.style.configure("TNotebook.Tab", background="#e0e0e0", padding=[10, 4], font=('Helvetica', 11))
        self.style.map("TNotebook.Tab", 
                        background=[("selected", "#f0f0f0"), ("active", "#f9f9f9")],
                        foreground=[("selected", "#000000"), ("active", "#333333")])
        
        self.style.configure("TButton", padding=6, relief="flat", font=('Helvetica', 10))
        self.style.configure("Primary.TButton", background="#4CAF50", foreground="white")
        self.style.configure("Secondary.TButton", background="#9E9E9E", foreground="white")
        self.style.configure("Accent.TButton", background="#2196F3", foreground="white")
        self.style.configure("Danger.TButton", background="#F44336", foreground="white")
        
        self.style.configure("TLabel", font=('Helvetica', 11))
        self.style.configure("Header.TLabel", font=('Helvetica', 16, 'bold'))
        self.style.configure("Subheader.TLabel", font=('Helvetica', 14, 'bold'))
        self.style.configure("URL.TLabel", font=('Helvetica', 10))
        self.style.configure("Status.TLabel", font=('Helvetica', 10))
        self.style.configure("Success.TLabel", foreground="green")
        self.style.configure("Error.TLabel", foreground="red")
        self.style.configure("Info.TLabel", foreground="blue")
        self.style.configure("Warning.TLabel", foreground="#FF9800")
        
        self.style.configure("TCheckbutton", font=('Helvetica', 11))
        self.style.configure("TRadiobutton", font=('Helvetica', 11))
        self.style.configure("TEntry", font=('Helvetica', 11))
        self.style.configure("TCombobox", font=('Helvetica', 11))
        
        # プログレスバースタイル
        self.style.configure("TProgressbar", thickness=10)
        
        # 区切り線スタイル
        self.style.configure("TSeparator", background="#cccccc")
        
        # スクロールバースタイル
        self.style.configure("Vertical.TScrollbar", gripcount=0, background="#d9d9d9", troughcolor="#f0f0f0", 
                             arrowcolor="#606060", relief="flat")
        self.style.configure("Horizontal.TScrollbar", gripcount=0, background="#d9d9d9", 
                             troughcolor="#f0f0f0", arrowcolor="#606060", relief="flat")
        
        # リストボックススタイル
        self.style.configure("TListbox", background="white", foreground="black", borderwidth=1, relief="solid")
    
    def apply_theme(self, *args):
        """テーマを適用（ライト/ダークモード切替）"""
        if self.dark_mode.get():
            # ダークモード
            self.root.configure(bg="#2d2d2d")
            self.style.configure("TFrame", background="#2d2d2d")
            self.style.configure("TNotebook", background="#2d2d2d")
            self.style.configure("TNotebook.Tab", background="#444444", foreground="#ffffff")
            self.style.map("TNotebook.Tab", 
                          background=[("selected", "#3c3c3c"), ("active", "#505050")],
                          foreground=[("selected", "#ffffff"), ("active", "#eeeeee")])
            
            # ボタンスタイル
            self.style.configure("TButton", background="#505050", foreground="#ffffff")
            self.style.configure("Primary.TButton", background="#388E3C", foreground="white")
            self.style.configure("Secondary.TButton", background="#616161", foreground="white")
            self.style.configure("Accent.TButton", background="#1976D2", foreground="white")
            self.style.configure("Danger.TButton", background="#D32F2F", foreground="white")
            
            # ラベルスタイル
            self.style.configure("TLabel", foreground="#ffffff", background="#2d2d2d")
            self.style.configure("Header.TLabel", foreground="#ffffff", background="#2d2d2d")
            self.style.configure("Subheader.TLabel", foreground="#ffffff", background="#2d2d2d")
            self.style.configure("URL.TLabel", foreground="#4FC3F7", background="#2d2d2d")
            
            # テキストカラー
            for txt in [self.url_text, self.output_text, self.log_text]:
                txt.configure(bg="#3c3c3c", fg="#e0e0e0", insertbackground="#ffffff")
            
            # 他のウィジェットの色
            for frame in self.all_frames:
                frame.configure(background="#2d2d2d")
        else:
            # ライトモード
            self.root.configure(bg="#f5f5f5")
            self.style.configure("TFrame", background="#f5f5f5")
            self.style.configure("TNotebook", background="#f5f5f5")
            self.style.configure("TNotebook.Tab", background="#e0e0e0", foreground="#000000")
            self.style.map("TNotebook.Tab", 
                          background=[("selected", "#f0f0f0"), ("active", "#f9f9f9")],
                          foreground=[("selected", "#000000"), ("active", "#333333")])
            
            # ボタンスタイル
            self.style.configure("TButton", background="#e0e0e0", foreground="#000000")
            self.style.configure("Primary.TButton", background="#4CAF50", foreground="white")
            self.style.configure("Secondary.TButton", background="#9E9E9E", foreground="white")
            self.style.configure("Accent.TButton", background="#2196F3", foreground="white")
            self.style.configure("Danger.TButton", background="#F44336", foreground="white")
            
            # ラベルスタイル
            self.style.configure("TLabel", foreground="#000000", background="#f5f5f5")
            self.style.configure("Header.TLabel", foreground="#000000", background="#f5f5f5")
            self.style.configure("Subheader.TLabel", foreground="#000000", background="#f5f5f5")
            self.style.configure("URL.TLabel", foreground="#0288D1", background="#f5f5f5")
            
            # テキストカラー
            for txt in [self.url_text, self.output_text, self.log_text]:
                txt.configure(bg="white", fg="black", insertbackground="black")
            
            # 他のウィジェットの色
            for frame in self.all_frames:
                frame.configure(background="#f5f5f5")
    
    def create_menu(self):
        """メニューバーを作成"""
        self.menubar = Menu(self.root)
        self.root.config(menu=self.menubar)
        
        # ファイルメニュー
        self.file_menu = Menu(self.menubar, tearoff=0)
        self.file_menu.add_command(label="新規プロジェクト", command=self.new_project)
        self.file_menu.add_command(label="プロジェクトを開く", command=self.open_project)
        self.file_menu.add_command(label="プロジェクトを保存", command=self.save_project)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="URLリストをインポート", command=self.import_urls)
        self.file_menu.add_command(label="結果をエクスポート", command=self.export_results)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="終了", command=self.root.quit)
        self.menubar.add_cascade(label="ファイル", menu=self.file_menu)
        
        # 編集メニュー
        self.edit_menu = Menu(self.menubar, tearoff=0)
        self.edit_menu.add_command(label="URLをすべてクリア", command=self.clear_urls)
        self.edit_menu.add_command(label="結果をクリア", command=self.clear_results)
        self.edit_menu.add_separator()
        self.edit_menu.add_command(label="設定", command=self.show_settings)
        self.menubar.add_cascade(label="編集", menu=self.edit_menu)
        
        # 実行メニュー
        self.run_menu = Menu(self.menubar, tearoff=0)
        self.run_menu.add_command(label="実行", command=self.start_extraction)
        self.run_menu.add_command(label="停止", command=self.stop_extraction, state="disabled")
        self.run_menu.add_separator()
        self.run_menu.add_command(label="選択したURLだけ実行", command=self.run_selected)
        self.menubar.add_cascade(label="実行", menu=self.run_menu)
        
        # 表示メニュー
        self.view_menu = Menu(self.menubar, tearoff=0)
        self.view_menu.add_checkbutton(label="ダークモード", variable=self.dark_mode)
        self.view_menu.add_separator()
        self.view_menu.add_command(label="ログを表示", command=self.show_log)
        self.view_menu.add_command(label="結果の詳細表示", command=self.show_result_details)
        self.menubar.add_cascade(label="表示", menu=self.view_menu)
        
        # ヘルプメニュー
        self.help_menu = Menu(self.menubar, tearoff=0)
        self.help_menu.add_command(label="ヘルプ", command=self.show_help)
        self.help_menu.add_command(label="バージョン情報", command=self.show_about)
        self.menubar.add_cascade(label="ヘルプ", menu=self.help_menu)
    
    def create_widgets(self):
        """UIコンポーネントを作成"""
        # メインフレーム
        self.main_frame = ttk.Frame(self.root, padding=10)
        self.main_frame.pack(fill=tk.BOTH, expand=True)
        self.all_frames.append(self.main_frame)
        
        # ヘッダーフレーム
        self.header_frame = ttk.Frame(self.main_frame)
        self.header_frame.pack(fill=tk.X, pady=(0, 10))
        self.all_frames.append(self.header_frame)
        
        # アプリケーションタイトル
        self.title_label = ttk.Label(self.header_frame, text=f"究極版 Web テキスト抽出ツール v{self.version}", 
                                    style="Header.TLabel")
        self.title_label.pack(side=tk.LEFT, padx=5)
        
        # 操作ボタンフレーム
        self.action_frame = ttk.Frame(self.header_frame)
        self.action_frame.pack(side=tk.RIGHT)
        self.all_frames.append(self.action_frame)
        
        # 実行ボタン
        self.run_button = ttk.Button(self.action_frame, text="実行", command=self.start_extraction, 
                                    style="Primary.TButton")
        self.run_button.pack(side=tk.LEFT, padx=5)
        
        # 停止ボタン
        self.stop_button = ttk.Button(self.action_frame, text="停止", command=self.stop_extraction, 
                                     style="Danger.TButton", state="disabled")
        self.stop_button.pack(side=tk.LEFT, padx=5)
        
        # インポートボタン
        self.import_button = ttk.Button(self.action_frame, text="URLインポート", 
                                      command=self.import_urls, style="Secondary.TButton")
        self.import_button.pack(side=tk.LEFT, padx=5)
        
        # エクスポートボタン
        self.export_button = ttk.Button(self.action_frame, text="結果エクスポート", 
                                      command=self.export_results, style="Secondary.TButton")
        self.export_button.pack(side=tk.LEFT, padx=5)
        
        # 設定ボタン
        self.settings_button = ttk.Button(self.action_frame, text="設定", 
                                        command=self.show_settings, style="Secondary.TButton")
        self.settings_button.pack(side=tk.LEFT, padx=5)
        
        # ペイン分割
        self.paned_window = ttk.PanedWindow(self.main_frame, orient=tk.VERTICAL)
        self.paned_window.pack(fill=tk.BOTH, expand=True)
        
        # URL入力エリア
        self.url_frame = ttk.LabelFrame(self.paned_window, text="URL入力 (1行に1URLを入力)", padding=10)
        self.paned_window.add(self.url_frame, weight=1)
        self.all_frames.append(self.url_frame)
        
        # URLテキストエリア
        self.url_text_frame = ttk.Frame(self.url_frame)
        self.url_text_frame.pack(fill=tk.BOTH, expand=True)
        self.all_frames.append(self.url_text_frame)
        
        self.url_text = scrolledtext.ScrolledText(self.url_text_frame, wrap=tk.WORD, 
                                                height=10, font=('Courier New', 11))
        self.url_text.pack(fill=tk.BOTH, expand=True)
        
        # URL操作ボタンフレーム
        self.url_button_frame = ttk.Frame(self.url_frame)
        self.url_button_frame.pack(fill=tk.X, pady=(5, 0))
        self.all_frames.append(self.url_button_frame)
        
        # URLクリアボタン
        self.clear_url_button = ttk.Button(self.url_button_frame, text="URLをクリア", 
                                         command=self.clear_urls, style="Secondary.TButton")
        self.clear_url_button.pack(side=tk.LEFT, padx=5)
        
        # URL検証ボタン
        self.validate_url_button = ttk.Button(self.url_button_frame, text="URL検証", 
                                            command=self.validate_urls, style="Accent.TButton")
        self.validate_url_button.pack(side=tk.LEFT, padx=5)
        
        # URL件数ラベル
        self.url_count_label = ttk.Label(self.url_button_frame, text="URL: 0件", style="Status.TLabel")
        self.url_count_label.pack(side=tk.RIGHT, padx=5)
        
        # 出力テキストエリア
        self.output_frame = ttk.LabelFrame(self.paned_window, text="抽出結果", padding=10)
        self.paned_window.add(self.output_frame, weight=2)
        self.all_frames.append(self.output_frame)
        
        # タブ付きの出力エリア
        self.output_notebook = ttk.Notebook(self.output_frame)
        self.output_notebook.pack(fill=tk.BOTH, expand=True)
        
        # 結果タブ
        self.result_tab = ttk.Frame(self.output_notebook)
        self.output_notebook.add(self.result_tab, text="抽出テキスト")
        self.all_frames.append(self.result_tab)
        
        self.output_text = scrolledtext.ScrolledText(self.result_tab, wrap=tk.WORD, 
                                                  height=20, font=('Courier New', 11))
        self.output_text.pack(fill=tk.BOTH, expand=True)
        
        # ログタブ
        self.log_tab = ttk.Frame(self.output_notebook)
        self.output_notebook.add(self.log_tab, text="実行ログ")
        self.all_frames.append(self.log_tab)
        
        self.log_text = scrolledtext.ScrolledText(self.log_tab, wrap=tk.WORD, 
                                               height=20, font=('Courier New', 11))
        self.log_text.pack(fill=tk.BOTH, expand=True)
        
        # 処理中のステータス表示
        self.status_frame = ttk.Frame(self.main_frame)
        self.status_frame.pack(fill=tk.X, pady=(10, 0))
        self.all_frames.append(self.status_frame)
        
        # 進捗バー
        self.progress_bar = ttk.Progressbar(self.status_frame, mode='determinate', length=100)
        self.progress_bar.pack(fill=tk.X, side=tk.TOP)
        
        # ステータスラベル
        self.status_label = ttk.Label(self.status_frame, text="準備完了", style="Status.TLabel")
        self.status_label.pack(side=tk.LEFT, padx=5, pady=5)
        
        # 処理時間ラベル
        self.time_label = ttk.Label(self.status_frame, text="", style="Status.TLabel")
        self.time_label.pack(side=tk.RIGHT, padx=5, pady=5)
        
        # URLカウンターの更新
        self.update_url_count()
    
    def new_project(self):
        """新規プロジェクト"""
        if messagebox.askyesno("確認", "現在の作業内容はすべて消去されます。続行しますか？"):
            self.clear_urls()
            self.clear_results()
            self.loaded_project = None
            self.root.title("究極版 Web テキスト抽出ツール")
            self.log("新規プロジェクトを作成しました")
    
    def open_project(self):
        """プロジェクトを開く"""
        file_path = filedialog.askopenfilename(
            title="プロジェクトを開く",
            filetypes=[("Web抽出プロジェクト", "*.wextr"), ("すべてのファイル", "*.*")]
        )
        
        if not file_path:
            return
            
        try:
            with open(file_path, 'rb') as f:
                project_data = pickle.load(f)
                
            # プロジェクトデータの読み込み
            self.clear_urls()
            self.clear_results()
            
            # URLの復元
            if 'urls' in project_data:
                urls = project_data['urls']
                self.url_text.insert('1.0', '\n'.join(urls))
            
            # 結果の復元
            if 'results' in project_data:
                self.results = project_data['results']
                self.display_results()
            
            # 設定の復元
            if 'settings' in project_data:
                self.saved_settings = project_data['settings']
                # 設定を適用
                if isinstance(self.saved_settings, dict):
                    for k, v in self.saved_settings.items():
                        if hasattr(self.extractor.options, k):
                            self.extractor.options[k] = v
            
            self.loaded_project = file_path
            self.root.title(f"究極版 Web テキスト抽出ツール - {os.path.basename(file_path)}")
            self.log(f"プロジェクトを読み込みました: {file_path}")
            self.update_url_count()
            
        except Exception as e:
            messagebox.showerror("エラー", f"プロジェクトの読み込み中にエラーが発生しました:\n{str(e)}")
            self.log(f"プロジェクト読み込みエラー: {str(e)}")
    
    def save_project(self):
        """プロジェクトを保存"""
        file_path = self.loaded_project
        
        if not file_path:
            file_path = filedialog.asksaveasfilename(
                title="プロジェクトを保存",
                defaultextension=".wextr",
                filetypes=[("Web抽出プロジェクト", "*.wextr"), ("すべてのファイル", "*.*")]
            )
            
        if not file_path:
            return
            
        try:
            # 現在のURLを取得
            urls = self.url_text.get('1.0', tk.END).strip().split('\n')
            urls = [url.strip() for url in urls if url.strip()]
            
            # プロジェクトデータの構築
            project_data = {
                'urls': urls,
                'results': self.results,
                'settings': self.extractor.options,
                'version': self.version,
                'saved_date': datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            }
            
            with open(file_path, 'wb') as f:
                pickle.dump(project_data, f)
                
            self.loaded_project = file_path
            self.root.title(f"究極版 Web テキスト抽出ツール - {os.path.basename(file_path)}")
            self.log(f"プロジェクトを保存しました: {file_path}")
            messagebox.showinfo("保存完了", "プロジェクトが保存されました")
            
        except Exception as e:
            messagebox.showerror("エラー", f"プロジェクトの保存中にエラーが発生しました:\n{str(e)}")
            self.log(f"プロジェクト保存エラー: {str(e)}")
    
    def import_urls(self):
        """URLをファイルからインポート"""
        file_path = filedialog.askopenfilename(
            title="URLリストをインポート",
            filetypes=[("テキストファイル", "*.txt"), ("CSVファイル", "*.csv"), ("すべてのファイル", "*.*")]
        )
        
        if not file_path:
            return
            
        try:
            urls = []
            
            # ファイル拡張子でフォーマットを判定
            ext = os.path.splitext(file_path)[1].lower()
            
            if ext == '.csv':
                # CSVファイルとして処理
                with open(file_path, 'r', encoding='utf-8') as f:
                    csv_reader = csv.reader(f)
                    for row in csv_reader:
                        if row and row[0].strip():
                            # 先頭列をURLとして使用
                            url = row[0].strip()
                            if URL.is_valid(url):
                                urls.append(url)
            else:
                # テキストファイルとして処理
                with open(file_path, 'r', encoding='utf-8') as f:
                    for line in f:
                        url = line.strip()
                        if url and not url.startswith('#'):
                            if URL.is_valid(url):
                                urls.append(url)
            
            if not urls:
                messagebox.showwarning("警告", "有効なURLが見つかりませんでした")
                return
                
            # 既存のURLに追加するか置き換えるかを確認
            if self.url_text.get('1.0', tk.END).strip():
                add_mode = messagebox.askyesno("確認", "既存のURLに追加しますか？\n「いいえ」を選択すると既存のURLが置き換えられます。")
                
                if add_mode:
                    # 末尾に追加
                    current_text = self.url_text.get('1.0', tk.END).strip()
                    self.url_text.delete('1.0', tk.END)
                    self.url_text.insert('1.0', current_text + '\n' + '\n'.join(urls))
                else:
                    # 置き換え
                    self.url_text.delete('1.0', tk.END)
                    self.url_text.insert('1.0', '\n'.join(urls))
            else:
                # 空のテキストボックスに追加
                self.url_text.insert('1.0', '\n'.join(urls))
            
            self.update_url_count()
            self.log(f"{len(urls)}件のURLをインポートしました: {file_path}")
            
        except Exception as e:
            messagebox.showerror("エラー", f"URLのインポート中にエラーが発生しました:\n{str(e)}")
            self.log(f"URLインポートエラー: {str(e)}")
    
    def export_results(self):
        """結果をエクスポート"""
        if not self.results:
            messagebox.showwarning("警告", "エクスポートする結果がありません")
            return
            
        # エクスポート設定ダイアログ
        export_dialog = tk.Toplevel(self.root)
        export_dialog.title("結果のエクスポート")
        export_dialog.geometry("500x350")
        export_dialog.transient(self.root)
        export_dialog.grab_set()
        
        # エクスポート設定フレーム
        settings_frame = ttk.Frame(export_dialog, padding=20)
        settings_frame.pack(fill=tk.BOTH, expand=True)
        
        # 保存形式
        ttk.Label(settings_frame, text="保存形式:").grid(row=0, column=0, sticky=tk.W, pady=5)
        
        format_var = tk.StringVar(value="txt")
        ttk.Radiobutton(settings_frame, text="テキスト形式 (.txt)", variable=format_var, value="txt").grid(
            row=0, column=1, sticky=tk.W, pady=5)
        ttk.Radiobutton(settings_frame, text="Markdown形式 (.md)", variable=format_var, value="md").grid(
            row=1, column=1, sticky=tk.W, pady=5)
        ttk.Radiobutton(settings_frame, text="HTML形式 (.html)", variable=format_var, value="html").grid(
            row=2, column=1, sticky=tk.W, pady=5)
        ttk.Radiobutton(settings_frame, text="JSON形式 (.json)", variable=format_var, value="json").grid(
            row=3, column=1, sticky=tk.W, pady=5)
        
        # オプション
        ttk.Label(settings_frame, text="オプション:").grid(row=4, column=0, sticky=tk.W, pady=10)
        
        headers_var = tk.BooleanVar(value=True)
        errors_var = tk.BooleanVar(value=False)
        sections_var = tk.BooleanVar(value=True)
        
        ttk.Checkbutton(settings_frame, text="ヘッダー情報を含める (URL, タイトルなど)", 
                       variable=headers_var).grid(row=5, column=1, sticky=tk.W)
        ttk.Checkbutton(settings_frame, text="エラー結果も含める", 
                       variable=errors_var).grid(row=6, column=1, sticky=tk.W)
        ttk.Checkbutton(settings_frame, text="カテゴリごとにセクション分けする", 
                       variable=sections_var).grid(row=7, column=1, sticky=tk.W)
        
        # ボタンフレーム
        button_frame = ttk.Frame(settings_frame)
        button_frame.grid(row=8, column=0, columnspan=2, pady=20)
        
        def do_export():
            format_type = format_var.get()
            include_headers = headers_var.get()
            include_errors = errors_var.get()
            separate_sections = sections_var.get()
            
            # 保存先を選択
            extensions = {
                "txt": ".txt",
                "md": ".md",
                "html": ".html",
                "json": ".json"
            }
            
            file_types = {
                "txt": [("テキストファイル", "*.txt")],
                "md": [("Markdownファイル", "*.md")],
                "html": [("HTMLファイル", "*.html")],
                "json": [("JSONファイル", "*.json")]
            }
            
            file_path = filedialog.asksaveasfilename(
                title="結果を保存",
                defaultextension=extensions[format_type],
                filetypes=file_types[format_type]
            )
            
            if not file_path:
                return
                
            try:
                if format_type == "json":
                    # JSON形式
                    json_data = []
                    for result in self.results:
                        if result['success'] or include_errors:
                            json_data.append(result)
                    
                    with open(file_path, 'w', encoding='utf-8') as f:
                        json.dump(json_data, f, ensure_ascii=False, indent=2)
                else:
                    # テキスト/Markdown/HTML形式
                    content = self.extractor.combine_results_to_single_file(
                        self.results, 
                        format_type=format_type, 
                        include_headers=include_headers, 
                        include_errors=include_errors, 
                        separate_sections=separate_sections
                    )
                    
                    with open(file_path, 'w', encoding='utf-8') as f:
                        f.write(content)
                
                self.log(f"結果をエクスポートしました: {file_path}")
                messagebox.showinfo("エクスポート完了", f"結果を保存しました:\n{file_path}")
                export_dialog.destroy()
                
            except Exception as e:
                messagebox.showerror("エラー", f"結果のエクスポート中にエラーが発生しました:\n{str(e)}")
                self.log(f"結果エクスポートエラー: {str(e)}")
        
        ttk.Button(button_frame, text="エクスポート", command=do_export, style="Primary.TButton").pack(
            side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="キャンセル", command=export_dialog.destroy).pack(
            side=tk.LEFT, padx=5)
    
    def clear_urls(self):
        """URLテキストをクリア"""
        if self.url_text.get('1.0', tk.END).strip():
            if messagebox.askyesno("確認", "URLリストをクリアしますか？"):
                self.url_text.delete('1.0', tk.END)
                self.update_url_count()
                self.log("URLリストをクリアしました")
    
    def clear_results(self):
        """結果をクリア"""
        if self.results:
            if messagebox.askyesno("確認", "すべての結果をクリアしますか？"):
                self.results = []
                self.output_text.delete('1.0', tk.END)
                self.log("結果をクリアしました")
    
    def validate_urls(self):
        """URLの検証"""
        urls = self.url_text.get('1.0', tk.END).strip().split('\n')
        urls = [url.strip() for url in urls if url.strip()]
        
        if not urls:
            messagebox.showinfo("URL検証", "URLが入力されていません")
            return
            
        valid_urls = []
        invalid_urls = []
        
        for url in urls:
            normalized_url = URL.normalize(url)
            if normalized_url and URL.is_valid(normalized_url):
                valid_urls.append(normalized_url)
            else:
                invalid_urls.append(url)
        
        # 結果を表示
        result_dialog = tk.Toplevel(self.root)
        result_dialog.title("URL検証結果")
        result_dialog.geometry("600x400")
        result_dialog.transient(self.root)
        
        result_frame = ttk.Frame(result_dialog, padding=20)
        result_frame.pack(fill=tk.BOTH, expand=True)
        
        ttk.Label(result_frame, text=f"検証結果: {len(valid_urls)}件 有効 / {len(invalid_urls)}件 無効", 
                 style="Subheader.TLabel").pack(pady=(0, 10), anchor=tk.W)
        
        # 無効URLがあれば表示
        if invalid_urls:
            ttk.Label(result_frame, text="無効なURL:", style="Error.TLabel").pack(anchor=tk.W)
            
            invalid_text = scrolledtext.ScrolledText(result_frame, height=10, width=70)
            invalid_text.pack(fill=tk.BOTH, expand=True, pady=5)
            
            for url in invalid_urls:
                invalid_text.insert(tk.END, f"{url}\n")
            
            def remove_invalid():
                # 無効なURLを削除したリストを作成
                self.url_text.delete('1.0', tk.END)
                self.url_text.insert('1.0', '\n'.join(valid_urls))
                self.update_url_count()
                self.log(f"{len(invalid_urls)}件の無効なURLを削除しました")
                result_dialog.destroy()
            
            ttk.Button(result_frame, text="無効なURLを削除", command=remove_invalid, 
                      style="Danger.TButton").pack(pady=10)
        else:
            ttk.Label(result_frame, text="すべてのURLは有効です", 
                     style="Success.TLabel").pack(pady=10)
        
        # 重複チェック
        seen_urls = set()
        duplicate_urls = []
        
        for url in valid_urls:
            if url in seen_urls:
                duplicate_urls.append(url)
            else:
                seen_urls.add(url)
        
        if duplicate_urls:
            ttk.Label(result_frame, text=f"重複URL: {len(duplicate_urls)}件", 
                     style="Warning.TLabel").pack(anchor=tk.W, pady=(10, 0))
            
            def remove_duplicates():
                # 重複を除去したリストを作成
                unique_urls = []
                seen = set()
                
                for url in valid_urls:
                    if url not in seen:
                        unique_urls.append(url)
                        seen.add(url)
                
                self.url_text.delete('1.0', tk.END)
                self.url_text.insert('1.0', '\n'.join(unique_urls))
                self.update_url_count()
                self.log(f"{len(duplicate_urls)}件の重複URLを削除しました")
                result_dialog.destroy()
            
            ttk.Button(result_frame, text="重複URLを削除", command=remove_duplicates, 
                      style="Secondary.TButton").pack(pady=10)
        
        ttk.Button(result_frame, text="閉じる", command=result_dialog.destroy).pack(pady=10)
    
    def update_url_count(self):
        """URL件数の更新"""
        urls = self.url_text.get('1.0', tk.END).strip().split('\n')
        urls = [url for url in urls if url.strip()]
        count = len(urls)
        self.url_count_label.config(text=f"URL: {count}件")
    
    def show_settings(self):
        """設定ダイアログを表示"""
        settings_dialog = tk.Toplevel(self.root)
        settings_dialog.title("抽出設定")
        settings_dialog.geometry("600x700")
        settings_dialog.transient(self.root)
        settings_dialog.grab_set()
        
        # 設定フレーム
        settings_frame = ttk.Frame(settings_dialog, padding=20)
        settings_frame.pack(fill=tk.BOTH, expand=True)
        
        # 設定タブ
        settings_notebook = ttk.Notebook(settings_frame)
        settings_notebook.pack(fill=tk.BOTH, expand=True)
        
        # 基本設定タブ
        basic_tab = ttk.Frame(settings_notebook, padding=10)
        settings_notebook.add(basic_tab, text="基本設定")
        
        # 抽出設定タブ
        extract_tab = ttk.Frame(settings_notebook, padding=10)
        settings_notebook.add(extract_tab, text="抽出設定")
        
        # 接続設定タブ
        connection_tab = ttk.Frame(settings_notebook, padding=10)
        settings_notebook.add(connection_tab, text="接続設定")
        
        # フィルター設定タブ
        filter_tab = ttk.Frame(settings_notebook, padding=10)
        settings_notebook.add(filter_tab, text="フィルター設定")
        
        # 設定値の変数
        settings_vars = {}
        
        # 設定項目の生成（基本設定）
        row = 0
        ttk.Label(basic_tab, text="基本設定", style="Subheader.TLabel").grid(row=row, column=0, sticky=tk.W, pady=(0, 10))
        row += 1
        
        # 抽出モード
        ttk.Label(basic_tab, text="抽出モード:").grid(row=row, column=0, sticky=tk.W, pady=5)
        extraction_mode = tk.StringVar(value=self.extractor.options.get('extraction_mode', 'auto'))
        settings_vars['extraction_mode'] = extraction_mode
        
        modes = [("自動", "auto"), ("本文優先", "content"), ("全ページ", "fullpage"), ("Readability", "readability")]
        frame = ttk.Frame(basic_tab)
        frame.grid(row=row, column=1, sticky=tk.W, pady=5)
        
        for i, (text, value) in enumerate(modes):
            ttk.Radiobutton(frame, text=text, variable=extraction_mode, value=value).grid(
                row=0, column=i, padx=5)
        
        row += 1
        
        # キャッシュ有効
        cache_enabled = tk.BooleanVar(value=self.extractor.options.get('cache_enabled', True))
        settings_vars['cache_enabled'] = cache_enabled
        ttk.Checkbutton(basic_tab, text="キャッシュを有効にする", variable=cache_enabled).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        # PDFテキスト抽出
        extract_pdf = tk.BooleanVar(value=self.extractor.options.get('extract_pdf_text', True))
        settings_vars['extract_pdf_text'] = extract_pdf
        ttk.Checkbutton(basic_tab, text="PDFからテキストを抽出する", variable=extract_pdf).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        # 多言語サポート
        multilingual = tk.BooleanVar(value=self.extractor.options.get('multilingual_support', True))
        settings_vars['multilingual_support'] = multilingual
        ttk.Checkbutton(basic_tab, text="多言語サポートを有効にする", variable=multilingual).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        # エラー時に続行
        continue_on_error = tk.BooleanVar(value=self.extractor.options.get('continue_on_error', True))
        settings_vars['continue_on_error'] = continue_on_error
        ttk.Checkbutton(basic_tab, text="エラー発生時も処理を続行する", variable=continue_on_error).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        # 抽出設定
        row = 0
        ttk.Label(extract_tab, text="抽出設定", style="Subheader.TLabel").grid(
            row=row, column=0, sticky=tk.W, pady=(0, 10))
        row += 1
        
        # 広告・ナビ削除オプション
        remove_ads = tk.BooleanVar(value=self.extractor.options.get('remove_ads', True))
        settings_vars['remove_ads'] = remove_ads
        ttk.Checkbutton(extract_tab, text="広告・プロモーションを削除", variable=remove_ads).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        remove_navigation = tk.BooleanVar(value=self.extractor.options.get('remove_navigation', True))
        settings_vars['remove_navigation'] = remove_navigation
        ttk.Checkbutton(extract_tab, text="ナビゲーション・メニューを削除", variable=remove_navigation).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        remove_footer = tk.BooleanVar(value=self.extractor.options.get('remove_footer', True))
        settings_vars['remove_footer'] = remove_footer
        ttk.Checkbutton(extract_tab, text="フッター・コピーライトを削除", variable=remove_footer).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        remove_related = tk.BooleanVar(value=self.extractor.options.get('remove_related', True))
        settings_vars['remove_related'] = remove_related
        ttk.Checkbutton(extract_tab, text="関連記事・おすすめを削除", variable=remove_related).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        # テキスト整形オプション
        ttk.Separator(extract_tab, orient=tk.HORIZONTAL).grid(
            row=row, column=0, columnspan=2, sticky=tk.EW, pady=10)
        row += 1
        
        remove_empty_lines = tk.BooleanVar(value=self.extractor.options.get('remove_empty_lines', True))
        settings_vars['remove_empty_lines'] = remove_empty_lines
        ttk.Checkbutton(extract_tab, text="空行の最適化", variable=remove_empty_lines).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        normalize_spaces = tk.BooleanVar(value=self.extractor.options.get('normalize_spaces', True))
        settings_vars['normalize_spaces'] = normalize_spaces
        ttk.Checkbutton(extract_tab, text="スペースの正規化", variable=normalize_spaces).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        # メタデータ・リンク抽出
        ttk.Separator(extract_tab, orient=tk.HORIZONTAL).grid(
            row=row, column=0, columnspan=2, sticky=tk.EW, pady=10)
        row += 1
        
        extract_metadata = tk.BooleanVar(value=self.extractor.options.get('extract_metadata', True))
        settings_vars['extract_metadata'] = extract_metadata
        ttk.Checkbutton(extract_tab, text="メタデータを抽出する", variable=extract_metadata).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        extract_images = tk.BooleanVar(value=self.extractor.options.get('extract_images', False))
        settings_vars['extract_images'] = extract_images
        ttk.Checkbutton(extract_tab, text="画像情報を抽出する", variable=extract_images).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        extract_links = tk.BooleanVar(value=self.extractor.options.get('extract_links', False))
        settings_vars['extract_links'] = extract_links
        ttk.Checkbutton(extract_tab, text="リンク情報を抽出する", variable=extract_links).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        # 接続設定
        row = 0
        ttk.Label(connection_tab, text="接続設定", style="Subheader.TLabel").grid(
            row=row, column=0, sticky=tk.W, pady=(0, 10))
        row += 1
        
        # タイムアウト設定
        ttk.Label(connection_tab, text="タイムアウト (秒):").grid(row=row, column=0, sticky=tk.W, pady=5)
        timeout = tk.IntVar(value=self.extractor.options.get('timeout', 30))
        settings_vars['timeout'] = timeout
        ttk.Spinbox(connection_tab, from_=5, to=120, textvariable=timeout, width=10).grid(
            row=row, column=1, sticky=tk.W, pady=5)
        row += 1
        
        # 同時接続数
        ttk.Label(connection_tab, text="同時接続数:").grid(row=row, column=0, sticky=tk.W, pady=5)
        max_connections = tk.IntVar(value=self.extractor.options.get('max_connections', 10))
        settings_vars['max_connections'] = max_connections
        ttk.Spinbox(connection_tab, from_=1, to=50, textvariable=max_connections, width=10).grid(
            row=row, column=1, sticky=tk.W, pady=5)
        row += 1
        
        # ユーザーエージェントローテーション
        user_agent_rotation = tk.BooleanVar(value=self.extractor.options.get('user_agent_rotation', True))
        settings_vars['user_agent_rotation'] = user_agent_rotation
        ttk.Checkbutton(connection_tab, text="ユーザーエージェントをランダム化", 
                       variable=user_agent_rotation).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        # フィルター設定
        row = 0
        ttk.Label(filter_tab, text="フィルター設定", style="Subheader.TLabel").grid(
            row=row, column=0, sticky=tk.W, pady=(0, 10))
        row += 1
        
        # 重複URL除外
        exclude_duplicates = tk.BooleanVar(value=self.extractor.options.get('exclude_duplicates', True))
        settings_vars['exclude_duplicates'] = exclude_duplicates
        ttk.Checkbutton(filter_tab, text="重複するURLを除外", variable=exclude_duplicates).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        # Eコマースサイト除外
        exclude_ecommerce = tk.BooleanVar(value=self.extractor.options.get('exclude_ecommerce', False))
        settings_vars['exclude_ecommerce'] = exclude_ecommerce
        ttk.Checkbutton(filter_tab, text="Eコマースサイトを除外", variable=exclude_ecommerce).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        # アダルトサイト除外
        exclude_adult = tk.BooleanVar(value=self.extractor.options.get('exclude_adult', False))
        settings_vars['exclude_adult'] = exclude_adult
        ttk.Checkbutton(filter_tab, text="アダルトサイトを除外", variable=exclude_adult).grid(
            row=row, column=0, columnspan=2, sticky=tk.W, pady=5)
        row += 1
        
        # ボタンフレーム
        button_frame = ttk.Frame(settings_dialog)
        button_frame.pack(fill=tk.X, padx=20, pady=20)
        
        def save_settings():
            # 設定を保存
            for key, var in settings_vars.items():
                self.extractor.options[key] = var.get()
            
            self.log("設定を更新しました")
            settings_dialog.destroy()
        
        def reset_defaults():
            # デフォルトに戻す
            if messagebox.askyesno("確認", "すべての設定をデフォルトに戻しますか？"):
                # デフォルト設定
                default_options = {
                    'remove_ads': True,
                    'remove_navigation': True, 
                    'remove_footer': True,
                    'remove_related': True,
                    'remove_empty_lines': True,
                    'normalize_spaces': True,
                    'multilingual_support': True,
                    'extraction_mode': 'auto',
                    'continue_on_error': True,
                    'exclude_ecommerce': False,
                    'exclude_adult': False,
                    'exclude_duplicates': True,
                    'extract_metadata': True,
                    'extract_images': False,
                    'extract_links': False,
                    'max_connections': 10,
                    'timeout': 30,
                    'cache_enabled': True,
                    'user_agent_rotation': True,
                    'extract_pdf_text': True
                }
                
                # 変数を更新
                for key, var in settings_vars.items():
                    if key in default_options:
                        if isinstance(var, tk.BooleanVar):
                            var.set(default_options[key])
                        elif isinstance(var, tk.IntVar):
                            var.set(default_options[key])
                        elif isinstance(var, tk.StringVar):
                            var.set(default_options[key])
        
        ttk.Button(button_frame, text="保存", command=save_settings, style="Primary.TButton").pack(
            side=tk.RIGHT, padx=5)
        ttk.Button(button_frame, text="キャンセル", command=settings_dialog.destroy).pack(
            side=tk.RIGHT, padx=5)
        ttk.Button(button_frame, text="デフォルトに戻す", command=reset_defaults).pack(
            side=tk.LEFT, padx=5)
    
    def start_extraction(self):
        """抽出処理を開始"""
        if self.is_processing:
            return
            
        # URLを取得
        urls = self.url_text.get('1.0', tk.END).strip().split('\n')
        urls = [url.strip() for url in urls if url.strip()]
        
        if not urls:
            messagebox.showwarning("警告", "URLが入力されていません")
            return
            
        # 処理開始前の確認
        if len(urls) > 20:
            if not messagebox.askyesno("確認", f"{len(urls)}件のURLを処理します。続行しますか？"):
                return
        
        # UIを処理中状態に更新
        self.is_processing = True
        self.run_button.config(state="disabled")
        self.stop_button.config(state="normal")
        self.run_menu.entryconfig("実行", state="disabled")
        self.run_menu.entryconfig("停止", state="normal")
        self.run_menu.entryconfig("選択したURLだけ実行", state="disabled")
        
        # 進捗バーの初期化
        self.progress_bar['maximum'] = len(urls)
        self.progress_bar['value'] = 0
        
        # ログの初期化
        self.log_text.delete('1.0', tk.END)
        self.log(f"抽出処理を開始します: {len(urls)}件のURL")
        
        # 結果をクリア
        self.results = []
        self.output_text.delete('1.0', tk.END)
        
        # スレッド用のキュー
        self.result_queue = queue.Queue()
        
        # 開始時刻を記録
        self.start_time = time.time()
        self.update_time_display()
        
        # ワーカースレッドの起動
        self.worker_thread = threading.Thread(
            target=self.extractor.process_url_batch,
            args=(urls,),
            kwargs={
                'max_workers': self.extractor.options.get('max_connections', 10),
                'callback': self.on_url_success,
                'error_callback': self.on_url_error,
                'progress_callback': self.on_progress_update
            }
        )
        self.worker_thread.daemon = True
        self.worker_thread.start()
        
        # キューをポーリングしてUIを更新
        self.root.after(100, self.check_result_queue)
    
    def update_time_display(self):
        """経過時間表示の更新"""
        if self.is_processing and self.start_time:
            elapsed = time.time() - self.start_time
            hours = int(elapsed // 3600)
            minutes = int((elapsed % 3600) // 60)
            seconds = int(elapsed % 60)
            
            if hours > 0:
                time_text = f"経過時間: {hours}時間 {minutes}分 {seconds}秒"
            elif minutes > 0:
                time_text = f"経過時間: {minutes}分 {seconds}秒"
            else:
                time_text = f"経過時間: {seconds}秒"
                
            self.time_label.config(text=time_text)
            
            # 定期的に更新
            self.root.after(1000, self.update_time_display)
        else:
            if self.start_time:
                elapsed = time.time() - self.start_time
                self.time_label.config(text=f"処理時間: {int(elapsed)}秒")
            else:
                self.time_label.config(text="")
    
    def check_result_queue(self):
        """結果キューをチェックして処理"""
        try:
            # キューがある限り処理
            while not self.result_queue.empty():
                item_type, data = self.result_queue.get_nowait()
                
                if item_type == 'success':
                    # 成功結果の処理
                    self.process_success_result(data)
                elif item_type == 'error':
                    # エラー結果の処理
                    self.process_error_result(data)
                elif item_type == 'progress':
                    # 進捗更新の処理
                    url, current, total, status, stats = data
                    self.process_progress_update(url, current, total, status, stats)
                    
                self.result_queue.task_done()
        except queue.Empty:
            pass
        
        # 処理が完了したかチェック
        if self.is_processing and (not self.worker_thread or not self.worker_thread.is_alive()):
            # 処理完了
            self.finalize_extraction()
        else:
            # まだ処理中なら再度キューをチェック
            self.root.after(100, self.check_result_queue)
    
    def on_url_success(self, result):
        """URL処理成功時のコールバック（ワーカースレッドから呼ばれる）"""
        self.result_queue.put(('success', result))
    
    def on_url_error(self, error_result):
        """URL処理エラー時のコールバック（ワーカースレッドから呼ばれる）"""
        self.result_queue.put(('error', error_result))
    
    def on_progress_update(self, url, current, total, status, stats=None):
        """進捗更新時のコールバック（ワーカースレッドから呼ばれる）"""
        self.result_queue.put(('progress', (url, current, total, status, stats)))
    
    def process_success_result(self, result):
        """成功結果の処理（メインスレッド）"""
        # 結果を保存
        self.results.append(result)
        
        # ログに追加
        url = result.get('url', '不明')
        self.log(f"成功: {url}")
        
        # 結果の更新（最大10件まで表示、その後は上書き）
        if len(self.results) <= 10:
            self.display_results()
        
        # タイトルの更新
        self.update_window_title()
    
    def process_error_result(self, error_result):
        """エラー結果の処理（メインスレッド）"""
        # 結果を保存
        self.results.append(error_result)
        
        # ログに追加
        url = error_result.get('url', '不明')
        error = error_result.get('error', '不明なエラー')
        self.log(f"エラー: {url} - {error}", level="error")
        
        # タイトルの更新
        self.update_window_title()
    
    def process_progress_update(self, url, current, total, status, stats=None):
        """進捗更新の処理（メインスレッド）"""
        # 進捗バーの更新
        if current is not None and total is not None:
            self.progress_bar['value'] = current
            percent = int((current / total) * 100) if total > 0 else 0
            self.status_label.config(text=f"処理中... {current}/{total} ({percent}%)")
        
        # 個別URLの状態更新
        if url and status:
            self.log(f"{url} - {status}")
        
        # 統計情報の表示（処理完了時）
        if stats and isinstance(stats, dict):
            stats_text = "処理結果統計:\n"
            for category, count in stats.items():
                if count > 0:
                    stats_text += f"- {category}: {count}件\n"
            self.log(stats_text)
    
    def stop_extraction(self):
        """抽出処理を停止"""
        if not self.is_processing:
            return
            
        if messagebox.askyesno("確認", "処理を中断しますか？"):
            # 停止フラグを設定
            self.is_processing = False
            self.log("処理を中断しています...")
            
            # UIを更新
            self.status_label.config(text="中断中...")
            
            # スレッドを停止（Pythonではスレッドの強制終了は難しいのでフラグで管理）
            if self.worker_thread and self.worker_thread.is_alive():
                # スレッド停止を待機
                self.worker_thread.join(1.0)
            
            # 完了処理
            self.finalize_extraction()
    
    def finalize_extraction(self):
        """抽出処理の完了処理"""
        # 処理完了
        self.is_processing = False
        
        # UI更新
        self.run_button.config(state="normal")
        self.stop_button.config(state="disabled")
        self.run_menu.entryconfig("実行", state="normal")
        self.run_menu.entryconfig("停止", state="disabled")
        self.run_menu.entryconfig("選択したURLだけ実行", state="normal")
        
        # 結果の表示
        self.display_results()
        
        # 成功・エラー数のカウント
        success_count = len([r for r in self.results if r.get('success', False)])
        error_count = len(self.results) - success_count
        
        # 経過時間の最終更新
        elapsed = time.time() - self.start_time if self.start_time else 0
        time_text = f"処理時間: {int(elapsed)}秒"
        self.time_label.config(text=time_text)
        
        # 完了メッセージ
        self.status_label.config(text=f"完了: {success_count}件成功, {error_count}件エラー")
        self.log(f"抽出処理が完了しました: {success_count}件成功, {error_count}件エラー, 処理時間: {int(elapsed)}秒")
        
        # タイトルの更新
        self.update_window_title()
        
        # 結果表示タブをアクティブに
        self.output_notebook.select(0)
        
        # 完了音を鳴らす（オプション）
        try:
            if platform.system() == "Windows":
                import winsound
                winsound.MessageBeep()
        except:
            pass
    
    def display_results(self):
        """結果を表示エリアに表示"""
        self.output_text.delete('1.0', tk.END)
        
        if not self.results:
            self.output_text.insert(tk.END, "結果はまだありません。")
            return
            
        # 結果の概要を表示
        success_count = len([r for r in self.results if r.get('success', False)])
        error_count = len(self.results) - success_count
        
        summary = f"=== 抽出結果 ===\n"
        summary += f"処理URL: {len(self.results)}件 (成功: {success_count}件, エラー: {error_count}件)\n\n"
        
        self.output_text.insert(tk.END, summary)
        
        # 成功した結果のみ表示（最初の30件）
        displayed_count = 0
        for result in self.results:
            if result.get('success', False):
                url = result.get('url', '')
                content = result.get('content', '')
                raw_result = result.get('raw_result', {})
                
                if isinstance(raw_result, dict) and 'title' in raw_result:
                    title = raw_result['title']
                    self.output_text.insert(tk.END, f"URL: {url}\nタイトル: {title}\n\n")
                else:
                    self.output_text.insert(tk.END, f"URL: {url}\n\n")
                
                # 長すぎるコンテンツは省略
                if len(content) > 2000:
                    content = content[:2000] + "...(省略)..."
                
                self.output_text.insert(tk.END, f"{content}\n\n")
                self.output_text.insert(tk.END, f"{'-' * 60}\n\n")
                
                displayed_count += 1
                if displayed_count >= 30:
                    self.output_text.insert(tk.END, "...(以下省略)...\n")
                    break
    
    def update_window_title(self):
        """ウィンドウタイトルの更新"""
        if self.loaded_project:
            project_name = os.path.basename(self.loaded_project)
            result_count = len(self.results) if self.results else 0
            self.root.title(f"究極版 Web テキスト抽出ツール - {project_name} ({result_count}件)")
        elif self.results:
            result_count = len(self.results)
            self.root.title(f"究極版 Web テキスト抽出ツール ({result_count}件)")
        else:
            self.root.title("究極版 Web テキスト抽出ツール")
    
    def run_selected(self):
        """選択したURLのみ実行"""
        # テキストボックスから選択範囲を取得
        try:
            sel_start = self.url_text.index(tk.SEL_FIRST)
            sel_end = self.url_text.index(tk.SEL_LAST)
            selected_text = self.url_text.get(sel_start, sel_end)
        except tk.TclError:
            messagebox.showinfo("選択エラー", "実行するURLを選択してください。")
            return
        
        if not selected_text.strip():
            messagebox.showinfo("選択エラー", "実行するURLを選択してください。")
            return
        
        # 選択テキストからURLを抽出
        urls = selected_text.strip().split('\n')
        urls = [url.strip() for url in urls if url.strip()]
        
        if not urls:
            messagebox.showinfo("選択エラー", "有効なURLが選択されていません。")
            return
        
        # 確認ダイアログ
        if not messagebox.askyesno("確認", f"選択した{len(urls)}件のURLを処理します。続行しますか？"):
            return
        
        # 実行
        self.is_processing = True
        self.run_button.config(state="disabled")
        self.stop_button.config(state="normal")
        self.run_menu.entryconfig("実行", state="disabled")
        self.run_menu.entryconfig("停止", state="normal")
        self.run_menu.entryconfig("選択したURLだけ実行", state="disabled")
        
        # 進捗バーの初期化
        self.progress_bar['maximum'] = len(urls)
        self.progress_bar['value'] = 0
        
        # ログの初期化
        self.log_text.delete('1.0', tk.END)
        self.log(f"選択した{len(urls)}件のURLの処理を開始します")
        
        # 結果をクリア
        self.results = []
        self.output_text.delete('1.0', tk.END)
        
        # スレッド用のキュー
        self.result_queue = queue.Queue()
        
        # 開始時刻を記録
        self.start_time = time.time()
        self.update_time_display()
        
        # ワーカースレッドの起動
        self.worker_thread = threading.Thread(
            target=self.extractor.process_url_batch,
            args=(urls,),
            kwargs={
                'max_workers': self.extractor.options.get('max_connections', 10),
                'callback': self.on_url_success,
                'error_callback': self.on_url_error,
                'progress_callback': self.on_progress_update
            }
        )
        self.worker_thread.daemon = True
        self.worker_thread.start()
        
        # キューをポーリングしてUIを更新
        self.root.after(100, self.check_result_queue)
    
    def show_log(self):
        """ログを表示"""
        self.output_notebook.select(1)  # ログタブを選択
    
    def show_result_details(self):
        """結果の詳細表示"""
        if not self.results:
            messagebox.showinfo("情報", "表示する結果がありません")
            return
        
        # 詳細表示ウィンドウ
        detail_window = tk.Toplevel(self.root)
        detail_window.title("抽出結果の詳細")
        detail_window.geometry("900x700")
        
        # 詳細フレーム
        detail_frame = ttk.Frame(detail_window, padding=20)
        detail_frame.pack(fill=tk.BOTH, expand=True)
        
        # 結果リスト（左側）
        list_frame = ttk.Frame(detail_frame, width=300)
        list_frame.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        
        ttk.Label(list_frame, text="URL一覧:").pack(anchor=tk.W, pady=(0, 5))
        
        # リストボックス
        result_list = tk.Listbox(list_frame, width=40, height=30)
        result_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # スクロールバー
        list_scrollbar = ttk.Scrollbar(list_frame, orient=tk.VERTICAL, command=result_list.yview)
        list_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        result_list.config(yscrollcommand=list_scrollbar.set)
        
        # 詳細表示（右側）
        content_frame = ttk.Frame(detail_frame)
        content_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        
        # 詳細表示タブ
        content_notebook = ttk.Notebook(content_frame)
        content_notebook.pack(fill=tk.BOTH, expand=True)
        
        # テキストタブ
        text_tab = ttk.Frame(content_notebook)
        content_notebook.add(text_tab, text="テキスト")
        
        text_content = scrolledtext.ScrolledText(text_tab, wrap=tk.WORD, font=('Courier New', 11))
        text_content.pack(fill=tk.BOTH, expand=True)
        
        # メタデータタブ
        meta_tab = ttk.Frame(content_notebook)
        content_notebook.add(meta_tab, text="メタデータ")
        
        meta_content = scrolledtext.ScrolledText(meta_tab, wrap=tk.WORD, font=('Courier New', 11))
        meta_content.pack(fill=tk.BOTH, expand=True)
        
        # 結果リストにデータを追加
        for i, result in enumerate(self.results):
            url = result.get('url', '不明')
            success = result.get('success', False)
            
            # 成功/失敗でプレフィックスを変更
            prefix = "[OK] " if success else "[NG] "
            result_list.insert(tk.END, f"{prefix}{url}")
            
            # 成功/失敗で背景色を変更
            if success:
                result_list.itemconfig(i, {'bg': '#e6ffe6'})
            else:
                result_list.itemconfig(i, {'bg': '#ffe6e6'})
        
        # リスト選択時の処理
        def on_select(event):
            # 選択されたインデックスを取得
            selection = result_list.curselection()
            if not selection:
                return
                
            index = selection[0]
            result = self.results[index]
            
            # テキストタブを更新
            text_content.delete('1.0', tk.END)
            
            if result.get('success', False):
                # 成功結果の表示
                url = result.get('url', '')
                content = result.get('content', '')
                raw_result = result.get('raw_result', {})
                
                if isinstance(raw_result, dict) and 'title' in raw_result:
                    title = raw_result['title']
                    text_content.insert(tk.END, f"URL: {url}\nタイトル: {title}\n\n")
                else:
                    text_content.insert(tk.END, f"URL: {url}\n\n")
                
                text_content.insert(tk.END, content)
            else:
                # エラー結果の表示
                url = result.get('url', '')
                error = result.get('error', '不明なエラー')
                error_type = result.get('error_type', '')
                
                text_content.insert(tk.END, f"URL: {url}\n\n")
                text_content.insert(tk.END, f"エラータイプ: {error_type}\n")
                text_content.insert(tk.END, f"エラーメッセージ: {error}\n")
            
            # メタデータタブを更新
            meta_content.delete('1.0', tk.END)
            
            if result.get('success', False):
                raw_result = result.get('raw_result', {})
                
                if isinstance(raw_result, dict):
                    if 'metadata' in raw_result:
                        meta_content.insert(tk.END, "===== メタデータ =====\n\n")
                        for key, value in raw_result['metadata'].items():
                            meta_content.insert(tk.END, f"{key}: {value}\n")
                    
                    if 'images' in raw_result:
                        meta_content.insert(tk.END, "\n===== 画像情報 =====\n\n")
                        for img in raw_result['images']:
                            meta_content.insert(tk.END, f"URL: {img.get('url', '')}\n")
                            meta_content.insert(tk.END, f"代替テキスト: {img.get('alt', '')}\n")
                            meta_content.insert(tk.END, f"タイトル: {img.get('title', '')}\n\n")
                    
                    if 'links' in raw_result:
                        meta_content.insert(tk.END, "\n===== リンク情報 =====\n\n")
                        for link in raw_result['links']:
                            meta_content.insert(tk.END, f"URL: {link.get('url', '')}\n")
                            meta_content.insert(tk.END, f"テキスト: {link.get('text', '')}\n")
                            meta_content.insert(tk.END, f"タイトル: {link.get('title', '')}\n\n")
            else:
                # エラー結果のメタ情報
                timestamp = result.get('timestamp', '')
                category = result.get('category', '')
                
                meta_content.insert(tk.END, f"タイムスタンプ: {timestamp}\n")
                meta_content.insert(tk.END, f"カテゴリ: {category}\n")
        
        # リスト選択イベントをバインド
        result_list.bind('<<ListboxSelect>>', on_select)
        
        # 最初の項目を選択
        if self.results:
            result_list.selection_set(0)
            result_list.event_generate('<<ListboxSelect>>')
    
    def show_help(self):
        """ヘルプを表示"""
        help_window = tk.Toplevel(self.root)
        help_window.title("ヘルプ")
        help_window.geometry("800x600")
        help_window.transient(self.root)
        
        help_frame = ttk.Frame(help_window, padding=20)
        help_frame.pack(fill=tk.BOTH, expand=True)
        
        help_text = scrolledtext.ScrolledText(help_frame, wrap=tk.WORD, font=('Helvetica', 11))
        help_text.pack(fill=tk.BOTH, expand=True)
        
        help_content = """
# Web テキスト抽出ツール ヘルプ

## 基本的な使い方

1. URLテキストボックスに抽出したいWebページのURLを入力します。1行に1URLを入力してください。
2. 「実行」ボタンをクリックして抽出処理を開始します。
3. 抽出結果は下部のテキストエリアに表示されます。

## 主要機能

### URL入力と管理
- **URLインポート**: テキストファイルやCSVからURLのリストをインポートできます。
- **URL検証**: 入力されたURLの有効性をチェックします。
- **選択したURLだけ実行**: 選択したURLのみを処理します。

### 抽出設定
- **抽出モード**: 自動、本文優先、全ページ、Readabilityから選択できます。
- **テキスト整形オプション**: 広告・ナビゲーション削除、空行最適化などを設定できます。
- **メタデータ抽出**: タイトル、説明文、著者などのメタデータを抽出できます。

### 結果管理
- **結果エクスポート**: 抽出結果をテキスト、Markdown、HTML、JSON形式で保存できます。
- **詳細表示**: 個別の抽出結果の詳細情報を確認できます。
- **プロジェクト保存**: 作業状態をプロジェクトファイルとして保存できます。

## トラブルシューティング

- **抽出に失敗する場合**: 接続設定のタイムアウト値を増やしてみてください。
- **特定のサイトで抽出精度が低い**: 抽出モードを変更すると改善する場合があります。
- **処理が遅い**: 同時接続数を調整してください。高すぎると逆に遅くなることがあります。

## ショートカット

- Ctrl+O: プロジェクトを開く
- Ctrl+S: プロジェクトを保存
- Ctrl+R: 実行
- Ctrl+E: 停止
- F1: ヘルプを表示

## お問い合わせ

バグ報告や機能リクエストは、公式サイトのフォームからお願いします。
        """
        
        help_text.insert('1.0', help_content)
        help_text.config(state='disabled')  # 読み取り専用
    
    def show_about(self):
        """バージョン情報を表示"""
        about_window = tk.Toplevel(self.root)
        about_window.title("バージョン情報")
        about_window.geometry("500x350")
        about_window.transient(self.root)
        
        about_frame = ttk.Frame(about_window, padding=20)
        about_frame.pack(fill=tk.BOTH, expand=True)
        
        # ロゴ
        try:
            logo_img = Image.open("icon.png").resize((100, 100))
            logo = ImageTk.PhotoImage(logo_img)
            logo_label = ttk.Label(about_frame, image=logo)
            logo_label.image = logo  # 参照を保持
            logo_label.pack(pady=10)
        except:
            pass
        
        # アプリ情報
        ttk.Label(about_frame, text=f"究極版 Web テキスト抽出ツール", 
                 font=('Helvetica', 16, 'bold')).pack(pady=5)
        ttk.Label(about_frame, text=f"バージョン {self.version}").pack()
        ttk.Label(about_frame, text=f"Copyright © 2023-2024").pack(pady=5)
        
        # システム情報
        sys_info = f"Python: {platform.python_version()}\n"
        sys_info += f"OS: {platform.system()} {platform.version()}\n"
        sys_info += f"Tkinter: {tk.TkVersion}\n"
        sys_info += f"BeautifulSoup: {BeautifulSoup.__version__}\n"
        
        if PDF_SUPPORT:
            sys_info += f"PyPDF2: インストール済み\n"
        else:
            sys_info += f"PyPDF2: 未インストール\n"
        
        system_frame = ttk.LabelFrame(about_frame, text="システム情報")
        system_frame.pack(fill=tk.X, pady=10)
        
        ttk.Label(system_frame, text=sys_info, justify=tk.LEFT).pack(padx=10, pady=10)
        
        # 閉じるボタン
        ttk.Button(about_frame, text="閉じる", command=about_window.destroy).pack(pady=10)
    
    def log(self, message, level="info"):
        """ログにメッセージを追加"""
        timestamp = datetime.datetime.now().strftime("%H:%M:%S")
        
        # ログレベルに応じたプレフィックス
        if level == "error":
            prefix = "エラー"
        elif level == "warning":
            prefix = "警告"
        else:
            prefix = "情報"
        
        log_message = f"[{timestamp}] [{prefix}] {message}\n"
        
        # UIスレッドセーフな挿入
        self.log_text.insert(tk.END, log_message)
        
        # ログレベルに応じたタグ付け
        if level == "error":
            self.log_text.tag_add("error", f"end - {len(log_message) + 1}c", "end - 1c")
            self.log_text.tag_config("error", foreground="red")
        elif level == "warning":
            self.log_text.tag_add("warning", f"end - {len(log_message) + 1}c", "end - 1c")
            self.log_text.tag_config("warning", foreground="#FF9800")
        
        # 自動スクロール
        self.log_text.see(tk.END)
        
        # ファイルにも記録
        try:
            logger.info(message) if level == "info" else logger.error(message)
        except:
            pass
    
    def load_settings(self):
        """設定を読み込み"""
        settings_file = os.path.join(os.path.expanduser("~"), ".web_extractor_settings.json")
        try:
            if os.path.exists(settings_file):
                with open(settings_file, 'r', encoding='utf-8') as f:
                    settings = json.load(f)
                    
                    # ダークモード設定
                    if 'dark_mode' in settings:
                        self.dark_mode.set(settings['dark_mode'])
                    
                    # 抽出設定
                    if 'extractor_options' in settings:
                        extractor_options = settings['extractor_options']
                        for key, value in extractor_options.items():
                            self.extractor.options[key] = value
                    
                    # ウィンドウサイズ
                    if 'window_size' in settings:
                        size = settings['window_size']
                        if len(size) == 2:
                            self.root.geometry(f"{size[0]}x{size[1]}")
                    
                self.log("設定を読み込みました")
        except Exception as e:
            self.log(f"設定の読み込み中にエラーが発生しました: {e}", level="warning")
    
    def save_settings(self):
        """設定を保存"""
        settings_file = os.path.join(os.path.expanduser("~"), ".web_extractor_settings.json")
        try:
            # 現在の設定を収集
            settings = {
                'dark_mode': self.dark_mode.get(),
                'extractor_options': self.extractor.options,
                'window_size': [self.root.winfo_width(), self.root.winfo_height()]
            }
            
            with open(settings_file, 'w', encoding='utf-8') as f:
                json.dump(settings, f, ensure_ascii=False, indent=2)
                
            self.log("設定を保存しました")
        except Exception as e:
            self.log(f"設定の保存中にエラーが発生しました: {e}", level="warning")
    
    def show_splash_screen(self):
        """スプラッシュスクリーンを表示"""
        splash = tk.Toplevel(self.root)
        splash.overrideredirect(True)
        
        # スプラッシュウィンドウを中央に配置
        window_width = 500
        window_height = 300
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        x = (screen_width - window_width) // 2
        y = (screen_height - window_height) // 2
        splash.geometry(f"{window_width}x{window_height}+{x}+{y}")
        
        # スプラッシュの背景色
        if self.dark_mode.get():
            splash.configure(bg="#2d2d2d")
            fg_color = "#ffffff"
        else:
            splash.configure(bg="#f5f5f5")
            fg_color = "#000000"
        
        # スプラッシュ内容
        splash_frame = ttk.Frame(splash)
        splash_frame.pack(fill=tk.BOTH, expand=True)
        
        # ロゴ
        try:
            logo_img = Image.open("icon.png").resize((100, 100))
            logo = ImageTk.PhotoImage(logo_img)
            logo_label = ttk.Label(splash_frame, image=logo)
            logo_label.image = logo  # 参照を保持
            logo_label.pack(pady=(40, 10))
        except:
            pass
        
        # アプリ名とバージョン
        ttk.Label(splash_frame, text=f"究極版 Web テキスト抽出ツール", 
                 font=('Helvetica', 20, 'bold')).pack()
        ttk.Label(splash_frame, text=f"Version {self.version}").pack(pady=5)
        
        # ロード中メッセージ
        loading_label = ttk.Label(splash_frame, text="ロード中...")
        loading_label.pack(pady=20)
        
        # プログレスバー
        progress = ttk.Progressbar(splash_frame, mode='indeterminate', length=300)
        progress.pack(padx=20)
        progress.start(15)
        
        # スプラッシュを表示し、少し待ってから閉じる
        self.root.update()
        
        # 初期化処理
        self.root.after(1000, lambda: self.dismiss_splash(splash))
    
    def dismiss_splash(self, splash):
        """スプラッシュスクリーンを閉じる"""
        splash.destroy()
    
    def check_dependencies(self):
        """依存パッケージのチェック"""
        # 必要なライブラリの存在をチェック
        missing_packages = []
        
        required_packages = {
            'beautifulsoup4': 'BeautifulSoup',
            'requests': 'requests',
            'Pillow': 'PIL',
            'PyPDF2': 'PyPDF2',
            'lxml': 'lxml',
            'chardet': 'chardet'
        }
        
        for package, module in required_packages.items():
            try:
                __import__(module.split('.')[0])
            except ImportError:
                missing_packages.append(package)
        
        # 不足パッケージがあれば警告
        if missing_packages:
            message = f"以下のパッケージがインストールされていません:\n\n"
            message += "\n".join(missing_packages)
            message += "\n\n一部の機能が制限される可能性があります。インストールしますか？"
            
            if messagebox.askyesno("警告", message):
                self.install_dependencies(missing_packages)
    
    def install_dependencies(self, packages):
        """不足している依存パッケージをインストール"""
        def run_installation():
            self.log("必要なパッケージをインストールしています...")
            self.status_label.config(text="パッケージインストール中...")
            
            try:
                # pip を使ってインストール
                import pip
                for package in packages:
                    self.log(f"{package}をインストール中...")
                    pip.main(['install', package])
                
                self.log("パッケージのインストールが完了しました。再起動してください。")
                messagebox.showinfo("インストール完了", 
                                  "必要なパッケージがインストールされました。\n"
                                  "変更を適用するには、アプリケーションを再起動してください。")
                self.status_label.config(text="準備完了")
            except Exception as e:
                self.log(f"パッケージのインストール中にエラーが発生しました: {e}", level="error")
                messagebox.showerror("エラー", 
                                    f"パッケージのインストール中にエラーが発生しました:\n{str(e)}\n\n"
                                    "手動でインストールしてください。")
                self.status_label.config(text="準備完了")
        
        # インストールを別スレッドで実行
        thread = threading.Thread(target=run_installation)
        thread.daemon = True
        thread.start()
    
    def on_closing(self):
        """アプリケーション終了時の処理"""
        # 未保存の変更がある場合は確認
        if self.results and not self.loaded_project:
            if messagebox.askyesno("確認", "保存されていない結果があります。終了しますか？"):
                # 設定を保存
                self.save_settings()
                # キャッシュを保存
                self.extractor.save_cache()
                self.root.destroy()
        else:
            # 設定を保存
            self.save_settings()
            # キャッシュを保存
            self.extractor.save_cache()
            self.root.destroy()


def main():
    """アプリケーションのメインエントリーポイント"""
    root = tk.Tk()
    app = UltimateWebTextExtractorApp(root)
    
    # 終了時の処理をバインド
    root.protocol("WM_DELETE_WINDOW", app.on_closing)
    
    # スタイル設定
    app.apply_theme()
    
    root.mainloop()


if __name__ == "__main__":
    # パッケージのインストールを確認
    if install_required_packages():
        main()
    else:
        print("必要なパッケージをインストールできませんでした。")