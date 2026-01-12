/**
 * CWE Mapper - Map CWE IDs to Japanese explanations
 *
 * Implements: TSK-CODEQL-002, REQ-CODEQL-003, DES-CODEQL-002
 */

/**
 * CWE Information
 */
export interface CWEInfo {
  id: string;
  name: string;
  nameJa: string;
  description: string;
  explanation: string;
  severity: 'critical' | 'high' | 'medium' | 'low';
  category: string;
  references?: string[];
}

/**
 * CWE Database - Common Web Application Vulnerabilities (Top 25 + Additional)
 * @see https://cwe.mitre.org/top25/archive/2023/2023_top25_list.html
 */
const CWE_DATABASE: Record<string, CWEInfo> = {
  'CWE-79': {
    id: 'CWE-79',
    name: 'Cross-site Scripting (XSS)',
    nameJa: 'クロスサイトスクリプティング (XSS)',
    description: 'Improper Neutralization of Input During Web Page Generation',
    explanation:
      'ユーザー入力がHTMLページに適切にエスケープされずに出力されることで、攻撃者が悪意のあるスクリプトを注入できる脆弱性です。Cookieの窃取、セッションハイジャック、フィッシングなどの攻撃に悪用されます。対策として、出力時のHTMLエスケープ、Content Security Policy (CSP) の設定、HTTPOnlyフラグの使用を推奨します。',
    severity: 'high',
    category: 'injection',
    references: ['https://owasp.org/www-community/attacks/xss/'],
  },
  'CWE-89': {
    id: 'CWE-89',
    name: 'SQL Injection',
    nameJa: 'SQLインジェクション',
    description: 'Improper Neutralization of Special Elements used in an SQL Command',
    explanation:
      'ユーザー入力がSQLクエリに直接組み込まれることで、攻撃者がデータベースを不正に操作できる脆弱性です。データの窃取、改ざん、削除、認証バイパスなどの攻撃に悪用されます。対策として、プリペアドステートメント（パラメータ化クエリ）の使用、ORMの活用、入力検証を推奨します。',
    severity: 'critical',
    category: 'injection',
    references: ['https://owasp.org/www-community/attacks/SQL_Injection'],
  },
  'CWE-78': {
    id: 'CWE-78',
    name: 'OS Command Injection',
    nameJa: 'OSコマンドインジェクション',
    description: 'Improper Neutralization of Special Elements used in an OS Command',
    explanation:
      'ユーザー入力がOSコマンドに直接組み込まれることで、攻撃者がサーバー上で任意のコマンドを実行できる脆弱性です。システムの完全な乗っ取りにつながる可能性があります。対策として、シェルコマンドの使用回避、入力の厳格な検証、コマンド実行APIの適切な使用を推奨します。',
    severity: 'critical',
    category: 'injection',
    references: ['https://owasp.org/www-community/attacks/Command_Injection'],
  },
  'CWE-22': {
    id: 'CWE-22',
    name: 'Path Traversal',
    nameJa: 'パストラバーサル',
    description: "Improper Limitation of a Pathname to a Restricted Directory ('Path Traversal')",
    explanation:
      'ファイルパスの構成にユーザー入力を使用する際、../などの特殊文字列により意図しないディレクトリにアクセスできる脆弱性です。機密ファイルの読み取りや上書きに悪用されます。対策として、パスの正規化、ホワイトリスト検証、chroot環境の使用を推奨します。',
    severity: 'high',
    category: 'file',
    references: ['https://owasp.org/www-community/attacks/Path_Traversal'],
  },
  'CWE-352': {
    id: 'CWE-352',
    name: 'Cross-Site Request Forgery (CSRF)',
    nameJa: 'クロスサイトリクエストフォージェリ (CSRF)',
    description: 'Cross-Site Request Forgery (CSRF)',
    explanation:
      '認証済みユーザーが意図しないリクエストを強制的に実行させられる脆弱性です。ログイン状態を悪用して、パスワード変更や送金などの操作を行わせることができます。対策として、CSRFトークンの使用、SameSite Cookie属性の設定、リファラーチェックを推奨します。',
    severity: 'medium',
    category: 'auth',
    references: ['https://owasp.org/www-community/attacks/csrf'],
  },
  'CWE-287': {
    id: 'CWE-287',
    name: 'Improper Authentication',
    nameJa: '不適切な認証',
    description: 'Improper Authentication',
    explanation:
      '認証メカニズムが適切に実装されていないことで、攻撃者が認証をバイパスできる脆弱性です。セッション固定、認証情報の推測、認証ロジックの欠陥などが含まれます。対策として、標準的な認証フレームワークの使用、多要素認証の導入、セッション管理の強化を推奨します。',
    severity: 'critical',
    category: 'auth',
    references: ['https://cwe.mitre.org/data/definitions/287.html'],
  },
  'CWE-306': {
    id: 'CWE-306',
    name: 'Missing Authentication for Critical Function',
    nameJa: '重要な機能に対する認証の欠如',
    description: 'Missing Authentication for Critical Function',
    explanation:
      '重要な機能やリソースへのアクセスに認証が要求されていない脆弱性です。管理機能や機密データへの不正アクセスにつながります。対策として、すべての重要エンドポイントでの認証要求、デフォルト拒否ポリシーの適用を推奨します。',
    severity: 'high',
    category: 'auth',
    references: ['https://cwe.mitre.org/data/definitions/306.html'],
  },
  'CWE-862': {
    id: 'CWE-862',
    name: 'Missing Authorization',
    nameJa: '認可の欠如',
    description: 'Missing Authorization',
    explanation:
      'ユーザーの権限が適切に検証されずにリソースへのアクセスが許可される脆弱性です。水平・垂直権限昇格攻撃に悪用されます。対策として、すべてのアクセスでの権限チェック、最小権限の原則の適用を推奨します。',
    severity: 'high',
    category: 'auth',
    references: ['https://cwe.mitre.org/data/definitions/862.html'],
  },
  'CWE-798': {
    id: 'CWE-798',
    name: 'Use of Hard-coded Credentials',
    nameJa: 'ハードコードされた認証情報の使用',
    description: 'Use of Hard-coded Credentials',
    explanation:
      'ソースコード内にパスワードやAPIキーなどの認証情報が直接記述されている脆弱性です。コード漏洩時に認証情報が露出し、不正アクセスにつながります。対策として、環境変数や秘密管理サービスの使用、定期的な認証情報のローテーションを推奨します。',
    severity: 'critical',
    category: 'secrets',
    references: ['https://cwe.mitre.org/data/definitions/798.html'],
  },
  'CWE-311': {
    id: 'CWE-311',
    name: 'Missing Encryption of Sensitive Data',
    nameJa: '機密データの暗号化の欠如',
    description: 'Missing Encryption of Sensitive Data',
    explanation:
      '機密データが暗号化されずに保存または送信される脆弱性です。データ漏洩時に機密情報が平文で露出します。対策として、保存時の暗号化（AES-256等）、通信時のTLS使用、適切な鍵管理を推奨します。',
    severity: 'high',
    category: 'crypto',
    references: ['https://cwe.mitre.org/data/definitions/311.html'],
  },
  'CWE-327': {
    id: 'CWE-327',
    name: 'Use of a Broken or Risky Cryptographic Algorithm',
    nameJa: '脆弱な暗号アルゴリズムの使用',
    description: 'Use of a Broken or Risky Cryptographic Algorithm',
    explanation:
      'MD5、SHA-1、DES、RC4などの脆弱な暗号アルゴリズムが使用されている脆弱性です。暗号化されたデータが解読される可能性があります。対策として、AES-256、SHA-256以上、RSA 2048ビット以上など、現代的な暗号アルゴリズムの使用を推奨します。',
    severity: 'medium',
    category: 'crypto',
    references: ['https://cwe.mitre.org/data/definitions/327.html'],
  },
  'CWE-502': {
    id: 'CWE-502',
    name: 'Deserialization of Untrusted Data',
    nameJa: '信頼されないデータのデシリアライゼーション',
    description: 'Deserialization of Untrusted Data',
    explanation:
      '信頼されないソースからのシリアライズデータを復元する際に、任意のコードが実行される可能性がある脆弱性です。リモートコード実行につながる重大な脆弱性です。対策として、JSONなど安全なフォーマットの使用、デシリアライズ前の検証、ホワイトリストによる型制限を推奨します。',
    severity: 'critical',
    category: 'injection',
    references: ['https://owasp.org/www-project-web-security-testing-guide/latest/4-Web_Application_Security_Testing/07-Input_Validation_Testing/14-Testing_for_Deserialization_of_Untrusted_Data'],
  },
  'CWE-94': {
    id: 'CWE-94',
    name: 'Improper Control of Generation of Code (Code Injection)',
    nameJa: 'コードインジェクション',
    description: "Improper Control of Generation of Code ('Code Injection')",
    explanation:
      '動的にコードを生成・実行する際にユーザー入力が含まれることで、任意のコードが実行される脆弱性です。eval()、Function()、exec()などの使用時に発生します。対策として、動的コード生成の回避、入力の厳格な検証、サンドボックス環境での実行を推奨します。',
    severity: 'critical',
    category: 'injection',
    references: ['https://cwe.mitre.org/data/definitions/94.html'],
  },
  'CWE-269': {
    id: 'CWE-269',
    name: 'Improper Privilege Management',
    nameJa: '不適切な権限管理',
    description: 'Improper Privilege Management',
    explanation:
      'アプリケーションが必要以上の権限で実行される、または権限の昇格が適切に制御されていない脆弱性です。対策として、最小権限の原則の適用、権限分離、権限昇格時の再認証を推奨します。',
    severity: 'high',
    category: 'auth',
    references: ['https://cwe.mitre.org/data/definitions/269.html'],
  },
  'CWE-434': {
    id: 'CWE-434',
    name: 'Unrestricted Upload of File with Dangerous Type',
    nameJa: '危険なファイルタイプの無制限アップロード',
    description: 'Unrestricted Upload of File with Dangerous Type',
    explanation:
      'ファイルアップロード機能で危険なファイルタイプ（実行可能ファイル等）がアップロード・実行される脆弱性です。Webシェルの設置などに悪用されます。対策として、ファイルタイプのホワイトリスト検証、アップロードディレクトリの実行権限無効化、ファイル名のサニタイズを推奨します。',
    severity: 'high',
    category: 'file',
    references: ['https://owasp.org/www-community/vulnerabilities/Unrestricted_File_Upload'],
  },
  'CWE-918': {
    id: 'CWE-918',
    name: 'Server-Side Request Forgery (SSRF)',
    nameJa: 'サーバーサイドリクエストフォージェリ (SSRF)',
    description: 'Server-Side Request Forgery (SSRF)',
    explanation:
      'サーバーが外部リソースへのリクエストを行う際にURLがユーザー制御可能で、内部ネットワークへのアクセスや認証情報の窃取に悪用される脆弱性です。対策として、URLのホワイトリスト検証、内部ネットワークへのアクセス制限、DNSリバインディング対策を推奨します。',
    severity: 'high',
    category: 'injection',
    references: ['https://owasp.org/www-community/attacks/Server_Side_Request_Forgery'],
  },
  'CWE-200': {
    id: 'CWE-200',
    name: 'Exposure of Sensitive Information to an Unauthorized Actor',
    nameJa: '権限のない者への機密情報の露出',
    description: 'Exposure of Sensitive Information to an Unauthorized Actor',
    explanation:
      'エラーメッセージ、ログ、APIレスポンスなどを通じて機密情報が露出する脆弱性です。スタックトレース、データベース構造、内部IPアドレスなどが漏洩します。対策として、エラーハンドリングの適切な実装、本番環境でのデバッグ情報の無効化を推奨します。',
    severity: 'medium',
    category: 'info-disclosure',
    references: ['https://cwe.mitre.org/data/definitions/200.html'],
  },
  'CWE-119': {
    id: 'CWE-119',
    name: 'Improper Restriction of Operations within the Bounds of a Memory Buffer',
    nameJa: 'バッファオーバーフロー',
    description: 'Improper Restriction of Operations within the Bounds of a Memory Buffer',
    explanation:
      'メモリバッファの境界を超えた読み書きが行われる脆弱性です。クラッシュ、任意コード実行、情報漏洩につながります。C/C++で主に発生します。対策として、安全な文字列操作関数の使用、境界チェック、ASLRとDEPの有効化を推奨します。',
    severity: 'critical',
    category: 'memory',
    references: ['https://cwe.mitre.org/data/definitions/119.html'],
  },
  'CWE-416': {
    id: 'CWE-416',
    name: 'Use After Free',
    nameJa: '解放後使用',
    description: 'Use After Free',
    explanation:
      'メモリが解放された後にそのメモリにアクセスする脆弱性です。クラッシュや任意コード実行につながります。対策として、解放後のポインタのNULL化、スマートポインタの使用、メモリ安全な言語の採用を推奨します。',
    severity: 'critical',
    category: 'memory',
    references: ['https://cwe.mitre.org/data/definitions/416.html'],
  },
  'CWE-476': {
    id: 'CWE-476',
    name: 'NULL Pointer Dereference',
    nameJa: 'NULLポインタ参照',
    description: 'NULL Pointer Dereference',
    explanation:
      'NULLポインタを参照してしまう脆弱性です。アプリケーションのクラッシュを引き起こします。対策として、ポインタ使用前のNULLチェック、Optional型の使用を推奨します。',
    severity: 'medium',
    category: 'memory',
    references: ['https://cwe.mitre.org/data/definitions/476.html'],
  },
  'CWE-190': {
    id: 'CWE-190',
    name: 'Integer Overflow or Wraparound',
    nameJa: '整数オーバーフロー',
    description: 'Integer Overflow or Wraparound',
    explanation:
      '整数演算の結果が型の最大値を超えてオーバーフローする脆弱性です。予期しない動作やバッファオーバーフローにつながります。対策として、演算前の境界チェック、安全な算術ライブラリの使用を推奨します。',
    severity: 'high',
    category: 'memory',
    references: ['https://cwe.mitre.org/data/definitions/190.html'],
  },
  'CWE-77': {
    id: 'CWE-77',
    name: 'Command Injection',
    nameJa: 'コマンドインジェクション',
    description: "Improper Neutralization of Special Elements used in a Command ('Command Injection')",
    explanation:
      'コマンド文字列にユーザー入力が適切にエスケープされずに含まれることで、追加のコマンドが実行される脆弱性です。対策として、シェル呼び出しの回避、パラメータ化された実行、入力のホワイトリスト検証を推奨します。',
    severity: 'critical',
    category: 'injection',
    references: ['https://cwe.mitre.org/data/definitions/77.html'],
  },
  'CWE-601': {
    id: 'CWE-601',
    name: "URL Redirection to Untrusted Site ('Open Redirect')",
    nameJa: 'オープンリダイレクト',
    description: "URL Redirection to Untrusted Site ('Open Redirect')",
    explanation:
      'リダイレクト先URLがユーザー制御可能で、フィッシングサイトへの誘導に悪用される脆弱性です。対策として、リダイレクト先のホワイトリスト検証、相対パスのみの許可を推奨します。',
    severity: 'medium',
    category: 'redirect',
    references: ['https://cwe.mitre.org/data/definitions/601.html'],
  },
  'CWE-732': {
    id: 'CWE-732',
    name: 'Incorrect Permission Assignment for Critical Resource',
    nameJa: '重要なリソースに対する不適切なパーミッション設定',
    description: 'Incorrect Permission Assignment for Critical Resource',
    explanation:
      '機密ファイルやリソースに過剰なアクセス権限が付与されている脆弱性です。対策として、最小権限の原則の適用、適切なファイルパーミッションの設定を推奨します。',
    severity: 'medium',
    category: 'config',
    references: ['https://cwe.mitre.org/data/definitions/732.html'],
  },
  'CWE-20': {
    id: 'CWE-20',
    name: 'Improper Input Validation',
    nameJa: '不適切な入力検証',
    description: 'Improper Input Validation',
    explanation:
      'ユーザー入力が適切に検証されずに使用される脆弱性の総称です。多くのインジェクション脆弱性の根本原因となります。対策として、すべての入力の検証、ホワイトリストアプローチ、型変換時のエラーハンドリングを推奨します。',
    severity: 'high',
    category: 'validation',
    references: ['https://cwe.mitre.org/data/definitions/20.html'],
  },
};

/**
 * Map CWE ID to CWE information
 */
export function mapCWE(cweId: string): CWEInfo | null {
  // Normalize ID format
  const normalizedId = cweId.toUpperCase().startsWith('CWE-')
    ? cweId.toUpperCase()
    : `CWE-${cweId}`;

  return CWE_DATABASE[normalizedId] ?? null;
}

/**
 * Get all CWE entries
 */
export function getAllCWEs(): CWEInfo[] {
  return Object.values(CWE_DATABASE);
}

/**
 * Get CWE entries by category
 */
export function getCWEsByCategory(category: string): CWEInfo[] {
  return Object.values(CWE_DATABASE).filter((cwe) => cwe.category === category);
}

/**
 * Get CWE entries by severity
 */
export function getCWEsBySeverity(severity: CWEInfo['severity']): CWEInfo[] {
  return Object.values(CWE_DATABASE).filter((cwe) => cwe.severity === severity);
}

/**
 * Extract CWE IDs from text
 */
export function extractCWEIds(text: string): string[] {
  const regex = /CWE-\d+/gi;
  const matches = text.match(regex) ?? [];
  return [...new Set(matches.map((m) => m.toUpperCase()))];
}

/**
 * Check if CWE ID is known
 */
export function isCWEKnown(cweId: string): boolean {
  return mapCWE(cweId) !== null;
}

/**
 * Get CWE severity
 */
export function getCWESeverity(cweId: string): CWEInfo['severity'] | null {
  const info = mapCWE(cweId);
  return info?.severity ?? null;
}

/**
 * Get CWE explanation (Japanese)
 */
export function getCWEExplanation(cweId: string): string | null {
  const info = mapCWE(cweId);
  return info?.explanation ?? null;
}

/**
 * CWE categories
 */
export const CWE_CATEGORIES = [
  'injection',
  'auth',
  'crypto',
  'file',
  'secrets',
  'memory',
  'info-disclosure',
  'config',
  'validation',
  'redirect',
] as const;

export type CWECategory = (typeof CWE_CATEGORIES)[number];
