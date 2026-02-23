# MUSUBIX Security Package 実装計画

**パッケージ名**: `@nahisaho/musubix-security`  
**目標バージョン**: v1.8.0  
**作成日**: 2026-01-06

---

## 1. 概要

セキュリティ特化機能を新パッケージとして実装します。Snyk DeepCode AI、Amazon CodeGuruの「LLM生成→記号検証」アプローチを採用し、MUSUBIXのNeuro-Symbolic統合の強みを活かします。

### 1.1 参考事例

| ツール | アプローチ | 特徴 |
|--------|----------|------|
| **Snyk DeepCode AI** | LLM修正 + 記号ルール再検証 | ハルシネーション防止 |
| **Semgrep + AI** | パターンベース + GPT-4トリアージ | 偽陽性削減 |
| **SonarQube + AI** | 静的解析 + LLM修正 | コード品質 |
| **GitHub Advanced Security** | CodeQL + Copilot | GitHub統合 |

### 1.2 MUSUBIXの差別化ポイント

| 機能 | 他ツール | MUSUBIX |
|------|---------|---------|
| **検出** | ルールベース | ルール + YATA知識グラフ + Z3形式検証 |
| **修正生成** | LLMのみ | LLM + パターンライブラリ |
| **検証** | 単純な再スキャン | Z3 SMT検証 + 形式証明 |
| **学習** | なし | Wake-Sleep継続学習 |
| **トレーサビリティ** | なし | 要件→脆弱性→修正の100%追跡 |

---

## 2. アーキテクチャ

### 2.1 パッケージ構成

```
packages/security/
├── src/
│   ├── analyzers/           # 脆弱性分析
│   │   ├── TaintAnalyzer.ts     # テイント分析
│   │   ├── VulnerabilityScanner.ts # 脆弱性スキャン
│   │   ├── DependencyAuditor.ts # 依存関係監査
│   │   └── SecretsDetector.ts   # シークレット検出
│   ├── rules/               # セキュリティルール
│   │   ├── RuleEngine.ts        # ルールエンジン
│   │   ├── OWASPRules.ts        # OWASP Top 10
│   │   ├── CWERules.ts          # CWE Top 25
│   │   └── CustomRules.ts       # カスタムルール
│   ├── fixers/              # 自動修正
│   │   ├── FixGenerator.ts      # 修正生成（LLM）
│   │   ├── FixVerifier.ts       # 修正検証（Z3）
│   │   └── FixApplier.ts        # 修正適用
│   ├── databases/           # 脆弱性データベース
│   │   ├── CVEDatabase.ts       # CVE/NVD連携
│   │   ├── VulnDB.ts            # 脆弱性DB
│   │   └── PatternDB.ts         # セキュリティパターン
│   ├── compliance/          # コンプライアンス
│   │   ├── ComplianceChecker.ts # 準拠チェック
│   │   ├── PolicyEngine.ts      # ポリシーエンジン
│   │   └── Reporter.ts          # レポート生成
│   ├── tools/               # MCPツール
│   │   └── security-tools.ts
│   ├── types.ts             # 型定義
│   └── index.ts             # エントリポイント
├── rules/                   # ルール定義ファイル
│   ├── owasp-top-10.yaml
│   ├── cwe-top-25.yaml
│   └── custom-rules.yaml
├── tests/
│   ├── unit/
│   └── integration/
├── package.json
└── tsconfig.json
```

### 2.2 アーキテクチャ図

```
┌─────────────────────────────────────────────────────────────┐
│                    Security Scanner                          │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│                    Analyzers                                 │
│  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────────────┐    │
│  │ Taint   │ │  Vuln   │ │  Deps   │ │    Secrets      │    │
│  │Analyzer │ │ Scanner │ │ Auditor │ │    Detector     │    │
│  └────┬────┘ └────┬────┘ └────┬────┘ └────────┬────────┘    │
└───────┼───────────┼───────────┼────────────────┼────────────┘
        │           │           │                │
        └───────────┴─────┬─────┴────────────────┘
                          │
┌─────────────────────────▼───────────────────────────────────┐
│                    Rule Engine                               │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────┐   │
│  │ OWASP Rules  │  │  CWE Rules   │  │  Custom Rules    │   │
│  └──────────────┘  └──────────────┘  └──────────────────┘   │
└─────────────────────────┬───────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────────┐
│                Vulnerability Report                          │
│  • 検出された脆弱性一覧                                       │
│  • 重大度スコア (CVSS)                                       │
│  • 影響範囲                                                  │
└─────────────────────────┬───────────────────────────────────┘
                          │
┌─────────────────────────▼───────────────────────────────────┐
│                    Fix Pipeline                              │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐      │
│  │ LLM生成     │ →  │ Z3検証      │ →  │ 適用        │      │
│  │ (VS Code LM)│    │ (Symbolic)  │    │             │      │
│  └─────────────┘    └─────────────┘    └─────────────┘      │
└─────────────────────────────────────────────────────────────┘
```

### 2.3 VS Code Language Model API 統合

MUSUBIXはVS Code拡張機能のLanguage Model APIを活用してLLM機能を提供します。

#### 2.3.1 概要

| 項目 | 説明 |
|------|------|
| **API** | `vscode.lm` (Language Model API) |
| **対応モデル** | Copilot (GPT-4), Claude, Gemini等 |
| **利点** | ユーザーの既存サブスクリプションを活用、認証不要 |

#### 2.3.2 アーキテクチャ

```
┌─────────────────────────────────────────────────────────────┐
│                  VS Code Extension Host                      │
│  ┌─────────────────────────────────────────────────────┐    │
│  │              Language Model API (vscode.lm)          │    │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐             │    │
│  │  │ Copilot │  │  Claude │  │ Gemini  │  ...        │    │
│  │  └────┬────┘  └────┬────┘  └────┬────┘             │    │
│  └───────┼────────────┼────────────┼────────────────────┘    │
│          └────────────┼────────────┘                         │
│                       ▼                                      │
│  ┌─────────────────────────────────────────────────────┐    │
│  │           MUSUBIX Security Extension                 │    │
│  │  • FixGenerator (LLM修正生成)                        │    │
│  │  • SecurityExplainer (脆弱性説明)                    │    │
│  │  • PatternSuggester (セキュアパターン提案)           │    │
│  └─────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────┘
```

#### 2.3.3 LLMクライアント実装

```typescript
// src/llm/VSCodeLMClient.ts
import * as vscode from 'vscode';

export interface LLMClient {
  generateFix(vulnerability: Vulnerability): Promise<FixCandidate[]>;
  explainVulnerability(vulnerability: Vulnerability): Promise<string>;
  suggestSecurePattern(context: CodeContext): Promise<string>;
}

export class VSCodeLMClient implements LLMClient {
  private modelSelector: vscode.LanguageModelChatSelector = {
    vendor: 'copilot',
    family: 'gpt-4'
  };

  async generateFix(vulnerability: Vulnerability): Promise<FixCandidate[]> {
    // 利用可能なモデルを取得
    const [model] = await vscode.lm.selectChatModels(this.modelSelector);
    
    if (!model) {
      throw new Error('No language model available. Please ensure GitHub Copilot is installed.');
    }

    // プロンプト構築
    const messages = [
      vscode.LanguageModelChatMessage.User(this.buildFixPrompt(vulnerability))
    ];

    // LLM呼び出し
    const response = await model.sendRequest(messages, {}, new vscode.CancellationTokenSource().token);

    // レスポンスをストリーミングで取得
    let result = '';
    for await (const chunk of response.text) {
      result += chunk;
    }

    return this.parseFixCandidates(result, vulnerability);
  }

  private buildFixPrompt(vuln: Vulnerability): string {
    return `You are a security expert. Generate a fix for the following vulnerability.

## Vulnerability Details
- Type: ${vuln.type}
- CWE: ${vuln.ruleId}
- Severity: ${vuln.severity}
- File: ${vuln.location.file}:${vuln.location.startLine}

## Vulnerable Code
\`\`\`
${vuln.location.snippet}
\`\`\`

## Requirements
1. Fix MUST address the security vulnerability
2. Fix MUST preserve the original functionality
3. Fix MUST follow secure coding best practices
4. Provide multiple fix candidates if possible

## Output Format
Provide fixes in JSON format:
\`\`\`json
{
  "fixes": [
    {
      "code": "fixed code here",
      "explanation": "why this fix works",
      "confidence": 0.95
    }
  ]
}
\`\`\``;
  }

  async explainVulnerability(vulnerability: Vulnerability): Promise<string> {
    const [model] = await vscode.lm.selectChatModels(this.modelSelector);
    
    if (!model) {
      return this.getFallbackExplanation(vulnerability);
    }

    const messages = [
      vscode.LanguageModelChatMessage.User(
        `Explain this security vulnerability in simple terms for a developer:
        
Type: ${vulnerability.type}
CWE: ${vulnerability.ruleId}
Code: ${vulnerability.location.snippet}

Include:
1. What the vulnerability is
2. How it can be exploited
3. The potential impact
4. How to fix it`
      )
    ];

    const response = await model.sendRequest(messages, {}, new vscode.CancellationTokenSource().token);
    
    let result = '';
    for await (const chunk of response.text) {
      result += chunk;
    }
    
    return result;
  }

  // モデル選択の変更
  setModelSelector(selector: vscode.LanguageModelChatSelector): void {
    this.modelSelector = selector;
  }

  // フォールバック（LLM利用不可時）
  private getFallbackExplanation(vuln: Vulnerability): string {
    const explanations: Record<string, string> = {
      'xss': 'Cross-Site Scripting (XSS) allows attackers to inject malicious scripts.',
      'sqli': 'SQL Injection allows attackers to execute arbitrary SQL commands.',
      'rce': 'Remote Code Execution allows attackers to run arbitrary code on the server.',
      // ...
    };
    return explanations[vuln.type] || 'Security vulnerability detected.';
  }
}
```

#### 2.3.4 モデル選択オプション

```typescript
// ユーザー設定による動的モデル選択
interface SecurityLLMConfig {
  preferredVendor: 'copilot' | 'anthropic' | 'google';
  preferredFamily?: string;
  fallbackToLocal: boolean;
}

async function selectBestModel(config: SecurityLLMConfig): Promise<vscode.LanguageModelChat | null> {
  // 優先モデルを試行
  const preferred = await vscode.lm.selectChatModels({
    vendor: config.preferredVendor,
    family: config.preferredFamily
  });

  if (preferred.length > 0) {
    return preferred[0];
  }

  // 利用可能な任意のモデルにフォールバック
  const available = await vscode.lm.selectChatModels({});
  if (available.length > 0) {
    return available[0];
  }

  return null;
}
```

#### 2.3.5 設定

VS Code設定（`settings.json`）:

```json
{
  "musubix.security.llm": {
    "preferredVendor": "copilot",
    "preferredFamily": "gpt-4",
    "maxTokens": 4096,
    "temperature": 0.2,
    "fallbackToLocal": false
  }
}
```

---

## 3. 主要機能

### 3.1 テイント分析（Taint Analysis）

汚染データ（ユーザー入力等）の伝播を追跡します。

```typescript
// API設計
interface TaintAnalyzer {
  // ソース定義（汚染の起点）
  defineSources(sources: TaintSource[]): void;
  
  // シンク定義（危険な出力先）
  defineSinks(sinks: TaintSink[]): void;
  
  // サニタイザー定義（浄化関数）
  defineSanitizers(sanitizers: Sanitizer[]): void;
  
  // テイント分析実行
  analyze(code: string): TaintResult[];
}

interface TaintSource {
  type: 'parameter' | 'property' | 'call';
  pattern: string;  // e.g., 'req.body.*', 'req.query.*'
  label: string;    // e.g., 'user-input'
}

interface TaintSink {
  type: 'call' | 'property';
  pattern: string;  // e.g., 'eval(*)', 'innerHTML'
  vulnerability: string;  // e.g., 'xss', 'sqli', 'rce'
}

interface TaintResult {
  source: TaintSource;
  sink: TaintSink;
  path: DataFlowPath[];
  vulnerability: VulnerabilityType;
  severity: 'critical' | 'high' | 'medium' | 'low';
}
```

**使用例**:

```typescript
import { TaintAnalyzer } from '@nahisaho/musubix-security';

const analyzer = new TaintAnalyzer();

// ソース定義
analyzer.defineSources([
  { type: 'property', pattern: 'req.body.*', label: 'user-input' },
  { type: 'property', pattern: 'req.query.*', label: 'user-input' },
  { type: 'property', pattern: 'req.params.*', label: 'user-input' },
]);

// シンク定義
analyzer.defineSinks([
  { type: 'call', pattern: 'eval(*)', vulnerability: 'rce' },
  { type: 'call', pattern: '*.query(*)', vulnerability: 'sqli' },
  { type: 'property', pattern: '*.innerHTML', vulnerability: 'xss' },
]);

// サニタイザー定義
analyzer.defineSanitizers([
  { pattern: 'escapeHtml(*)', cleanses: ['xss'] },
  { pattern: 'parameterize(*)', cleanses: ['sqli'] },
]);

// 分析実行
const results = await analyzer.analyze(sourceCode);
```

### 3.2 脆弱性スキャン（Vulnerability Scanner）

OWASP Top 10、CWE Top 25に基づく脆弱性検出。

```typescript
// API設計
interface VulnerabilityScanner {
  // スキャン設定
  configure(options: ScanOptions): void;
  
  // ファイル/ディレクトリスキャン
  scan(path: string): Promise<ScanResult>;
  
  // コードスニペットスキャン
  scanCode(code: string, language: string): Promise<ScanResult>;
  
  // 増分スキャン（変更分のみ）
  scanIncremental(diff: GitDiff): Promise<ScanResult>;
}

interface ScanOptions {
  rules: ('owasp-top-10' | 'cwe-top-25' | 'custom')[];
  severity: ('critical' | 'high' | 'medium' | 'low')[];
  excludePaths?: string[];
  excludeRules?: string[];
}

interface ScanResult {
  vulnerabilities: Vulnerability[];
  statistics: ScanStatistics;
  duration: number;
}

interface Vulnerability {
  id: string;           // e.g., 'VULN-001'
  ruleId: string;       // e.g., 'CWE-79', 'A03:2021'
  type: VulnType;       // e.g., 'xss', 'sqli', 'injection'
  severity: Severity;
  cvss?: number;        // CVSS score
  
  location: {
    file: string;
    startLine: number;
    endLine: number;
    snippet: string;
  };
  
  description: string;
  recommendation: string;
  references: string[];
  
  // トレーサビリティ
  relatedRequirements?: string[];  // REQ-*
  cwe?: string[];
  owasp?: string[];
}
```

**使用例**:

```typescript
import { VulnerabilityScanner } from '@nahisaho/musubix-security';

const scanner = new VulnerabilityScanner();

scanner.configure({
  rules: ['owasp-top-10', 'cwe-top-25'],
  severity: ['critical', 'high', 'medium'],
  excludePaths: ['node_modules', 'dist'],
});

const result = await scanner.scan('./src');

console.log(`Found ${result.vulnerabilities.length} vulnerabilities`);
for (const vuln of result.vulnerabilities) {
  console.log(`[${vuln.severity}] ${vuln.type}: ${vuln.location.file}:${vuln.location.startLine}`);
}
```

### 3.3 自動修正パイプライン（Fix Pipeline）

LLM生成 → Z3検証 → 適用の3段階パイプライン。

```typescript
// API設計
interface FixPipeline {
  // 修正生成（LLM）
  generateFix(vulnerability: Vulnerability): Promise<FixCandidate[]>;
  
  // 修正検証（Z3 + 再スキャン）
  verifyFix(fix: FixCandidate): Promise<VerificationResult>;
  
  // 修正適用
  applyFix(fix: FixCandidate): Promise<ApplyResult>;
  
  // 一括処理
  processAll(vulnerabilities: Vulnerability[]): Promise<FixReport>;
}

interface FixCandidate {
  id: string;
  vulnerability: Vulnerability;
  
  original: string;      // 元のコード
  fixed: string;         // 修正後のコード
  
  explanation: string;   // 修正の説明
  confidence: number;    // 0-1
  
  // 検証情報
  verified?: boolean;
  verificationDetails?: VerificationResult;
}

interface VerificationResult {
  passed: boolean;
  
  checks: {
    // 脆弱性が解消されたか
    vulnerabilityFixed: boolean;
    
    // 新しい脆弱性を導入していないか
    noNewVulnerabilities: boolean;
    
    // 形式検証（Z3）
    formalVerification: {
      passed: boolean;
      details: string;
    };
    
    // 構文的に正しいか
    syntaxValid: boolean;
    
    // 型チェック
    typeCheck: boolean;
  };
  
  // 失敗理由
  failureReasons?: string[];
}
```

**使用例**:

```typescript
import { FixPipeline } from '@nahisaho/musubix-security';

const pipeline = new FixPipeline({
  llmProvider: 'vscode-lm',  // VS Code Language Model API
  z3Adapter: z3,
  patternLibrary: patterns,
});

// 単一脆弱性の修正
const fixes = await pipeline.generateFix(vulnerability);

for (const fix of fixes) {
  const verification = await pipeline.verifyFix(fix);
  
  if (verification.passed) {
    console.log(`✅ Fix verified: ${fix.explanation}`);
    await pipeline.applyFix(fix);
  } else {
    console.log(`❌ Fix rejected: ${verification.failureReasons}`);
  }
}
```

### 3.4 依存関係監査（Dependency Auditor）

npm/yarn依存関係の脆弱性チェック。

```typescript
// API設計
interface DependencyAuditor {
  // package.json/lock分析
  audit(packagePath: string): Promise<AuditResult>;
  
  // 特定パッケージのチェック
  checkPackage(name: string, version: string): Promise<PackageVulnerability[]>;
  
  // アップグレード提案
  suggestUpgrades(auditResult: AuditResult): Promise<UpgradeSuggestion[]>;
}

interface AuditResult {
  totalDependencies: number;
  vulnerableDependencies: number;
  
  vulnerabilities: DependencyVulnerability[];
  
  summary: {
    critical: number;
    high: number;
    medium: number;
    low: number;
  };
}

interface DependencyVulnerability {
  package: string;
  version: string;
  vulnerability: {
    id: string;      // CVE ID
    title: string;
    severity: Severity;
    cvss: number;
    description: string;
    patchedVersions: string;
  };
  path: string[];    // 依存パス
}
```

### 3.5 シークレット検出（Secrets Detector）

ハードコードされた認証情報の検出。

```typescript
// API設計
interface SecretsDetector {
  // スキャン
  scan(path: string): Promise<SecretFinding[]>;
  
  // カスタムパターン追加
  addPattern(pattern: SecretPattern): void;
}

interface SecretFinding {
  type: SecretType;  // 'api-key' | 'password' | 'token' | 'private-key' | etc.
  value: string;     // マスク済み値
  location: Location;
  entropy: number;   // エントロピー値
  confidence: number;
}

type SecretType = 
  | 'github-token'
  | 'azure-key'
  | 'google-api-key'
  | 'jwt-secret'
  | 'private-key'
  | 'password'
  | 'database-url'
  | 'generic-secret';
```

---

## 4. セキュリティルール

### 4.1 OWASP Top 10 (2021)

| ID | 脆弱性 | 実装優先度 |
|----|--------|----------|
| A01:2021 | Broken Access Control | P0 |
| A02:2021 | Cryptographic Failures | P0 |
| A03:2021 | Injection | P0 |
| A04:2021 | Insecure Design | P1 |
| A05:2021 | Security Misconfiguration | P1 |
| A06:2021 | Vulnerable Components | P0 |
| A07:2021 | Auth Failures | P0 |
| A08:2021 | Software/Data Integrity | P1 |
| A09:2021 | Security Logging Failures | P2 |
| A10:2021 | SSRF | P1 |

### 4.2 CWE Top 25 (2024)

| Rank | CWE ID | 名前 | 実装優先度 |
|------|--------|------|----------|
| 1 | CWE-79 | XSS | P0 |
| 2 | CWE-89 | SQL Injection | P0 |
| 3 | CWE-20 | Improper Input Validation | P0 |
| 4 | CWE-125 | Out-of-bounds Read | P1 |
| 5 | CWE-78 | OS Command Injection | P0 |
| 6 | CWE-416 | Use After Free | P1 |
| 7 | CWE-22 | Path Traversal | P0 |
| 8 | CWE-352 | CSRF | P0 |
| 9 | CWE-434 | Unrestricted Upload | P1 |
| 10 | CWE-862 | Missing Authorization | P0 |

### 4.3 ルール定義形式

```yaml
# rules/owasp-top-10.yaml
rules:
  - id: A03-injection-sqli
    name: SQL Injection
    owasp: A03:2021
    cwe: CWE-89
    severity: critical
    
    patterns:
      - pattern: |
          $DB.query($USER_INPUT)
        message: "Potential SQL injection vulnerability"
      - pattern: |
          $DB.execute(`... ${$USER_INPUT} ...`)
        message: "String interpolation in SQL query"
    
    fix_template: |
      // Use parameterized queries
      $DB.query($QUERY, [$USER_INPUT])
    
    references:
      - https://owasp.org/Top10/A03_2021-Injection/
      - https://cwe.mitre.org/data/definitions/89.html
```

---

## 5. MCPツール

### 5.1 ツール一覧

| ツール名 | 説明 |
|---------|------|
| `security_scan` | 脆弱性スキャン |
| `security_taint_analyze` | テイント分析 |
| `security_audit_deps` | 依存関係監査 |
| `security_detect_secrets` | シークレット検出 |
| `security_generate_fix` | 修正生成 |
| `security_verify_fix` | 修正検証 |
| `security_apply_fix` | 修正適用 |
| `security_compliance_check` | コンプライアンスチェック |

### 5.2 ツール定義

```typescript
// tools/security-tools.ts
export const securityTools: ToolDefinition[] = [
  {
    name: 'security_scan',
    description: 'Scan code for security vulnerabilities (OWASP Top 10, CWE Top 25)',
    inputSchema: {
      type: 'object',
      properties: {
        path: { type: 'string', description: 'Path to scan' },
        rules: { 
          type: 'array', 
          items: { type: 'string' },
          description: 'Rule sets to apply'
        },
        severity: {
          type: 'array',
          items: { type: 'string', enum: ['critical', 'high', 'medium', 'low'] }
        }
      },
      required: ['path']
    },
    handler: async (params) => {
      const scanner = new VulnerabilityScanner();
      return await scanner.scan(params.path);
    }
  },
  
  {
    name: 'security_generate_fix',
    description: 'Generate fix for a vulnerability using LLM + symbolic verification',
    inputSchema: {
      type: 'object',
      properties: {
        vulnerability: { type: 'object', description: 'Vulnerability to fix' },
        maxCandidates: { type: 'number', default: 3 }
      },
      required: ['vulnerability']
    },
    handler: async (params) => {
      const pipeline = new FixPipeline();
      return await pipeline.generateFix(params.vulnerability);
    }
  }
];
```

---

## 6. CLIコマンド

```bash
# 脆弱性スキャン
npx musubix security scan ./src
npx musubix security scan ./src --rules owasp-top-10,cwe-top-25
npx musubix security scan ./src --severity critical,high

# テイント分析
npx musubix security taint ./src
npx musubix security taint ./src --sources user-input --sinks sql,eval

# 依存関係監査
npx musubix security audit
npx musubix security audit --fix  # 自動アップグレード

# シークレット検出
npx musubix security secrets ./src
npx musubix security secrets ./src --entropy 4.5

# 自動修正
npx musubix security fix ./src              # スキャン→修正
npx musubix security fix ./src --dry-run    # プレビューのみ
npx musubix security fix ./src --verify     # Z3検証付き

# コンプライアンスレポート
npx musubix security compliance ./src --standard owasp
npx musubix security compliance ./src --output report.html
```

---

## 7. YATA統合

### 7.1 セキュリティ知識グラフ

```turtle
@prefix sec: <http://musubix.dev/security#> .
@prefix vuln: <http://musubix.dev/vulnerabilities#> .

# 脆弱性タイプ
vuln:SQLInjection a sec:VulnerabilityType ;
    sec:cwe "CWE-89" ;
    sec:owasp "A03:2021" ;
    sec:severity "critical" .

# 検出パターン
sec:SQLInjectionPattern a sec:DetectionPattern ;
    sec:detects vuln:SQLInjection ;
    sec:pattern "$DB.query($USER_INPUT)" .

# 修正パターン
sec:ParameterizedQueryFix a sec:FixPattern ;
    sec:fixes vuln:SQLInjection ;
    sec:template "$DB.query($QUERY, [$USER_INPUT])" ;
    sec:successRate 0.95 .
```

### 7.2 学習フィードバック

```typescript
// 修正成功/失敗を学習
await yata.addTriple({
  subject: `fix:${fixId}`,
  predicate: 'sec:outcome',
  object: result.success ? 'sec:Success' : 'sec:Failure',
});

// パターンの成功率更新
await securityPatterns.updateSuccessRate(pattern.id, result);
```

---

## 8. 実装スケジュール

### Phase 1: Foundation (Week 1-2)

| タスク | 優先度 | 担当 |
|--------|--------|------|
| パッケージ構造作成 | P0 | - |
| 型定義 | P0 | - |
| ルールエンジン基盤 | P0 | - |
| OWASP Top 10ルール (P0分) | P0 | - |

### Phase 2: Core Analyzers (Week 3-4)

| タスク | 優先度 | 担当 |
|--------|--------|------|
| VulnerabilityScanner | P0 | - |
| TaintAnalyzer | P0 | - |
| SecretsDetector | P0 | - |
| DependencyAuditor | P1 | - |

### Phase 3: Fix Pipeline (Week 5-6)

| タスク | 優先度 | 担当 |
|--------|--------|------|
| FixGenerator (LLM) | P0 | - |
| FixVerifier (Z3) | P0 | - |
| FixApplier | P1 | - |
| YATA統合 | P1 | - |

### Phase 4: Polish (Week 7-8)

| タスク | 優先度 | 担当 |
|--------|--------|------|
| MCPツール | P0 | - |
| CLIコマンド | P0 | - |
| テスト (>90%カバレッジ) | P0 | - |
| ドキュメント | P1 | - |

---

## 9. テスト計画

### 9.1 ユニットテスト

| モジュール | テスト数 (目標) |
|-----------|---------------|
| TaintAnalyzer | 50+ |
| VulnerabilityScanner | 80+ |
| RuleEngine | 40+ |
| FixPipeline | 60+ |
| DependencyAuditor | 30+ |
| SecretsDetector | 30+ |
| **合計** | **290+** |

### 9.2 統合テスト

- 実際の脆弱性コード（OWASP WebGoat、DVWA）でのテスト
- 偽陽性/偽陰性率の測定
- 修正パイプラインのE2Eテスト

### 9.3 ベンチマーク

| 指標 | 目標値 |
|------|--------|
| 検出率（True Positive） | >90% |
| 偽陽性率（False Positive） | <5% |
| 修正成功率 | >80% |
| スキャン速度 | <10s/1000行 |

---

## 10. 成功指標

| 指標 | v1.8.0目標 |
|------|-----------|
| OWASP Top 10 カバレッジ | 100% |
| CWE Top 25 カバレッジ | 80% |
| 修正検証成功率 | >80% |
| テストカバレッジ | >90% |
| ドキュメント完成度 | 100% |

---

**© 2026 MUSUBIX Project**
