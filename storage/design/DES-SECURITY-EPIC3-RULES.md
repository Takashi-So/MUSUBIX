# EPIC-3: OWASP Top 10 / CWE Top 25 ルール 設計書

**Version**: 1.0.0
**Date**: 2026-01-08
**Status**: ✅ APPROVED
**Trace**: REQ-RULE-001 〜 REQ-RULE-005

---

## 1. 概要

### 1.1 目的

OWASP Top 10 2021 および CWE Top 25 2023 の全項目を検出するルールエンジンを設計する。

### 1.2 設計方針

- **Rule Engine**: プラガブルなルール実行基盤
- **Detection Methods**: テイント分析、パターンマッチ、型解析の組み合わせ
- **Output**: SARIF 2.1.0 準拠（GitHub Code Scanning 互換）

---

## 2. C4モデル

### 2.1 Component Diagram

```
packages/security/src/
├── rules/                          # NEW: ルールエンジン
│   ├── index.ts                    # Public exports
│   ├── engine/
│   │   ├── rule-engine.ts          # ルール実行エンジン
│   │   ├── rule-registry.ts        # ルール登録・管理
│   │   └── rule-context.ts         # 実行コンテキスト
│   ├── config/
│   │   ├── config-parser.ts        # 設定ファイルパーサー
│   │   ├── config-schema.ts        # JSON Schema
│   │   └── profiles.ts             # プロファイル定義
│   ├── owasp/
│   │   ├── index.ts                # OWASP ルール exports
│   │   ├── a01-broken-access.ts    # A01: Broken Access Control
│   │   ├── a02-crypto-failures.ts  # A02: Cryptographic Failures
│   │   ├── a03-injection.ts        # A03: Injection
│   │   ├── a04-insecure-design.ts  # A04: Insecure Design
│   │   ├── a05-misconfig.ts        # A05: Security Misconfiguration
│   │   ├── a06-vuln-components.ts  # A06: Vulnerable Components
│   │   ├── a07-auth-failures.ts    # A07: Auth Failures
│   │   ├── a08-data-integrity.ts   # A08: Data Integrity Failures
│   │   ├── a09-logging-failures.ts # A09: Logging Failures
│   │   └── a10-ssrf.ts             # A10: SSRF
│   ├── cwe/
│   │   ├── index.ts                # CWE ルール exports
│   │   ├── cwe-787.ts              # Out-of-bounds Write
│   │   ├── cwe-079.ts              # XSS
│   │   ├── cwe-089.ts              # SQL Injection
│   │   ├── ... (25 files)
│   │   └── cwe-276.ts              # Incorrect Default Permissions
│   ├── output/
│   │   ├── sarif-generator.ts      # SARIF 2.1.0 出力
│   │   ├── markdown-generator.ts   # Markdown 出力
│   │   └── html-generator.ts       # HTML 出力
│   └── suppression/
│       ├── inline-parser.ts        # インラインサプレッション
│       └── suppression-manager.ts  # サプレッション管理
└── types/
    └── rule.ts                     # 既存 (拡張)
```

---

## 3. コンポーネント設計

### 3.1 DES-RULE-001: Rule Engine

**Trace**: REQ-RULE-003

```typescript
// packages/security/src/rules/engine/rule-engine.ts

/**
 * ルール実行結果
 */
export interface RuleResult {
  ruleId: string;
  findings: RuleFinding[];
  executionTime: number;
  errors: string[];
}

/**
 * 検出結果
 */
export interface RuleFinding {
  id: string;
  ruleId: string;
  severity: 'critical' | 'high' | 'medium' | 'low' | 'info';
  message: string;
  location: {
    file: string;
    startLine: number;
    endLine: number;
    startColumn?: number;
    endColumn?: number;
  };
  cwe?: string;
  owasp?: string;
  remediation?: string;
  suppressed?: boolean;
  suppressionReason?: string;
}

/**
 * ルールエンジン
 */
export class RuleEngine {
  private registry: RuleRegistry;
  private config: RuleConfig;
  private suppressionManager: SuppressionManager;
  
  constructor(options?: RuleEngineOptions);
  
  /**
   * ファイルに対してルールを実行
   */
  async analyzeFile(filePath: string): Promise<RuleResult[]>;
  
  /**
   * プロジェクト全体を解析
   */
  async analyzeProject(projectDir: string): Promise<AnalysisReport>;
  
  /**
   * 特定ルールのみ実行
   */
  async runRule(ruleId: string, filePath: string): Promise<RuleResult>;
  
  /**
   * カスタムルールを追加
   */
  registerRule(rule: SecurityRule): void;
}
```

### 3.2 DES-RULE-002: Rule Interface

**Trace**: REQ-RULE-003

```typescript
// packages/security/src/types/rule.ts (拡張)

/**
 * セキュリティルール基底インターフェース
 */
export interface SecurityRule {
  /** ルールID (e.g., "CWE-079", "OWASP-A03") */
  id: string;
  /** ルール名 */
  name: string;
  /** 説明 */
  description: string;
  /** デフォルト重大度 */
  defaultSeverity: RuleSeverity;
  /** 関連 CWE */
  cwe?: string[];
  /** 関連 OWASP */
  owasp?: string[];
  /** 検出メソッド */
  detectionMethod: DetectionMethod;
  /** ルール実行 */
  analyze(context: RuleContext): Promise<RuleFinding[]>;
  /** 修正提案生成 */
  getSuggestion?(finding: RuleFinding): FixSuggestion | null;
}

export type DetectionMethod = 
  | 'taint-analysis'
  | 'pattern-match'
  | 'type-analysis'
  | 'config-check'
  | 'dependency-check'
  | 'combined';

export type RuleSeverity = 'critical' | 'high' | 'medium' | 'low' | 'info';
```

### 3.3 DES-RULE-003: Rule Context

**Trace**: REQ-RULE-003

```typescript
// packages/security/src/rules/engine/rule-context.ts

/**
 * ルール実行コンテキスト
 */
export interface RuleContext {
  /** ファイルパス */
  filePath: string;
  /** ソースコード */
  sourceCode: string;
  /** AST (ts-morph) */
  sourceFile: SourceFile;
  /** テイント分析結果 (EPIC-1) */
  taintAnalysis?: TaintAnalysisResult;
  /** DFG (musubix-dfg) */
  dfg?: DataFlowGraph;
  /** プロジェクト設定 */
  config: RuleConfig;
  /** 他ルールの結果参照 */
  previousResults: Map<string, RuleResult>;
}

export class RuleContextBuilder {
  /**
   * コンテキストを構築
   */
  async build(filePath: string, options: BuildOptions): Promise<RuleContext>;
  
  /**
   * テイント分析を追加
   */
  withTaintAnalysis(enabled: boolean): this;
  
  /**
   * DFG を追加
   */
  withDFG(enabled: boolean): this;
}
```

### 3.4 DES-RULE-004: Config Parser

**Trace**: REQ-RULE-004

```typescript
// packages/security/src/rules/config/config-parser.ts

/**
 * ルール設定
 */
export interface RuleConfig {
  /** プロファイル */
  profile: 'strict' | 'standard' | 'permissive';
  /** ルール個別設定 */
  rules: Record<string, RuleSettings>;
  /** 除外パターン */
  exclude: string[];
  /** 含めるパターン */
  include: string[];
  /** 重大度閾値 */
  severityThreshold: RuleSeverity;
}

export interface RuleSettings {
  enabled: boolean;
  severity?: RuleSeverity;
  options?: Record<string, unknown>;
}

/**
 * 設定ファイルパーサー
 */
export class ConfigParser {
  /**
   * 設定ファイルを読み込み
   */
  async load(projectDir: string): Promise<RuleConfig>;
  
  /**
   * プロファイルをロード
   */
  loadProfile(name: string): RuleConfig;
  
  /**
   * 設定をマージ（継承）
   */
  merge(base: RuleConfig, override: Partial<RuleConfig>): RuleConfig;
  
  /**
   * 設定を検証
   */
  validate(config: unknown): config is RuleConfig;
}
```

### 3.5 DES-RULE-005: OWASP A03 Example (Injection)

**Trace**: REQ-RULE-001

```typescript
// packages/security/src/rules/owasp/a03-injection.ts

/**
 * OWASP A03: Injection
 * SQL, NoSQL, OS Command, LDAP Injection 検出
 */
export class A03InjectionRule implements SecurityRule {
  id = 'OWASP-A03';
  name = 'Injection';
  description = 'Detects SQL, NoSQL, OS Command, and LDAP injection vulnerabilities';
  defaultSeverity: RuleSeverity = 'critical';
  cwe = ['CWE-89', 'CWE-78', 'CWE-90', 'CWE-943'];
  owasp = ['A03:2021'];
  detectionMethod: DetectionMethod = 'taint-analysis';
  
  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    
    // EPIC-1 のテイント分析結果を活用
    if (context.taintAnalysis) {
      for (const flow of context.taintAnalysis.taintedFlows) {
        if (this.isInjectionSink(flow.sink)) {
          findings.push(this.createFinding(flow, context));
        }
      }
    }
    
    return findings;
  }
  
  private isInjectionSink(sink: TaintSink): boolean {
    return ['sql-query', 'nosql-query', 'command-exec', 'ldap-query']
      .includes(sink.category);
  }
  
  getSuggestion(finding: RuleFinding): FixSuggestion | null {
    // EPIC-4 で実装
    return null;
  }
}
```

### 3.6 DES-RULE-006: CWE-079 Example (XSS)

**Trace**: REQ-RULE-002

```typescript
// packages/security/src/rules/cwe/cwe-079.ts

/**
 * CWE-79: Improper Neutralization of Input During Web Page Generation (XSS)
 */
export class CWE079Rule implements SecurityRule {
  id = 'CWE-079';
  name = 'Cross-site Scripting (XSS)';
  description = 'Detects potential XSS vulnerabilities where user input reaches HTML output';
  defaultSeverity: RuleSeverity = 'high';
  cwe = ['CWE-79'];
  owasp = ['A03:2021'];
  detectionMethod: DetectionMethod = 'taint-analysis';
  
  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    
    if (context.taintAnalysis) {
      for (const flow of context.taintAnalysis.taintedFlows) {
        if (flow.sink.category === 'html-output') {
          // サニタイザー通過チェック
          if (!this.hasSanitizer(flow)) {
            findings.push(this.createFinding(flow, context));
          }
        }
      }
    }
    
    return findings;
  }
  
  private hasSanitizer(flow: TaintFlow): boolean {
    return flow.sanitizers.some(s => 
      s.category === 'html-escape' || s.category === 'html-sanitize'
    );
  }
}
```

### 3.7 DES-RULE-007: SARIF Generator

**Trace**: REQ-RULE-005

```typescript
// packages/security/src/rules/output/sarif-generator.ts

/**
 * SARIF 2.1.0 出力生成
 * @see https://docs.oasis-open.org/sarif/sarif/v2.1.0/sarif-v2.1.0.html
 */
export class SARIFGenerator {
  /**
   * SARIF レポートを生成
   */
  generate(report: AnalysisReport): SARIFLog {
    return {
      $schema: 'https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json',
      version: '2.1.0',
      runs: [{
        tool: {
          driver: {
            name: 'musubix-security',
            version: '2.1.0',
            informationUri: 'https://github.com/nahisaho/musubix',
            rules: this.generateRuleDescriptors(report),
          },
        },
        results: this.generateResults(report),
      }],
    };
  }
  
  private generateRuleDescriptors(report: AnalysisReport): SARIFRuleDescriptor[];
  private generateResults(report: AnalysisReport): SARIFResult[];
}
```

### 3.8 DES-RULE-008: Inline Suppression

**Trace**: REQ-RULE-003

```typescript
// packages/security/src/rules/suppression/inline-parser.ts

/**
 * インラインサプレッションパーサー
 * 
 * 対応形式:
 * - // security-ignore: CWE-79
 * - // security-ignore: CWE-79, CWE-89
 * - // security-ignore-next-line: OWASP-A03
 * - /* security-ignore-file: CWE-79 *\/
 */
export class InlineSuppressionParser {
  private readonly patterns = [
    /\/\/\s*security-ignore:\s*(.+)/,
    /\/\/\s*security-ignore-next-line:\s*(.+)/,
    /\/\*\s*security-ignore-file:\s*(.+)\s*\*\//,
  ];
  
  /**
   * ファイルからサプレッションを抽出
   */
  parse(sourceCode: string): Suppression[];
  
  /**
   * 行がサプレッションされているか
   */
  isSuppressed(line: number, ruleId: string, suppressions: Suppression[]): boolean;
}

interface Suppression {
  type: 'line' | 'next-line' | 'file';
  ruleIds: string[];
  line: number;
  reason?: string;
}
```

---

## 4. ルール一覧

### 4.1 OWASP Top 10 2021

| ID | カテゴリ | 実装ファイル | 検出方法 |
|----|---------|-------------|----------|
| OWASP-A01 | Broken Access Control | a01-broken-access.ts | パターン + テイント |
| OWASP-A02 | Cryptographic Failures | a02-crypto-failures.ts | パターン |
| OWASP-A03 | Injection | a03-injection.ts | テイント |
| OWASP-A04 | Insecure Design | a04-insecure-design.ts | パターン |
| OWASP-A05 | Security Misconfiguration | a05-misconfig.ts | 設定検査 |
| OWASP-A06 | Vulnerable Components | a06-vuln-components.ts | CVE連携 (EPIC-2) |
| OWASP-A07 | Auth Failures | a07-auth-failures.ts | パターン + テイント |
| OWASP-A08 | Data Integrity Failures | a08-data-integrity.ts | テイント |
| OWASP-A09 | Logging Failures | a09-logging-failures.ts | パターン |
| OWASP-A10 | SSRF | a10-ssrf.ts | テイント |

### 4.2 CWE Top 25 2023

| Rank | CWE | 名称 | 検出方法 |
|------|-----|------|----------|
| 1 | CWE-787 | Out-of-bounds Write | バッファ解析 |
| 2 | CWE-079 | XSS | テイント |
| 3 | CWE-089 | SQL Injection | テイント |
| 4 | CWE-416 | Use After Free | メモリ解析 |
| 5 | CWE-078 | OS Command Injection | テイント |
| 6 | CWE-020 | Improper Input Validation | パターン |
| 7 | CWE-125 | Out-of-bounds Read | バッファ解析 |
| 8 | CWE-022 | Path Traversal | テイント |
| 9 | CWE-352 | CSRF | パターン |
| 10 | CWE-434 | Unrestricted Upload | パターン |
| 11 | CWE-862 | Missing Authorization | パターン |
| 12 | CWE-476 | NULL Pointer Dereference | 型解析 |
| 13 | CWE-287 | Improper Authentication | パターン |
| 14 | CWE-190 | Integer Overflow | 数値解析 |
| 15 | CWE-502 | Deserialization | テイント |
| 16 | CWE-077 | Command Injection | テイント |
| 17 | CWE-119 | Buffer Overflow | バッファ解析 |
| 18 | CWE-798 | Hard-coded Credentials | パターン |
| 19 | CWE-918 | SSRF | テイント |
| 20 | CWE-306 | Missing Authentication | パターン |
| 21 | CWE-362 | Race Condition | 並行性解析 |
| 22 | CWE-269 | Improper Privilege Mgmt | パターン |
| 23 | CWE-094 | Code Injection | テイント |
| 24 | CWE-863 | Incorrect Authorization | パターン |
| 25 | CWE-276 | Incorrect Default Perms | パターン |

---

## 5. 設定ファイル形式

```yaml
# .musubix-security.yml

# プロファイル: strict | standard | permissive
profile: standard

# ルール個別設定
rules:
  CWE-079:
    enabled: true
    severity: critical
  CWE-089:
    enabled: true
    severity: critical
  # ルールを無効化
  CWE-787:
    enabled: false

# 除外パターン
exclude:
  - "**/*.test.ts"
  - "**/node_modules/**"
  - "**/dist/**"

# 重大度閾値（これ以下は報告しない）
severityThreshold: low
```

---

## 6. タスク → 設計 トレーサビリティ

| タスク | 設計 |
|--------|------|
| TSK-RULE-001 | DES-RULE-001 (Rule Engine), DES-RULE-002 (Rule Interface) |
| TSK-RULE-002 | DES-RULE-004 (Config Parser) |
| TSK-RULE-003 | DES-RULE-005 (OWASP A01-A05) |
| TSK-RULE-004 | DES-RULE-005 (OWASP A06-A10) |
| TSK-RULE-005 | DES-RULE-006 (CWE 1-13) |
| TSK-RULE-006 | DES-RULE-006 (CWE 14-25) |
| TSK-RULE-007 | DES-RULE-008 (Inline Suppression) |
| TSK-RULE-008 | DES-RULE-007 (SARIF Generator) |
| TSK-RULE-009 | DES-RULE-002 (Custom Rule API) |
| TSK-RULE-010 | (テストスイート) |

---

## 7. 承認

- [x] アーキテクチャの妥当性
- [x] ルールカバレッジの完全性
- [x] EPIC-1 テイント分析との統合
- [x] タスク分解の妥当性
- [x] ユーザー承認 (2026-01-08)
