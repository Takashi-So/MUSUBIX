# 設計書: MUSUBIX Security Package

**文書ID**: DES-SEC-001  
**バージョン**: 0.2.0 (Revised)  
**作成日**: 2026-01-06  
**更新日**: 2026-01-06  
**ステータス**: ✅ レビュー完了  
**トレース元**: REQ-SEC-001

---

## 1. 概要

### 1.1 目的

本文書は、MUSUBIX Security Package (`@nahisaho/musubix-security`) のC4モデルに基づく設計を定義する。

### 1.2 設計原則

| 原則 | 説明 |
|------|------|
| **Neuro-Symbolic統合** | LLM（VS Code LM API）とシンボリック推論（Z3）の組み合わせ |
| **Library-First** | 独立したnpmパッケージとして実装（憲法I条） |
| **Fail-Safe** | 外部サービス障害時もローカル機能で継続 |
| **トレーサビリティ** | 全コンポーネントが要件IDに紐づく |

---

## 2. C4 Level 1: System Context

### 2.1 システムコンテキスト図

```
┌─────────────────────────────────────────────────────────────────────┐
│                        External Systems                             │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐              │
│  │   VS Code    │  │   GitHub     │  │     NVD      │              │
│  │   LM API     │  │   Advisory   │  │   Database   │              │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘              │
│         │                 │                 │                       │
└─────────┼─────────────────┼─────────────────┼───────────────────────┘
          │                 │                 │
          ▼                 ▼                 ▼
┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│                    MUSUBIX Security Package                         │
│                  (@nahisaho/musubix-security)                       │
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  • 脆弱性スキャン (OWASP/CWE)                               │   │
│  │  • テイント分析                                              │   │
│  │  • 自動修正 (LLM + Z3検証)                                  │   │
│  │  • シークレット検出                                         │   │
│  │  • 依存関係監査                                             │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└──────────────────────────────┬──────────────────────────────────────┘
                               │
          ┌────────────────────┼────────────────────┐
          │                    │                    │
          ▼                    ▼                    ▼
┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐
│   MUSUBIX Core   │  │   MUSUBIX MCP    │  │   YATA Local     │
│                  │  │     Server       │  │  Knowledge Graph │
└──────────────────┘  └──────────────────┘  └──────────────────┘
```

### 2.2 外部システム

| システム | 役割 | プロトコル |
|---------|------|-----------|
| **VS Code LM API** | LLMによる修正コード生成 | vscode.lm |
| **GitHub Advisory** | 依存関係脆弱性データ | HTTPS/REST |
| **NVD Database** | CVE/CWE脆弱性データベース | HTTPS/REST |
| **MUSUBIX Core** | EARS検証、コード生成基盤 | npm import |
| **MUSUBIX MCP Server** | AIエージェント統合 | MCP Protocol |
| **YATA Local** | 脆弱性・修正パターン知識グラフ | npm import |

---

## 3. C4 Level 2: Container

### 3.1 コンテナ図

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       @nahisaho/musubix-security                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐             │
│  │   CLI Layer     │  │   MCP Tools     │  │  Library API    │             │
│  │  (Commander)    │  │   (5 tools)     │  │   (Public)      │             │
│  └────────┬────────┘  └────────┬────────┘  └────────┬────────┘             │
│           │                    │                    │                       │
│           └────────────────────┼────────────────────┘                       │
│                                │                                            │
│                                ▼                                            │
│  ┌──────────────────────────────────────────────────────────────────────┐  │
│  │                        Core Services                                  │  │
│  │  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐         │  │
│  │  │ Vulnerability  │  │    Taint       │  │      Fix       │         │  │
│  │  │   Scanner      │  │   Analyzer     │  │   Pipeline     │         │  │
│  │  └───────┬────────┘  └───────┬────────┘  └───────┬────────┘         │  │
│  │          │                   │                   │                   │  │
│  │  ┌───────┴───────────────────┴───────────────────┴────────────┐     │  │
│  │  │                    Analysis Engine                          │     │  │
│  │  │  (TypeScript AST Parser + Data Flow Graph)                 │     │  │
│  │  └────────────────────────────────────────────────────────────┘     │  │
│  └──────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  ┌──────────────────────────────────────────────────────────────────────┐  │
│  │                      Supporting Services                              │  │
│  │  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐         │  │
│  │  │    Secrets     │  │  Dependency    │  │   Compliance   │         │  │
│  │  │   Detector     │  │   Auditor      │  │    Checker     │         │  │
│  │  └────────────────┘  └────────────────┘  └────────────────┘         │  │
│  └──────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  ┌──────────────────────────────────────────────────────────────────────┐  │
│  │                      Infrastructure                                   │  │
│  │  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐         │  │
│  │  │  Rule Engine   │  │  LM Client     │  │  YATA Adapter  │         │  │
│  │  │  (YAML Rules)  │  │ (VS Code LM)   │  │                │         │  │
│  │  └────────────────┘  └────────────────┘  └────────────────┘         │  │
│  └──────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 3.2 コンテナ一覧

| コンテナ | 技術 | 責務 | トレース |
|---------|------|------|---------|
| **CLI Layer** | Commander.js | CLIコマンド提供 | DES-SEC-CLI-* |
| **MCP Tools** | MCP SDK | AIエージェント統合 | DES-SEC-MCP-* |
| **Library API** | TypeScript | プログラマティックAPI | - |
| **Vulnerability Scanner** | TypeScript | 脆弱性検出 | DES-SEC-SCAN-* |
| **Taint Analyzer** | TypeScript | データフロー追跡 | DES-SEC-TAINT-* |
| **Fix Pipeline** | TypeScript + Z3 | 修正生成・検証 | DES-SEC-FIX-* |
| **Secrets Detector** | TypeScript | シークレット検出 | DES-SEC-SECRET-* |
| **Dependency Auditor** | TypeScript | npm監査 | DES-SEC-DEPS-* |
| **Compliance Checker** | TypeScript | ASVS準拠チェック | DES-SEC-COMP-* |
| **Rule Engine** | YAML | セキュリティルール定義 | - |
| **LM Client** | vscode.lm | LLM統合 | - |
| **YATA Adapter** | TypeScript | 知識グラフ連携 | DES-SEC-YATA-* |

---

## 4. C4 Level 3: Component

### 4.1 Vulnerability Scanner コンポーネント

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Vulnerability Scanner                            │
│                       DES-SEC-SCAN-*                                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                    VulnerabilityScanner                      │   │
│  │                    <<interface>>                             │   │
│  │  + scan(files: string[]): Promise<Vulnerability[]>          │   │
│  │  + scanIncremental(file: string): Promise<Vulnerability[]>  │   │
│  │  + configure(options: ScanOptions): void                    │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              │                                      │
│              ┌───────────────┼───────────────┐                      │
│              │               │               │                      │
│              ▼               ▼               ▼                      │
│  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐           │
│  │  OWASPScanner │  │   CWEScanner  │  │ CustomScanner │           │
│  │  (Top 10)     │  │   (Top 25)    │  │               │           │
│  └───────┬───────┘  └───────┬───────┘  └───────┬───────┘           │
│          │                  │                  │                    │
│          └──────────────────┼──────────────────┘                    │
│                             │                                       │
│                             ▼                                       │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                      RuleEngine                              │   │
│  │  + loadRules(path: string): Rule[]                          │   │
│  │  + match(ast: AST, rule: Rule): Match[]                     │   │
│  │  + getSeverity(match: Match): Severity                      │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                             │                                       │
│              ┌──────────────┴──────────────┐                       │
│              ▼                             ▼                        │
│  ┌─────────────────────┐      ┌─────────────────────┐              │
│  │  rules/             │      │  AnalysisEngine     │              │
│  │  ├─ owasp-top-10.yaml│     │  + parse(code)      │              │
│  │  ├─ cwe-top-25.yaml │      │  + buildCFG()       │              │
│  │  └─ custom/         │      │  + buildDFG()       │              │
│  └─────────────────────┘      └─────────────────────┘              │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

#### 4.1.1 コンポーネント詳細

| コンポーネント | 責務 | トレース |
|--------------|------|---------|
| **VulnerabilityScanner** | スキャンのエントリポイント | REQ-SEC-SCAN-001 |
| **OWASPScanner** | OWASP Top 10検出 | REQ-SEC-SCAN-002 |
| **CWEScanner** | CWE Top 25検出 | REQ-SEC-SCAN-003 |
| **RuleEngine** | YAMLルール読み込み・マッチング | - |
| **AnalysisEngine** | AST/CFG/DFG構築 | - |

---

### 4.2 Taint Analyzer コンポーネント

```
┌─────────────────────────────────────────────────────────────────────┐
│                       Taint Analyzer                                │
│                       DES-SEC-TAINT-*                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                      TaintAnalyzer                           │   │
│  │  + analyze(code: string): TaintResult                       │   │
│  │  + findPaths(source: Node, sink: Node): TaintPath[]        │   │
│  │  + registerSanitizer(name: string, config: Config): void   │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              │                                      │
│              ┌───────────────┼───────────────┐                      │
│              ▼               ▼               ▼                      │
│  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐           │
│  │ SourceDetector│  │  SinkDetector │  │SanitizerRegistry│         │
│  │               │  │               │  │               │           │
│  │ • req.body    │  │ • SQL queries │  │ • escape()    │           │
│  │ • req.query   │  │ • eval()      │  │ • sanitize()  │           │
│  │ • req.params  │  │ • innerHTML   │  │ • validate()  │           │
│  │ • env vars    │  │ • exec()      │  │ • encode()    │           │
│  │ • file reads  │  │ • file writes │  │               │           │
│  └───────────────┘  └───────────────┘  └───────────────┘           │
│                              │                                      │
│                              ▼                                      │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                    DataFlowGraph                             │   │
│  │  + addNode(node: DFGNode): void                             │   │
│  │  + addEdge(from: DFGNode, to: DFGNode): void               │   │
│  │  + findPath(source: DFGNode, sink: DFGNode): DFGPath[]     │   │
│  │  + propagateTaint(source: DFGNode): TaintedNode[]          │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

#### 4.2.1 コンポーネント詳細

| コンポーネント | 責務 | トレース |
|--------------|------|---------|
| **TaintAnalyzer** | テイント分析のエントリポイント | REQ-SEC-TAINT-001〜003 |
| **SourceDetector** | 汚染源の検出 | REQ-SEC-TAINT-001 |
| **SinkDetector** | 危険なシンクの検出 | REQ-SEC-TAINT-002 |
| **SanitizerRegistry** | サニタイザー関数の管理 | REQ-SEC-TAINT-004 |
| **DataFlowGraph** | データフローグラフ構築・探索 | REQ-SEC-TAINT-003 |

---

### 4.3 Fix Pipeline コンポーネント

```
┌─────────────────────────────────────────────────────────────────────┐
│                        Fix Pipeline                                 │
│                        DES-SEC-FIX-*                                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                      FixPipeline                             │   │
│  │  + generateFix(vuln: Vulnerability): Promise<Fix[]>         │   │
│  │  + verifyFix(fix: Fix): Promise<VerificationResult>        │   │
│  │  + applyFix(fix: Fix): Promise<ApplyResult>                │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              │                                      │
│              ┌───────────────┴───────────────┐                      │
│              ▼                               ▼                      │
│  ┌─────────────────────┐        ┌─────────────────────┐            │
│  │    FixGenerator     │        │    FixVerifier      │            │
│  │                     │        │                     │            │
│  │  ┌───────────────┐  │        │  ┌───────────────┐  │            │
│  │  │ LLMFixProvider│  │        │  │ Z3Verifier    │  │            │
│  │  │ (VS Code LM)  │  │        │  │ (SMT Solver)  │  │            │
│  │  └───────────────┘  │        │  └───────────────┘  │            │
│  │                     │        │                     │            │
│  │  ┌───────────────┐  │        │  ┌───────────────┐  │            │
│  │  │TemplateProvider│ │        │  │SemanticAnalyzer│ │            │
│  │  │ (Fallback)    │  │        │  │               │  │            │
│  │  └───────────────┘  │        │  └───────────────┘  │            │
│  └─────────────────────┘        └─────────────────────┘            │
│                                          │                          │
│                                          ▼                          │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                  VerificationEngine                          │   │
│  │  + checkVulnElimination(fix: Fix): boolean                  │   │
│  │  + checkNoNewVulns(fix: Fix): boolean                       │   │
│  │  + checkFunctionPreservation(fix: Fix): boolean             │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

#### 4.3.1 コンポーネント詳細

| コンポーネント | 責務 | トレース |
|--------------|------|---------|
| **FixPipeline** | 修正パイプライン全体制御 | REQ-SEC-FIX-001 |
| **FixGenerator** | 修正コード生成 | REQ-SEC-FIX-001, 005 |
| **LLMFixProvider** | VS Code LM APIによる修正生成 | REQ-SEC-FIX-001 |
| **TemplateProvider** | テンプレートベース修正（フォールバック） | REQ-SEC-FIX-006 |
| **FixVerifier** | 修正の形式検証 | REQ-SEC-FIX-002〜004 |
| **Z3Verifier** | Z3 SMTソルバによる検証 | REQ-SEC-FIX-002 |
| **SemanticAnalyzer** | 機能保持の検証 | REQ-SEC-FIX-004 |
| **VerificationEngine** | 検証ロジック統合 | REQ-SEC-FIX-003 |

---

### 4.4 Secrets Detector コンポーネント

```
┌─────────────────────────────────────────────────────────────────────┐
│                      Secrets Detector                               │
│                      DES-SEC-SECRET-*                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                    SecretsDetector                           │   │
│  │  + scan(code: string): Secret[]                             │   │
│  │  + addPattern(pattern: SecretPattern): void                 │   │
│  │  + setEntropyThreshold(threshold: number): void             │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              │                                      │
│              ┌───────────────┼───────────────┐                      │
│              ▼               ▼               ▼                      │
│  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐           │
│  │PatternMatcher │  │EntropyAnalyzer│  │ContextAnalyzer│           │
│  │               │  │               │  │               │           │
│  │ • GitHub Token│  │ threshold=4.5 │  │ • Variable    │           │
│  │ • Azure Key   │  │ Shannon entropy│ │   context     │           │
│  │ • Google API  │  │               │  │ • File type   │           │
│  │ • JWT Secret  │  │               │  │ • Comments    │           │
│  │ • DB ConnStr  │  │               │  │               │           │
│  └───────────────┘  └───────────────┘  └───────────────┘           │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

#### 4.4.1 コンポーネント詳細

| コンポーネント | 責務 | トレース |
|--------------|------|---------|
| **SecretsDetector** | シークレット検出エントリポイント | REQ-SEC-SECRET-001 |
| **PatternMatcher** | 既知パターンによる検出 | REQ-SEC-SECRET-003 |
| **EntropyAnalyzer** | エントロピー分析による検出 | REQ-SEC-SECRET-002 |
| **ContextAnalyzer** | 文脈解析による偽陽性削減 | - |

---

### 4.5 Dependency Auditor コンポーネント

```
┌─────────────────────────────────────────────────────────────────────┐
│                     Dependency Auditor                              │
│                     DES-SEC-DEPS-*                                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                   DependencyAuditor                          │   │
│  │  + audit(packageJson: string): AuditResult                  │   │
│  │  + getVulnerabilities(pkg: string): Vulnerability[]         │   │
│  │  + suggestUpgrade(pkg: string): UpgradeSuggestion          │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              │                                      │
│              ┌───────────────┼───────────────┐                      │
│              ▼               ▼               ▼                      │
│  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐           │
│  │ NVDClient     │  │GitHubAdvisory │  │UpgradeAdvisor │           │
│  │               │  │   Client      │  │               │           │
│  │ • CVE lookup  │  │ • GHSA lookup │  │ • semver calc │           │
│  │ • CVSS scores │  │ • severity    │  │ • breaking    │           │
│  │               │  │               │  │   change check│           │
│  └───────────────┘  └───────────────┘  └───────────────┘           │
│                              │                                      │
│                              ▼                                      │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │              TransitiveDependencyResolver                    │   │
│  │  + resolve(pkg: string, depth: number): DependencyTree      │   │
│  │  + findVulnerableTransitive(): VulnerableDep[]             │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

#### 4.5.1 コンポーネント詳細

| コンポーネント | 責務 | トレース |
|--------------|------|---------|
| **DependencyAuditor** | 依存関係監査エントリポイント | REQ-SEC-DEPS-001 |
| **NVDClient** | NVDデータベースへのアクセス | REQ-SEC-DEPS-001 |
| **GitHubAdvisoryClient** | GitHub Advisoryへのアクセス | REQ-SEC-DEPS-001 |
| **TransitiveDependencyResolver** | 推移的依存関係の解決 | REQ-SEC-DEPS-002 |
| **UpgradeAdvisor** | 安全なバージョンの提案 | REQ-SEC-DEPS-003 |

---

### 4.6 CLI & MCP コンポーネント

```
┌─────────────────────────────────────────────────────────────────────┐
│                       CLI & MCP Layer                               │
│                    DES-SEC-CLI-*, DES-SEC-MCP-*                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌──────────────────────────────┐  ┌──────────────────────────────┐│
│  │           CLI                │  │         MCP Tools            ││
│  │                              │  │                              ││
│  │  musubix security            │  │  security_scan               ││
│  │  ├─ scan <path>              │  │  security_fix                ││
│  │  ├─ fix <vuln-id>            │  │  security_audit_deps         ││
│  │  ├─ audit-deps               │  │  security_detect_secrets     ││
│  │  ├─ detect-secrets           │  │  security_compliance         ││
│  │  ├─ compliance               │  │                              ││
│  │  └─ --help                   │  │                              ││
│  │                              │  │                              ││
│  │  Exit Codes:                 │  │  Response Format:            ││
│  │  0 = success                 │  │  { vulnerabilities: [],      ││
│  │  1 = vulns found             │  │    fixes: [],                ││
│  │  2 = error                   │  │    metadata: {} }            ││
│  └──────────────────────────────┘  └──────────────────────────────┘│
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 5. C4 Level 4: Code（主要インターフェース）

### 5.1 型定義

```typescript
// types/vulnerability.ts
export interface Vulnerability {
  id: string;                          // e.g., "VULN-2026-001"
  type: VulnerabilityType;             // OWASP/CWE category
  severity: 'critical' | 'high' | 'medium' | 'low';
  cwes: string[];                      // e.g., ["CWE-79", "CWE-89"]
  location: SourceLocation;
  description: string;
  recommendation: string;
  confidence: number;                  // 0.0 - 1.0
}

export interface SourceLocation {
  file: string;
  startLine: number;
  endLine: number;
  startColumn: number;
  endColumn: number;
}

export type VulnerabilityType = 
  | 'injection'           // A03:2021
  | 'broken-auth'         // A07:2021
  | 'sensitive-exposure'  // A02:2021
  | 'xxe'                 // A05:2021
  | 'broken-access'       // A01:2021
  | 'misconfig'           // A05:2021
  | 'xss'                 // A03:2021
  | 'insecure-deser'      // A08:2021
  | 'vuln-components'     // A06:2021
  | 'insufficient-logging'; // A09:2021
```

### 5.2 主要サービスインターフェース

```typescript
// services/VulnerabilityScanner.ts
export interface IVulnerabilityScanner {
  scan(files: string[], options?: ScanOptions): Promise<ScanResult>;
  scanIncremental(file: string): Promise<ScanResult>;
  configure(options: ScanOptions): void;
}

export interface ScanOptions {
  severityFilter?: ('critical' | 'high' | 'medium' | 'low')[];
  rulesets?: ('owasp-top-10' | 'cwe-top-25' | 'custom')[];
  excludePatterns?: string[];
  maxFileSize?: number;
}

export interface ScanResult {
  vulnerabilities: Vulnerability[];
  scannedFiles: number;
  duration: number;
  timestamp: Date;
}
```

```typescript
// services/TaintAnalyzer.ts
export interface ITaintAnalyzer {
  analyze(code: string, file: string): Promise<TaintResult>;
  findPaths(sourceNode: string, sinkNode: string): TaintPath[];
  registerSanitizer(name: string, config: SanitizerConfig): void;
}

export interface TaintResult {
  sources: TaintSource[];
  sinks: TaintSink[];
  paths: TaintPath[];
  sanitizedPaths: TaintPath[];
}

export interface TaintPath {
  source: TaintSource;
  sink: TaintSink;
  nodes: DataFlowNode[];
  isSanitized: boolean;
  sanitizer?: string;
}
```

```typescript
// services/FixPipeline.ts
export interface IFixPipeline {
  generateFix(vulnerability: Vulnerability): Promise<Fix[]>;
  verifyFix(fix: Fix): Promise<VerificationResult>;
  applyFix(fix: Fix, dryRun?: boolean): Promise<ApplyResult>;
}

export interface Fix {
  id: string;
  vulnerabilityId: string;
  type: 'llm-generated' | 'template-based';
  code: string;
  location: SourceLocation;
  confidence: number;
  explanation: string;
}

export interface VerificationResult {
  isValid: boolean;
  eliminatesVulnerability: boolean;
  introducesNewVulnerabilities: boolean;
  preservesFunctionality: boolean;
  z3ProofStatus: 'proved' | 'disproved' | 'unknown';
  details: string;
}
```

### 5.3 VS Code LM Client

```typescript
// infrastructure/VSCodeLMClient.ts
import * as vscode from 'vscode';

export interface ILMClient {
  generateFix(context: FixContext): Promise<string>;
  isAvailable(): Promise<boolean>;
}

export class VSCodeLMClient implements ILMClient {
  private model: vscode.LanguageModelChat | null = null;

  async initialize(): Promise<void> {
    const models = await vscode.lm.selectChatModels({
      vendor: 'copilot',
      family: 'gpt-4'
    });
    this.model = models[0] ?? null;
  }

  async isAvailable(): Promise<boolean> {
    return this.model !== null;
  }

  async generateFix(context: FixContext): Promise<string> {
    if (!this.model) {
      throw new Error('LM API not available');
    }

    const messages = [
      vscode.LanguageModelChatMessage.User(
        this.buildPrompt(context)
      )
    ];

    const response = await this.model.sendRequest(
      messages,
      {},
      new vscode.CancellationTokenSource().token
    );

    let result = '';
    for await (const chunk of response.text) {
      result += chunk;
    }
    return this.extractCode(result);
  }

  private buildPrompt(context: FixContext): string {
    return `Fix the following security vulnerability:
Type: ${context.vulnerability.type}
CWE: ${context.vulnerability.cwes.join(', ')}
Description: ${context.vulnerability.description}

Original code:
\`\`\`typescript
${context.originalCode}
\`\`\`

Provide a secure fix that:
1. Eliminates the vulnerability
2. Preserves original functionality
3. Follows TypeScript best practices

Return ONLY the fixed code without explanation.`;
  }

  private extractCode(response: string): string {
    // Extract code block from LLM response
    const codeBlockRegex = /```(?:typescript|ts)?\n([\s\S]*?)```/;
    const match = response.match(codeBlockRegex);
    if (match && match[1]) {
      return match[1].trim();
    }
    // If no code block, assume entire response is code
    return response.trim();
  }
}
```

---

## 6. ディレクトリ構造

```
packages/security/
├── package.json
├── tsconfig.json
├── vitest.config.ts
├── README.md
├── src/
│   ├── index.ts                      # Public API exports
│   ├── types/
│   │   ├── vulnerability.ts          # Vulnerability, SourceLocation
│   │   ├── taint.ts                  # TaintSource, TaintSink, TaintPath
│   │   ├── fix.ts                    # Fix, VerificationResult
│   │   ├── secret.ts                 # Secret, SecretPattern
│   │   ├── dependency.ts             # AuditResult, VulnerableDep
│   │   └── config.ts                 # SecurityConfig
│   ├── services/
│   │   ├── VulnerabilityScanner.ts   # DES-SEC-SCAN-*
│   │   ├── TaintAnalyzer.ts          # DES-SEC-TAINT-*
│   │   ├── FixPipeline.ts            # DES-SEC-FIX-*
│   │   ├── SecretsDetector.ts        # DES-SEC-SECRET-*
│   │   ├── DependencyAuditor.ts      # DES-SEC-DEPS-*
│   │   └── ComplianceChecker.ts      # DES-SEC-COMP-*
│   ├── analysis/
│   │   ├── AnalysisEngine.ts         # AST/CFG/DFG builder
│   │   ├── DataFlowGraph.ts          # DFG implementation
│   │   ├── SourceDetector.ts         # Taint source detection
│   │   ├── SinkDetector.ts           # Taint sink detection
│   │   └── SanitizerRegistry.ts      # Sanitizer management
│   ├── fix/
│   │   ├── FixGenerator.ts           # Fix generation orchestrator
│   │   ├── LLMFixProvider.ts         # VS Code LM integration
│   │   ├── TemplateProvider.ts       # Template-based fixes
│   │   ├── FixVerifier.ts            # Fix verification
│   │   ├── Z3Verifier.ts             # Z3 SMT verification
│   │   └── SemanticAnalyzer.ts       # Functionality preservation
│   ├── secrets/
│   │   ├── PatternMatcher.ts         # Known pattern detection
│   │   ├── EntropyAnalyzer.ts        # Entropy-based detection
│   │   └── ContextAnalyzer.ts        # False positive reduction
│   ├── deps/
│   │   ├── NVDClient.ts              # NVD API client
│   │   ├── GitHubAdvisoryClient.ts   # GitHub Advisory client
│   │   ├── TransitiveDependencyResolver.ts
│   │   └── UpgradeAdvisor.ts         # Safe version suggestion
│   ├── infrastructure/
│   │   ├── RuleEngine.ts             # YAML rule loader
│   │   ├── VSCodeLMClient.ts         # VS Code LM API client
│   │   ├── YataSecurityAdapter.ts    # YATA integration
│   │   ├── CacheManager.ts           # API response caching
│   │   ├── ConfigLoader.ts           # Config file loader
│   │   └── ErrorHandler.ts           # Error handling
│   ├── cli/
│   │   ├── index.ts                  # CLI entry point
│   │   ├── commands/
│   │   │   ├── scan.ts
│   │   │   ├── fix.ts
│   │   │   ├── audit-deps.ts
│   │   │   ├── detect-secrets.ts
│   │   │   └── compliance.ts
│   │   └── formatters/
│   │       ├── json.ts
│   │       ├── sarif.ts
│   │       └── table.ts
│   └── mcp/
│       ├── index.ts                  # MCP tools registration
│       └── tools/
│           ├── security_scan.ts
│           ├── security_fix.ts
│           ├── security_audit_deps.ts
│           ├── security_detect_secrets.ts
│           └── security_compliance.ts
├── rules/
│   ├── owasp-top-10.yaml             # OWASP Top 10 rules
│   ├── cwe-top-25.yaml               # CWE Top 25 rules
│   ├── secrets-patterns.yaml         # Secret detection patterns
│   └── custom/                       # User custom rules
├── templates/
│   ├── fixes/                        # Template-based fix patterns
│   │   ├── sql-injection.ts
│   │   ├── xss.ts
│   │   ├── path-traversal.ts
│   │   └── command-injection.ts
│   └── reports/
│       ├── compliance.html
│       └── vulnerability.html
└── tests/
    ├── unit/
    │   ├── services/
    │   ├── analysis/
    │   ├── fix/
    │   ├── secrets/
    │   └── deps/
    ├── integration/
    │   ├── scan.test.ts
    │   ├── fix.test.ts
    │   └── e2e.test.ts
    └── fixtures/
        ├── vulnerable-code/
        ├── safe-code/
        └── package-jsons/
```

---

## 7. テスト戦略（憲法III条準拠）

### 7.1 テストピラミッド

```
                    ┌─────────────────────────┐
                    │      E2E Tests        │  <- 5%
                    │  (Full scan workflow) │
                    ├─────────────────────────┤
                    │   Integration Tests   │  <- 20%
                    │ (Scanner + Analyzer)  │
                    ├─────────────────────────┤
                    │      Unit Tests       │  <- 75%
                    │ (Individual functions)│
                    └─────────────────────────┘
```

### 7.2 テストカテゴリ

| カテゴリ | 対象 | 目標カバレッジ |
|---------|------|------------|
| **Unit** | 各コンポーネントの関数 | >90% |
| **Integration** | サービス間連携 | >80% |
| **E2E** | CLI/MCPフルワークフロー | 主要パス |
| **Security** | OWASP/CWE検出精度 | 検出率>90% |

### 7.3 テストフィクスチャ

```typescript
// tests/fixtures/vulnerable-code/sql-injection.ts
export const sqlInjectionExamples = {
  // CWE-89: SQL Injection
  vulnerable: `
    const query = "SELECT * FROM users WHERE id = " + userId;
    db.query(query);
  `,
  fixed: `
    const query = "SELECT * FROM users WHERE id = ?";
    db.query(query, [userId]);
  `,
  cwes: ['CWE-89'],
  owasp: 'A03:2021'
};
```

### 7.4 Red-Green-Blueサイクル

```bash
# 1. Red: 失敗するテストを書く
vitest run tests/unit/services/VulnerabilityScanner.test.ts
# ✗ should detect SQL injection vulnerability

# 2. Green: 最小限のコードでパスさせる
vitest run tests/unit/services/VulnerabilityScanner.test.ts
# ✓ should detect SQL injection vulnerability

# 3. Blue: リファクタリング
vitest run --coverage
```

---

## 8. キャッシュ設計

### 8.1 キャッシュ対象

| データ | TTL | ストレージ |
|------|-----|----------|
| NVD CVEデータ | 24時間 | SQLite |
| GitHub Advisory | 6時間 | SQLite |
| ASTパース結果 | ファイル変更まで | メモリ |
| ルールマッチ結果 | ファイル変更まで | メモリ |

### 8.2 CacheManager実装

```typescript
// infrastructure/CacheManager.ts
export interface ICacheManager {
  get<T>(key: string): Promise<T | null>;
  set<T>(key: string, value: T, ttlSeconds?: number): Promise<void>;
  invalidate(pattern: string): Promise<void>;
}

export class CacheManager implements ICacheManager {
  private memoryCache: Map<string, CacheEntry> = new Map();
  private db: Database; // SQLite for persistent cache

  async get<T>(key: string): Promise<T | null> {
    // Check memory cache first
    const memEntry = this.memoryCache.get(key);
    if (memEntry && !this.isExpired(memEntry)) {
      return memEntry.value as T;
    }

    // Check SQLite cache
    const dbEntry = await this.db.get(
      'SELECT value, expires_at FROM cache WHERE key = ?',
      [key]
    );
    if (dbEntry && new Date(dbEntry.expires_at) > new Date()) {
      const value = JSON.parse(dbEntry.value);
      this.memoryCache.set(key, { value, expiresAt: new Date(dbEntry.expires_at) });
      return value as T;
    }

    return null;
  }

  async set<T>(key: string, value: T, ttlSeconds = 3600): Promise<void> {
    const expiresAt = new Date(Date.now() + ttlSeconds * 1000);
    
    // Memory cache
    this.memoryCache.set(key, { value, expiresAt });
    
    // SQLite cache (persistent)
    await this.db.run(
      'INSERT OR REPLACE INTO cache (key, value, expires_at) VALUES (?, ?, ?)',
      [key, JSON.stringify(value), expiresAt.toISOString()]
    );
  }
}
```

---

## 9. 設定ファイル仕様

### 9.1 設定ファイル名

- `.musubix-security.yaml` (プロジェクトルート)
- `.musubix-security.yml` (別名)
- `musubix-security.config.js` (JavaScript形式)

### 9.2 設定スキーマ

```yaml
# .musubix-security.yaml
version: "1.0"

# スキャン設定
scan:
  # 有効なルールセット
  rulesets:
    - owasp-top-10
    - cwe-top-25
    # - custom/my-rules.yaml
  
  # 重大度フィルタ
  severity:
    - critical
    - high
    - medium
    # - low
  
  # 除外パターン
  exclude:
    - "**/node_modules/**"
    - "**/*.test.ts"
    - "**/*.spec.ts"
    - "**/dist/**"
  
  # 最大ファイルサイズ (bytes)
  maxFileSize: 1048576  # 1MB

# テイント分析設定
taint:
  # カスタムソース
  sources:
    - pattern: "customInput"
      type: "user-input"
  
  # カスタムサニタイザー
  sanitizers:
    - name: "myEscape"
      vulnerabilities: ["xss"]

# 自動修正設定
fix:
  # LLM使用設定
  llm:
    enabled: true
    model: "copilot"  # copilot | claude | gemini
    maxCandidates: 3
  
  # 自動適用
  autoApply: false
  
  # ドライランデフォルト
  dryRun: true

# シークレット検出設定
secrets:
  # エントロピー閾値
  entropyThreshold: 4.5
  
  # 追加パターン
  patterns:
    - name: "internal-api-key"
      regex: "INTERNAL_[A-Z0-9]{32}"
  
  # 無視パターン
  ignore:
    - "**/*.example"
    - "**/.env.template"

# 依存関係監査設定
dependencies:
  # 推移的依存関係の深さ
  maxDepth: 10
  
  # 無視する脆弱性
  ignore:
    - "CVE-2020-12345"  # Known false positive

# レポート設定
report:
  format: "sarif"  # json | sarif | html | table
  output: "./security-report"

# キャッシュ設定
cache:
  enabled: true
  ttl:
    nvd: 86400      # 24 hours
    github: 21600   # 6 hours
```

### 9.3 ConfigLoader実装

```typescript
// infrastructure/ConfigLoader.ts
import { cosmiconfig } from 'cosmiconfig';
import { z } from 'zod';

const SecurityConfigSchema = z.object({
  version: z.string().default('1.0'),
  scan: z.object({
    rulesets: z.array(z.string()).default(['owasp-top-10', 'cwe-top-25']),
    severity: z.array(z.enum(['critical', 'high', 'medium', 'low'])).default(['critical', 'high']),
    exclude: z.array(z.string()).default(['**/node_modules/**']),
    maxFileSize: z.number().default(1048576),
  }).default({}),
  // ... other schemas
});

export type SecurityConfig = z.infer<typeof SecurityConfigSchema>;

export class ConfigLoader {
  async load(searchFrom?: string): Promise<SecurityConfig> {
    const explorer = cosmiconfig('musubix-security', {
      searchPlaces: [
        '.musubix-security.yaml',
        '.musubix-security.yml',
        'musubix-security.config.js',
      ],
    });

    const result = await explorer.search(searchFrom);
    const config = result?.config ?? {};
    
    return SecurityConfigSchema.parse(config);
  }
}
```

---

## 10. データフロー

### 10.1 脆弱性スキャンフロー

```
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│  Source  │───▶│  Parser  │───▶│   AST    │───▶│  Rule    │
│  Files   │    │ (ts-morph)│   │          │    │  Engine  │
└──────────┘    └──────────┘    └──────────┘    └────┬─────┘
                                                      │
                    ┌─────────────────────────────────┘
                    │
                    ▼
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│  Taint   │◀───│ Pattern  │◀───│ OWASP/   │◀───│  Rules   │
│ Analyzer │    │  Match   │    │ CWE Rules│    │  (YAML)  │
└────┬─────┘    └──────────┘    └──────────┘    └──────────┘
     │
     ▼
┌──────────────────────────────────────────────────────────┐
│                    Vulnerability Report                  │
│  { id, type, severity, location, description, cwes }    │
└──────────────────────────────────────────────────────────┘
```

### 10.2 自動修正フロー

```
┌─────────────┐
│Vulnerability│
└──────┬──────┘
       │
       ▼
┌──────────────────────────────────────────────────────────┐
│                    Fix Generator                         │
│  ┌────────────────┐    ┌────────────────┐              │
│  │  LLM Provider  │ OR │ Template Provider│              │
│  │  (VS Code LM)  │    │   (Fallback)   │              │
│  └───────┬────────┘    └───────┬────────┘              │
│          └──────────┬──────────┘                        │
└─────────────────────┼────────────────────────────────────┘
                      │
                      ▼
┌──────────────────────────────────────────────────────────┐
│                    Fix Verifier                          │
│  ┌────────────────┐  ┌────────────────┐                │
│  │   Z3 Verifier  │  │Semantic Analyzer│                │
│  │ (Vulnerability │  │  (Functionality │                │
│  │  Elimination)  │  │   Preservation) │                │
│  └───────┬────────┘  └───────┬────────┘                │
│          └──────────┬────────┘                          │
└─────────────────────┼────────────────────────────────────┘
                      │
                      ▼
              ┌───────────────┐
              │  Verified Fix │
              │ (confidence,  │
              │  z3proof)     │
              └───────────────┘
```

---

## 11. 依存関係

### 11.1 パッケージ依存関係

```json
{
  "dependencies": {
    "@nahisaho/musubix-core": "^1.7.5",
    "@nahisaho/musubix-formal-verify": "^1.7.5",
    "@nahisaho/yata-local": "^1.7.5",
    "ts-morph": "^22.0.0",
    "commander": "^12.0.0",
    "yaml": "^2.4.0"
  },
  "peerDependencies": {
    "vscode": "^1.85.0"
  },
  "devDependencies": {
    "vitest": "^2.0.0",
    "typescript": "^5.4.0"
  }
}
```

### 11.2 内部依存関係

```
┌─────────────────────────────────────────────────────────┐
│                    CLI / MCP Layer                      │
└────────────────────────┬────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────┐
│                    Core Services                        │
│  VulnerabilityScanner ─┬─ TaintAnalyzer               │
│                        └─ FixPipeline                  │
│  SecretsDetector ──────── DependencyAuditor           │
│                        └─ ComplianceChecker            │
└────────────────────────┬────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────┐
│                   Infrastructure                        │
│  RuleEngine ───── AnalysisEngine ───── LMClient        │
│  YataAdapter ──── ErrorHandler                         │
└─────────────────────────────────────────────────────────┘
```

---

## 12. エラーハンドリング

### 12.1 エラー分類

| エラー種別 | コード範囲 | 例 |
|-----------|-----------|-----|
| **Analysis** | SEC-1xxx | SEC-1001: Parse error |
| **Scan** | SEC-2xxx | SEC-2001: Rule load failed |
| **Fix** | SEC-3xxx | SEC-3001: LLM unavailable |
| **Verification** | SEC-4xxx | SEC-4001: Z3 timeout |
| **External** | SEC-5xxx | SEC-5001: NVD unreachable |

### 12.2 グレースフルデグラデーション

```typescript
// DES-SEC-ERR-001: Graceful degradation
export class SecurityService {
  async scan(files: string[]): Promise<ScanResult> {
    const result = await this.scanner.scan(files);
    
    // LLM非可用時はテンプレートベース修正にフォールバック
    if (result.vulnerabilities.length > 0) {
      const fixes = await this.generateFixes(result.vulnerabilities);
      result.fixes = fixes;
    }
    
    return result;
  }

  private async generateFixes(vulns: Vulnerability[]): Promise<Fix[]> {
    if (await this.lmClient.isAvailable()) {
      return this.fixPipeline.generateWithLLM(vulns);
    } else {
      // DES-SEC-FIX-006: Template-based fallback
      console.warn('[SEC-3001] LLM unavailable, using template-based fixes');
      return this.fixPipeline.generateFromTemplates(vulns);
    }
  }
}
```

---

## 13. 設計決定記録（ADR）

### ADR-SEC-001: VS Code LM API採用

**ステータス**: 承認  
**コンテキスト**: LLM統合方式の選定  
**決定**: OpenAI/Anthropic直接ではなくVS Code Language Model APIを採用  
**理由**:
- ユーザーの既存サブスクリプション活用
- 認証・課金の一元管理
- 複数モデル（Copilot, Claude, Gemini）対応
**トレース**: REQ-SEC-FIX-001

### ADR-SEC-002: Z3 Wasm版優先

**ステータス**: 承認  
**コンテキスト**: Z3ソルバのデプロイ方式  
**決定**: Native版よりWasm版を優先  
**理由**:
- クロスプラットフォーム互換性
- インストール不要
- npm依存のみで完結
**トレース**: REQ-SEC-FIX-002

### ADR-SEC-003: YAMLベースルール定義

**ステータス**: 承認  
**コンテキスト**: セキュリティルールの定義形式  
**決定**: TypeScriptコードではなくYAMLでルール定義  
**理由**:
- 非開発者でもルール追加可能
- 外部ルールセットの取り込みが容易
- バージョン管理が明確
**トレース**: REQ-SEC-SCAN-002, 003

---

## 14. トレーサビリティマトリクス（設計→要件）

| 設計ID | 要件ID | コンポーネント |
|--------|--------|--------------|
| DES-SEC-SCAN-001 | REQ-SEC-SCAN-001 | VulnerabilityScanner |
| DES-SEC-SCAN-002 | REQ-SEC-SCAN-002 | OWASPScanner |
| DES-SEC-SCAN-003 | REQ-SEC-SCAN-003 | CWEScanner |
| DES-SEC-SCAN-004 | REQ-SEC-SCAN-004 | ScanOptions.severityFilter |
| DES-SEC-SCAN-005 | REQ-SEC-SCAN-005 | IncrementalScanner |
| DES-SEC-SCAN-006 | REQ-SEC-SCAN-006 | RuleEngine.confidence |
| DES-SEC-TAINT-001 | REQ-SEC-TAINT-001 | SourceDetector |
| DES-SEC-TAINT-002 | REQ-SEC-TAINT-002 | SinkDetector |
| DES-SEC-TAINT-003 | REQ-SEC-TAINT-003 | DataFlowGraph |
| DES-SEC-TAINT-004 | REQ-SEC-TAINT-004 | SanitizerRegistry |
| DES-SEC-FIX-001 | REQ-SEC-FIX-001 | FixGenerator |
| DES-SEC-FIX-002 | REQ-SEC-FIX-002 | Z3Verifier |
| DES-SEC-FIX-003 | REQ-SEC-FIX-003 | VerificationEngine |
| DES-SEC-FIX-004 | REQ-SEC-FIX-004 | SemanticAnalyzer |
| DES-SEC-FIX-005 | REQ-SEC-FIX-005 | FixGenerator.rankCandidates |
| DES-SEC-FIX-006 | REQ-SEC-FIX-006 | TemplateProvider |
| DES-SEC-SECRET-001 | REQ-SEC-SECRET-001 | SecretsDetector |
| DES-SEC-SECRET-002 | REQ-SEC-SECRET-002 | EntropyAnalyzer |
| DES-SEC-SECRET-003 | REQ-SEC-SECRET-003 | PatternMatcher |
| DES-SEC-DEPS-001 | REQ-SEC-DEPS-001 | DependencyAuditor |
| DES-SEC-DEPS-002 | REQ-SEC-DEPS-002 | TransitiveDependencyResolver |
| DES-SEC-DEPS-003 | REQ-SEC-DEPS-003 | UpgradeAdvisor |
| DES-SEC-COMP-001 | REQ-SEC-COMP-001 | ReportGenerator |
| DES-SEC-COMP-002 | REQ-SEC-COMP-002 | ASVSChecker |
| DES-SEC-YATA-001 | REQ-SEC-YATA-001 | YataSecurityAdapter |
| DES-SEC-YATA-002 | REQ-SEC-YATA-002 | FixPatternLearner |
| DES-SEC-MCP-001 | REQ-SEC-MCP-001 | McpSecurityTools.scan |
| DES-SEC-MCP-002 | REQ-SEC-MCP-002 | McpSecurityTools.fix |
| DES-SEC-CLI-001 | REQ-SEC-CLI-001 | cli/security.ts |
| DES-SEC-CLI-002 | REQ-SEC-CLI-002 | cli/security.ts --help |
| DES-SEC-CLI-003 | REQ-SEC-CLI-003 | cli/security.ts exit codes |
| DES-SEC-ERR-001 | REQ-SEC-ERR-001 | ErrorHandler.degrade |
| DES-SEC-ERR-002 | REQ-SEC-ERR-002 | ErrorHandler.format |
| DES-SEC-PERF-001 | REQ-SEC-PERF-001 | AnalysisEngine |
| DES-SEC-PERF-002 | REQ-SEC-PERF-002 | MemoryManager |
| DES-SEC-REL-001 | REQ-SEC-REL-001 | RuleEngine |
| DES-SEC-REL-002 | REQ-SEC-REL-002 | FixPipeline |
| DES-SEC-AVAIL-001 | REQ-SEC-AVAIL-001 | OfflineMode |

---

## 15. レビュー履歴

| バージョン | 日付 | レビュアー | ステータス | コメント |
|-----------|------|-----------|----------|--------|
| 0.1.0 | 2026-01-06 | - | 📝 レビュー待ち | 初版作成 |
| 0.2.0 | 2026-01-06 | AI Agent (Constitution Enforcer) | ✅ 合格 | ディレクトリ構造追加、テスト戦略追加、キャッシュ設計追加、設定ファイル仕様追加 |

---

## 16. 承認

| 役割 | 名前 | 署名 | 日付 |
|------|------|------|------|
| 作成者 | AI Agent | ✅ | 2026-01-06 |
| レビュアー | AI Agent (Constitution Enforcer) | ✅ | 2026-01-06 |
| 承認者 | - | ⏳ | - |

---

**© 2026 MUSUBIX Project**
