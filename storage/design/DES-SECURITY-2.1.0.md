# MUSUBIX Security v2.1.0 設計書

**ドキュメントID**: DES-SECURITY-2.1.0  
**バージョン**: 1.0.0  
**作成日**: 2026-01-08  
**ステータス**: Draft  
**関連要件**: REQ-SECURITY-2.1.0

---

## 1. 概要

### 1.1 設計目標

`@nahisaho/musubix-security` v2.1.0 の設計目標：

1. **拡張性**: 新しいルール・検出器を容易に追加可能
2. **パフォーマンス**: インクリメンタル解析、並列処理
3. **統合性**: DFG、Z3、YATA との密な連携
4. **Neuro-Symbolic**: LLM生成 + Z3検証のハイブリッドアプローチ

### 1.2 設計原則

| 原則 | 適用 |
|------|------|
| **Single Responsibility** | 各クラスは1つの責務のみ |
| **Open/Closed** | ルール・検出器はプラグイン形式 |
| **Dependency Inversion** | インターフェース経由で依存 |
| **Strategy Pattern** | LLMプロバイダー切り替え |
| **Chain of Responsibility** | 検証パイプライン |

---

## 2. C4モデル

### 2.1 Context Diagram (Level 1)

```
┌─────────────────────────────────────────────────────────────────────┐
│                         External Systems                             │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│   ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐     │
│   │   NVD    │    │ VS Code  │    │  Ollama  │    │  GitHub  │     │
│   │   API    │    │  LM API  │    │  (Local) │    │ Advisory │     │
│   └────┬─────┘    └────┬─────┘    └────┬─────┘    └────┬─────┘     │
│        │               │               │               │            │
└────────┼───────────────┼───────────────┼───────────────┼────────────┘
         │               │               │               │
         ▼               ▼               ▼               ▼
┌─────────────────────────────────────────────────────────────────────┐
│                                                                      │
│                    MUSUBIX Security v2.1.0                          │
│                                                                      │
│   ┌─────────────────────────────────────────────────────────────┐   │
│   │  Vulnerability Scanner │ Taint Analyzer │ CVE Database     │   │
│   │  Rule Engine          │ Fix Generator  │ Fix Verifier      │   │
│   └─────────────────────────────────────────────────────────────┘   │
│                                                                      │
└──────────────────────────────┬──────────────────────────────────────┘
                               │
         ┌─────────────────────┼─────────────────────┐
         │                     │                     │
         ▼                     ▼                     ▼
┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐
│  musubix-dfg    │  │ musubix-formal  │  │   yata-local    │
│  (Data Flow)    │  │   (Z3 Verify)   │  │ (Knowledge DB)  │
└─────────────────┘  └─────────────────┘  └─────────────────┘
```

### 2.2 Container Diagram (Level 2)

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      @nahisaho/musubix-security                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │                         Core Layer                                  │ │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐             │ │
│  │  │SecurityScanner│  │ RuleEngine  │  │ TaintAnalyzer │             │ │
│  │  │   [Entry]    │  │  [Rules]    │  │   [DFA]      │             │ │
│  │  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘             │ │
│  │         │                 │                 │                      │ │
│  └─────────┼─────────────────┼─────────────────┼──────────────────────┘ │
│            │                 │                 │                        │
│  ┌─────────┼─────────────────┼─────────────────┼──────────────────────┐ │
│  │         ▼                 ▼                 ▼    Intelligence       │ │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐             │ │
│  │  │ CVEDatabase  │  │RiskScorer   │  │ThreatIntel   │             │ │
│  │  │   [NVD]     │  │  [CVSS]     │  │  [Patterns]  │             │ │
│  │  └──────────────┘  └──────────────┘  └──────────────┘             │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │                       Remediation Layer                             │ │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐             │ │
│  │  │ FixGenerator │  │ FixVerifier │  │ FixApplier  │             │ │
│  │  │   [LLM]     │──▶│   [Z3]      │──▶│  [Apply]    │             │ │
│  │  └──────────────┘  └──────────────┘  └──────────────┘             │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │                       Interface Layer                               │ │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐             │ │
│  │  │     CLI     │  │  MCP Tools  │  │    API       │             │ │
│  │  └──────────────┘  └──────────────┘  └──────────────┘             │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.3 Component Diagram (Level 3)

#### 2.3.1 Core Layer Components

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           Core Layer                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    SecurityScanner                               │    │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │    │
│  │  │ FileScanner │  │BatchScanner │  │IncrementalSc│             │    │
│  │  │             │  │             │  │anner       │             │    │
│  │  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘             │    │
│  │         └─────────────────┴─────────────────┘                   │    │
│  │                          │                                      │    │
│  │                          ▼                                      │    │
│  │                 ┌─────────────────┐                             │    │
│  │                 │ ScanCoordinator │                             │    │
│  │                 └────────┬────────┘                             │    │
│  └──────────────────────────┼──────────────────────────────────────┘    │
│                             │                                            │
│  ┌──────────────────────────┼──────────────────────────────────────┐    │
│  │                          ▼         RuleEngine                    │    │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │    │
│  │  │ RuleLoader  │  │RuleRegistry │  │RuleMatcher  │             │    │
│  │  │  [YAML]     │  │             │  │  [AST]      │             │    │
│  │  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘             │    │
│  │         │                │                │                     │    │
│  │         ▼                ▼                ▼                     │    │
│  │  ┌─────────────────────────────────────────────────────────┐   │    │
│  │  │                    Rule Categories                       │   │    │
│  │  │ ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐        │   │    │
│  │  │ │Injection│ │ AuthN/Z │ │Crypto   │ │Config   │        │   │    │
│  │  │ │ Rules   │ │ Rules   │ │ Rules   │ │ Rules   │        │   │    │
│  │  │ └─────────┘ └─────────┘ └─────────┘ └─────────┘        │   │    │
│  │  └─────────────────────────────────────────────────────────┘   │    │
│  └────────────────────────────────────────────────────────────────┘    │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────┐    │
│  │                      TaintAnalyzer                              │    │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │    │
│  │  │SourceFinder │  │FlowTracer   │  │ SinkChecker │             │    │
│  │  │             │  │             │  │             │             │    │
│  │  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘             │    │
│  │         │                │                │                     │    │
│  │         ▼                ▼                ▼                     │    │
│  │  ┌─────────────────────────────────────────────────────────┐   │    │
│  │  │              InterproceduralAnalyzer                     │   │    │
│  │  │  ┌───────────────┐  ┌───────────────┐                   │   │    │
│  │  │  │ CallGraphBuilder│  │TaintPropagator│                   │   │    │
│  │  │  └───────────────┘  └───────────────┘                   │   │    │
│  │  └─────────────────────────────────────────────────────────┘   │    │
│  │                          │                                      │    │
│  │                          ▼                                      │    │
│  │                 ┌─────────────────┐                             │    │
│  │                 │  DFG Adapter    │ ←── @nahisaho/musubix-dfg   │    │
│  │                 └─────────────────┘                             │    │
│  └────────────────────────────────────────────────────────────────┘    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

#### 2.3.2 Intelligence Layer Components

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        Intelligence Layer                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────┐    │
│  │                      CVEDatabase                                │    │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │    │
│  │  │ NVDClient   │  │ LocalCache  │  │CVEMatcher   │             │    │
│  │  │  [HTTP]     │  │ [SQLite]    │  │ [semver]    │             │    │
│  │  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘             │    │
│  │         │                │                │                     │    │
│  │         ▼                ▼                ▼                     │    │
│  │  ┌─────────────────────────────────────────────────────────┐   │    │
│  │  │                    CVESyncService                        │   │    │
│  │  │  - Incremental sync                                      │   │    │
│  │  │  - Rate limiting (5 req/30s)                             │   │    │
│  │  │  - Retry with exponential backoff                        │   │    │
│  │  └─────────────────────────────────────────────────────────┘   │    │
│  └────────────────────────────────────────────────────────────────┘    │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────┐    │
│  │                      RiskScorer                                 │    │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │    │
│  │  │CVSSCalculator│ │ContextScorer│  │PriorityRanker│             │    │
│  │  │   [v3.1]    │  │             │  │             │             │    │
│  │  └─────────────┘  └─────────────┘  └─────────────┘             │    │
│  └────────────────────────────────────────────────────────────────┘    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

#### 2.3.3 Remediation Layer Components

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        Remediation Layer                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────┐    │
│  │                      FixGenerator                               │    │
│  │                                                                  │    │
│  │  ┌─────────────────────────────────────────────────────────┐   │    │
│  │  │                 LLMProviderRegistry                      │   │    │
│  │  │  ┌───────────┐ ┌───────────┐ ┌───────────┐ ┌─────────┐ │   │    │
│  │  │  │ VSCodeLM  │ │  Ollama   │ │  OpenAI   │ │Pattern  │ │   │    │
│  │  │  │ Provider  │ │ Provider  │ │ Provider  │ │Fallback │ │   │    │
│  │  │  │ [Priority]│ │           │ │           │ │         │ │   │    │
│  │  │  └─────┬─────┘ └─────┬─────┘ └─────┬─────┘ └────┬────┘ │   │    │
│  │  │        │             │             │            │       │   │    │
│  │  │        └─────────────┴──────┬──────┴────────────┘       │   │    │
│  │  │                             │                            │   │    │
│  │  │                             ▼                            │   │    │
│  │  │                    ┌─────────────────┐                  │   │    │
│  │  │                    │ FixPromptBuilder│                  │   │    │
│  │  │                    └─────────────────┘                  │   │    │
│  │  └─────────────────────────────────────────────────────────┘   │    │
│  └────────────────────────────────────────────────────────────────┘    │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────┐    │
│  │                      FixVerifier                                │    │
│  │                                                                  │    │
│  │  ┌─────────────────────────────────────────────────────────┐   │    │
│  │  │                 Verification Pipeline                    │   │    │
│  │  │                                                          │   │    │
│  │  │  ┌───────────┐   ┌───────────┐   ┌───────────┐         │   │    │
│  │  │  │  Syntax   │──▶│  Taint    │──▶│    Z3     │         │   │    │
│  │  │  │  Check    │   │  Recheck  │   │  Verify   │         │   │    │
│  │  │  └───────────┘   └───────────┘   └─────┬─────┘         │   │    │
│  │  │                                        │                │   │    │
│  │  │                                        ▼                │   │    │
│  │  │                               ┌─────────────────┐       │   │    │
│  │  │                               │ Z3 SMT Adapter  │       │   │    │
│  │  │                               │ (formal-verify) │       │   │    │
│  │  │                               └─────────────────┘       │   │    │
│  │  └─────────────────────────────────────────────────────────┘   │    │
│  └────────────────────────────────────────────────────────────────┘    │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────┐    │
│  │                      FixApplier                                 │    │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │    │
│  │  │BackupManager│  │ CodePatcher │  │TestRunner   │             │    │
│  │  │   [git]     │  │             │  │ [optional]  │             │    │
│  │  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘             │    │
│  │         │                │                │                     │    │
│  │         ▼                ▼                ▼                     │    │
│  │  ┌─────────────────────────────────────────────────────────┐   │    │
│  │  │                 RollbackManager                          │   │    │
│  │  └─────────────────────────────────────────────────────────┘   │    │
│  └────────────────────────────────────────────────────────────────┘    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 3. 詳細設計

### 3.1 ディレクトリ構造

```
packages/security/src/
├── index.ts                      # Public API exports
├── types/
│   ├── index.ts
│   ├── vulnerability.ts          # Vulnerability types
│   ├── taint.ts                  # Taint analysis types
│   ├── cve.ts                    # CVE/NVD types
│   ├── rule.ts                   # Rule definition types
│   └── fix.ts                    # Fix types
├── core/
│   ├── security-scanner.ts       # Main scanner entry
│   ├── scan-coordinator.ts       # Orchestrates scanning
│   └── scan-result.ts           # Result aggregation
├── analysis/
│   ├── taint-analyzer.ts         # Enhanced taint analysis
│   ├── interprocedural/
│   │   ├── call-graph-builder.ts
│   │   ├── taint-propagator.ts
│   │   └── context-sensitivity.ts
│   ├── sources/
│   │   ├── source-registry.ts
│   │   └── builtin-sources.ts
│   ├── sinks/
│   │   ├── sink-registry.ts
│   │   └── builtin-sinks.ts
│   ├── sanitizers/
│   │   ├── sanitizer-registry.ts
│   │   └── builtin-sanitizers.ts
│   └── dfg-adapter.ts           # DFG package integration
├── rules/
│   ├── rule-engine.ts           # Rule execution engine
│   ├── rule-loader.ts           # YAML rule loader
│   ├── rule-registry.ts         # Rule registration
│   ├── rule-matcher.ts          # AST pattern matching
│   ├── owasp/
│   │   ├── index.ts
│   │   ├── a01-broken-access.yaml
│   │   ├── a02-crypto-failures.yaml
│   │   ├── a03-injection.yaml
│   │   ├── a04-insecure-design.yaml
│   │   ├── a05-misconfiguration.yaml
│   │   ├── a06-vulnerable-components.yaml
│   │   ├── a07-auth-failures.yaml
│   │   ├── a08-integrity-failures.yaml
│   │   ├── a09-logging-failures.yaml
│   │   └── a10-ssrf.yaml
│   └── cwe/
│       ├── index.ts
│       └── cwe-top-25.yaml
├── databases/
│   ├── cve-database.ts          # CVE database manager
│   ├── nvd-client.ts            # NVD API client
│   ├── local-cache.ts           # SQLite cache
│   ├── cve-matcher.ts           # Version matching
│   └── cpe-mapper.ts            # npm → CPE mapping
├── intelligence/
│   ├── risk-scorer.ts           # Risk assessment
│   ├── threat-intelligence.ts   # Threat intel
│   └── attack-pattern-matcher.ts
├── remediation/
│   ├── fix-generator.ts         # LLM fix generation
│   ├── fix-verifier.ts          # Z3 verification
│   ├── fix-applier.ts           # Fix application
│   ├── providers/
│   │   ├── provider-registry.ts
│   │   ├── vscode-lm-provider.ts
│   │   ├── ollama-provider.ts
│   │   ├── openai-provider.ts
│   │   └── pattern-fallback.ts
│   ├── prompts/
│   │   ├── fix-prompt-builder.ts
│   │   └── templates/
│   │       ├── sql-injection.md
│   │       ├── xss.md
│   │       └── ...
│   └── verification/
│       ├── syntax-checker.ts
│       ├── taint-rechecker.ts
│       └── z3-verifier.ts
├── cli/
│   ├── security-cli.ts
│   └── commands/
│       ├── scan.ts
│       ├── cve-check.ts
│       ├── fix.ts
│       └── report.ts
├── mcp/
│   ├── security-tools.ts
│   └── tool-handlers/
└── utils/
    ├── sarif-exporter.ts
    └── report-generator.ts
```

### 3.2 コアインターフェース

#### 3.2.1 SecurityScanner

```typescript
// DES-SEC-CORE-001: SecurityScanner Interface
// Trace: REQ-SEC-TAINT-001, REQ-SEC-RULES-001

interface ScanOptions {
  /** Target paths */
  paths: string[];
  /** Rule sets to enable */
  ruleSets: ('owasp-top-10' | 'cwe-top-25' | 'custom')[];
  /** Minimum severity to report */
  minSeverity: 'info' | 'low' | 'medium' | 'high' | 'critical';
  /** Enable interprocedural taint analysis */
  interprocedural: boolean;
  /** Include CVE check */
  checkCVE: boolean;
  /** Generate fixes */
  generateFixes: boolean;
  /** Maximum concurrent files */
  concurrency: number;
}

interface ScanResult {
  /** Scan metadata */
  metadata: ScanMetadata;
  /** Detected vulnerabilities */
  vulnerabilities: Vulnerability[];
  /** Taint paths found */
  taintPaths: TaintPath[];
  /** CVE findings */
  cveFindings: CVEFinding[];
  /** Generated fixes */
  fixes: FixCandidate[];
  /** Statistics */
  stats: ScanStatistics;
}

interface SecurityScanner {
  scan(options: ScanOptions): Promise<ScanResult>;
  scanFile(filePath: string, options?: Partial<ScanOptions>): Promise<ScanResult>;
  scanIncremental(changedFiles: string[]): Promise<ScanResult>;
}
```

#### 3.2.2 TaintAnalyzer

```typescript
// DES-SEC-TAINT-001: TaintAnalyzer Interface
// Trace: REQ-SEC-TAINT-001, REQ-SEC-TAINT-002, REQ-SEC-TAINT-003
// NOTE: 既存 types/taint.ts との整合性を維持

/**
 * Taint source category (既存実装と同期)
 * @see packages/security/src/types/taint.ts
 */
type TaintSourceCategory =
  | 'user-input'    // Form data, query params, request body
  | 'database'      // Database queries without sanitization
  | 'file-system'   // File reads
  | 'network'       // External API responses
  | 'environment'   // Environment variables
  | 'config'        // Configuration files
  | 'cli-args';     // Command line arguments

/**
 * Taint sink category (既存実装と同期)
 * @see packages/security/src/types/taint.ts
 */
type TaintSinkCategory =
  | 'sql-query'       // SQL execution (CWE-89)
  | 'nosql-query'     // NoSQL query
  | 'command-exec'    // OS command execution (CWE-78)
  | 'file-write'      // File system writes
  | 'file-read'       // File system reads - path traversal (CWE-22)
  | 'html-output'     // HTML rendering - XSS (CWE-79)
  | 'redirect'        // URL redirects (CWE-601)
  | 'eval'            // Code evaluation (CWE-94)
  | 'deserialization' // Object deserialization (CWE-502)
  | 'ldap-query'      // LDAP queries
  | 'xpath-query'     // XPath queries
  | 'http-request';   // Outbound HTTP requests - SSRF (CWE-918)

interface TaintSource {
  id: string;
  category: TaintSourceCategory;
  location: SourceLocation;
  variableName: string;
  expression: string;
  description: string;
  confidence: number;
}

interface TaintSink {
  id: string;
  category: TaintSinkCategory;
  location: SourceLocation;
  functionName: string;
  argumentIndex: number;
  expectedSanitizers: string[];
  description: string;
  severity: Severity;
}

/**
 * Sanitizer definition
 * @see BUILTIN_SANITIZERS in types/taint.ts for built-in definitions
 */
interface Sanitizer {
  name: string;
  package?: string;
  protects: TaintSinkCategory[];
  complete: boolean;
  notes?: string;
}

/**
 * Complete taint propagation path from source to sink
 * @see TaintPath in types/taint.ts
 */
interface TaintPath {
  id: string;
  source: TaintSource;
  sink: TaintSink;
  /** Steps in the propagation path (renamed from 'path' for clarity) */
  steps: TaintFlowStep[];
  /** Whether any sanitization was applied */
  sanitized: boolean;
  /** Overall path confidence */
  confidence: number;
  /** Path length (number of steps) */
  length: number;
}

/**
 * Taint flow step in the propagation path
 * @see TaintFlowStep in types/taint.ts
 */
interface TaintFlowStep {
  /** Step index in the path (0-based) */
  index: number;
  location: SourceLocation;
  expression: string;
  /** Variable name holding data at this step */
  variableName?: string;
  /** Type of operation */
  operation: 'assignment' | 'call' | 'return' | 'parameter' | 'property-access' | 'array-access';
  /** Whether sanitization was applied at this step */
  sanitized: boolean;
  /** Sanitizer function if sanitization was applied */
  sanitizer?: string;
}

/**
 * Taint analysis options
 * @see TaintAnalysisOptions in types/taint.ts
 */
interface TaintAnalyzerOptions {
  /** Enable interprocedural analysis */
  interprocedural: boolean;
  /** Max call depth for interprocedural */
  maxCallDepth: number;
  /** Context sensitivity level */
  contextSensitivity: 'none' | 'call-site' | 'object';
  /** Track through async/await boundaries */
  trackAsync: boolean;
  /** Custom source patterns */
  customSources?: {
    pattern: string;
    category: TaintSourceCategory;
    description: string;
  }[];
  /** Custom sink patterns */
  customSinks?: {
    pattern: string;
    category: TaintSinkCategory;
    severity: Severity;
    description: string;
  }[];
  /** Additional sanitizer functions to recognize */
  additionalSanitizers?: {
    functionName: string;
    sinkCategories: TaintSinkCategory[];
  }[];
  /** File patterns to exclude */
  excludePatterns?: string[];
}

interface TaintAnalyzer {
  analyze(files: string[], options?: TaintAnalyzerOptions): Promise<TaintPath[]>;
  analyzeFile(filePath: string): Promise<TaintPath[]>;
  registerSource(source: TaintSource): void;
  registerSink(sink: TaintSink): void;
  registerSanitizer(sanitizer: Sanitizer): void;
}
```

#### 3.2.3 CVEDatabase

```typescript
// DES-SEC-CVE-001: CVEDatabase Interface
// Trace: REQ-SEC-CVE-001, REQ-SEC-CVE-002, REQ-SEC-CVE-003

interface CVE {
  id: string;                    // CVE-YYYY-NNNNN
  description: string;
  published: Date;
  lastModified: Date;
  cvss: CVSSScore;
  cwe: string[];
  references: CVEReference[];
  affectedProducts: CPEMatch[];
}

interface CVSSScore {
  version: '3.0' | '3.1';
  baseScore: number;
  severity: 'none' | 'low' | 'medium' | 'high' | 'critical';
  vectorString: string;
  attackVector: string;
  attackComplexity: string;
  privilegesRequired: string;
  userInteraction: string;
  scope: string;
  confidentialityImpact: string;
  integrityImpact: string;
  availabilityImpact: string;
}

interface CPEMatch {
  cpe: string;
  versionStartIncluding?: string;
  versionStartExcluding?: string;
  versionEndIncluding?: string;
  versionEndExcluding?: string;
}

interface CVEFinding {
  cve: CVE;
  package: string;
  installedVersion: string;
  affectedRange: string;
  fixedVersion?: string;
  severity: string;
  recommendation: string;
}

interface CVEDatabaseOptions {
  /** NVD API key (optional, increases rate limit) */
  apiKey?: string;
  /** Cache directory */
  cacheDir: string;
  /** Cache TTL in hours */
  cacheTTL: number;
  /** Max cache size in MB */
  maxCacheSize: number;
}

interface CVEDatabase {
  /** Initialize and sync database */
  initialize(): Promise<void>;
  /** Sync with NVD */
  sync(options?: { full?: boolean }): Promise<SyncResult>;
  /** Get CVE by ID */
  getCVE(cveId: string): Promise<CVE | null>;
  /** Search CVEs */
  searchCVE(query: CVESearchQuery): Promise<CVE[]>;
  /** Check dependencies for CVEs */
  checkDependencies(packageJsonPath: string): Promise<CVEFinding[]>;
  /** Check specific package */
  checkPackage(name: string, version: string): Promise<CVEFinding[]>;
}
```

#### 3.2.4 RuleEngine

```typescript
// DES-SEC-RULES-001: RuleEngine Interface
// Trace: REQ-SEC-RULES-001, REQ-SEC-RULES-002, REQ-SEC-RULES-003

interface Rule {
  id: string;
  name: string;
  severity: 'info' | 'low' | 'medium' | 'high' | 'critical';
  cwe: string;
  owasp?: string;
  message: string;
  description: string;
  pattern: ASTPattern;
  fix?: FixTemplate;
  references: string[];
  tags: string[];
}

interface ASTPattern {
  type: string;
  properties?: Record<string, ASTPattern | string | boolean>;
  constraints?: PatternConstraint[];
}

interface PatternConstraint {
  type: 'tainted' | 'literal' | 'regex' | 'not';
  path: string;
  value?: string | RegExp;
}

interface FixTemplate {
  type: 'replace' | 'wrap' | 'parameterize' | 'custom';
  template: string;
  imports?: string[];
}

interface RuleMatch {
  rule: Rule;
  location: SourceLocation;
  matchedCode: string;
  context: MatchContext;
}

interface RuleEngine {
  /** Load rules from file/directory */
  loadRules(path: string): Promise<void>;
  /** Register a rule */
  registerRule(rule: Rule): void;
  /** Get all registered rules */
  getRules(filter?: RuleFilter): Rule[];
  /** Match rules against AST */
  match(ast: SourceFile, options?: MatchOptions): RuleMatch[];
  /** Enable/disable rule sets */
  enableRuleSet(name: string): void;
  disableRuleSet(name: string): void;
}
```

#### 3.2.5 FixGenerator & FixVerifier

```typescript
// DES-SEC-FIX-001: Fix Generation & Verification
// Trace: REQ-SEC-FIX-001, REQ-SEC-FIX-002, REQ-SEC-FIX-003

interface FixCandidate {
  id: string;
  vulnerability: Vulnerability;
  originalCode: string;
  fixedCode: string;
  explanation: string;
  confidence: number;
  provider: string;
  verified: boolean;
  verificationResult?: VerificationResult;
}

interface VerificationResult {
  passed: boolean;
  syntaxValid: boolean;
  taintEliminated: boolean;
  z3Verified: boolean;
  errors: VerificationError[];
}

interface LLMProvider {
  name: string;
  priority: number;
  isAvailable(): Promise<boolean>;
  generateFix(prompt: FixPrompt): Promise<string>;
}

interface FixPrompt {
  vulnerability: Vulnerability;
  vulnerableCode: string;
  codeContext: string;
  language: string;
  requirements: string[];
}

interface FixGenerator {
  /** Register LLM provider */
  registerProvider(provider: LLMProvider): void;
  /** Generate fix candidates */
  generateFixes(vulnerability: Vulnerability): Promise<FixCandidate[]>;
  /** Generate single fix */
  generateFix(vulnerability: Vulnerability): Promise<FixCandidate | null>;
}

interface FixVerifier {
  /** Verify a fix candidate */
  verify(fix: FixCandidate): Promise<VerificationResult>;
  /** Verify using Z3 */
  verifyWithZ3(fix: FixCandidate): Promise<Z3VerificationResult>;
  /** Re-run taint analysis */
  verifyTaintElimination(fix: FixCandidate): Promise<boolean>;
}

interface FixApplier {
  /** Apply fix with backup */
  apply(fix: FixCandidate): Promise<ApplyResult>;
  /** Rollback last applied fix */
  rollback(): Promise<void>;
  /** Apply with test verification */
  applyWithTests(fix: FixCandidate, testCommand?: string): Promise<ApplyResult>;
}
```

### 3.3 データベーススキーマ

#### 3.3.1 CVE Cache Schema (SQLite)

```sql
-- DES-SEC-CVE-DB-001: CVE Cache Schema
-- Location: ~/.musubix/cve-cache.db

CREATE TABLE cve (
  id TEXT PRIMARY KEY,           -- CVE-YYYY-NNNNN
  description TEXT NOT NULL,
  published_at TEXT NOT NULL,    -- ISO 8601
  modified_at TEXT NOT NULL,
  cvss_version TEXT,
  cvss_score REAL,
  cvss_severity TEXT,
  cvss_vector TEXT,
  cwe TEXT,                      -- JSON array
  references TEXT,               -- JSON array
  raw_data TEXT,                 -- Full NVD JSON
  cached_at TEXT NOT NULL,
  expires_at TEXT NOT NULL
);

CREATE TABLE cpe_match (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  cve_id TEXT NOT NULL REFERENCES cve(id),
  cpe TEXT NOT NULL,
  version_start_including TEXT,
  version_start_excluding TEXT,
  version_end_including TEXT,
  version_end_excluding TEXT
);

CREATE TABLE npm_cpe_mapping (
  npm_package TEXT PRIMARY KEY,
  cpe_vendor TEXT NOT NULL,
  cpe_product TEXT NOT NULL,
  updated_at TEXT NOT NULL
);

CREATE TABLE sync_metadata (
  key TEXT PRIMARY KEY,
  value TEXT NOT NULL
);

CREATE INDEX idx_cve_published ON cve(published_at);
CREATE INDEX idx_cve_severity ON cve(cvss_severity);
CREATE INDEX idx_cpe_match_cve ON cpe_match(cve_id);
CREATE INDEX idx_cpe_match_cpe ON cpe_match(cpe);
```

### 3.4 ルール定義形式

```yaml
# DES-SEC-RULES-FORMAT-001: OWASP A03 Injection Rules
# File: packages/security/src/rules/owasp/a03-injection.yaml

metadata:
  id: owasp-a03
  name: OWASP A03:2021 - Injection
  version: "1.0.0"
  description: Rules for detecting injection vulnerabilities

rules:
  # SQL Injection
  - id: sql-injection-template-literal
    name: SQL Injection via Template Literal
    severity: critical
    cwe: CWE-89
    owasp: A03
    message: |
      Possible SQL injection vulnerability. User-controlled data is interpolated 
      directly into a SQL query without parameterization.
    description: |
      Template literals containing tainted data should not be used directly in 
      SQL queries. Use parameterized queries instead.
    pattern:
      type: CallExpression
      callee:
        anyOf:
          - { object: { name: db }, property: query }
          - { object: { name: connection }, property: query }
          - { object: { name: pool }, property: query }
          - { callee: { name: query } }
      arguments:
        first:
          type: TemplateLiteral
          expressions:
            any:
              constraint: tainted
    fix:
      type: parameterize
      template: |
        ${callee}(${sql}, [${params}])
    references:
      - https://owasp.org/Top10/A03_2021-Injection/
      - https://cwe.mitre.org/data/definitions/89.html
      - https://cheatsheetseries.owasp.org/cheatsheets/SQL_Injection_Prevention_Cheat_Sheet.html
    tags:
      - sql
      - injection
      - database

  - id: sql-injection-string-concat
    name: SQL Injection via String Concatenation
    severity: critical
    cwe: CWE-89
    owasp: A03
    message: |
      Possible SQL injection. User input is concatenated into SQL query.
    pattern:
      type: CallExpression
      callee:
        anyOf:
          - { object: { name: db }, property: query }
      arguments:
        first:
          type: BinaryExpression
          operator: "+"
          anyOperand:
            constraint: tainted
    fix:
      type: parameterize
    references:
      - https://owasp.org/Top10/A03_2021-Injection/

  # Command Injection
  - id: command-injection-exec
    name: Command Injection via exec()
    severity: critical
    cwe: CWE-78
    owasp: A03
    message: |
      Possible command injection. User input is passed to exec() without sanitization.
    pattern:
      type: CallExpression
      callee:
        anyOf:
          - { name: exec }
          - { object: { name: child_process }, property: exec }
      arguments:
        any:
          constraint: tainted
    fix:
      type: replace
      template: |
        execFile(${command}, ${args}, ${options})
    references:
      - https://cwe.mitre.org/data/definitions/78.html

  # XSS
  - id: xss-innerhtml
    name: XSS via innerHTML
    severity: high
    cwe: CWE-79
    owasp: A03
    message: |
      Possible XSS vulnerability. User input is assigned to innerHTML without sanitization.
    pattern:
      type: AssignmentExpression
      left:
        type: MemberExpression
        property: innerHTML
      right:
        constraint: tainted
    fix:
      type: wrap
      template: |
        ${left} = DOMPurify.sanitize(${right})
      imports:
        - "import DOMPurify from 'dompurify'"
    references:
      - https://cwe.mitre.org/data/definitions/79.html
```

### 3.5 LLMプロバイダー実装

```typescript
// DES-SEC-FIX-LLM-001: VS Code LM Provider
// File: packages/security/src/remediation/providers/vscode-lm-provider.ts
// Trace: REQ-SEC-FIX-001

interface VSCodeLMProviderOptions {
  modelFamily?: string;  // e.g., 'copilot-gpt-4'
  maxTokens?: number;
  temperature?: number;
}

class VSCodeLMProvider implements LLMProvider {
  name = 'vscode-lm';
  priority = 1;  // Highest priority

  async isAvailable(): Promise<boolean> {
    // Check if VS Code LM API is available
    // This will be true when running in VS Code extension context
    return typeof vscode !== 'undefined' && 
           vscode.lm !== undefined &&
           (await vscode.lm.selectChatModels()).length > 0;
  }

  async generateFix(prompt: FixPrompt): Promise<string> {
    const models = await vscode.lm.selectChatModels({
      family: this.options.modelFamily
    });
    
    if (models.length === 0) {
      throw new Error('No LLM models available');
    }

    const model = models[0];
    const messages = [
      vscode.LanguageModelChatMessage.User(this.buildPrompt(prompt))
    ];

    const response = await model.sendRequest(messages, {
      maxTokens: this.options.maxTokens ?? 2048
    });

    let result = '';
    for await (const chunk of response.text) {
      result += chunk;
    }

    return this.extractCode(result);
  }

  private buildPrompt(prompt: FixPrompt): string {
    return `You are a security expert. Generate a secure fix for the following vulnerability.

## Vulnerability Information
- Type: ${prompt.vulnerability.type}
- CWE: ${prompt.vulnerability.cwe}
- Severity: ${prompt.vulnerability.severity}
- Location: ${prompt.vulnerability.location.file}:${prompt.vulnerability.location.line}

## Description
${prompt.vulnerability.description}

## Vulnerable Code
\`\`\`${prompt.language}
${prompt.vulnerableCode}
\`\`\`

## Context
\`\`\`${prompt.language}
${prompt.codeContext}
\`\`\`

## Requirements
${prompt.requirements.map(r => `- ${r}`).join('\n')}

## Instructions
1. Provide ONLY the fixed code, no explanations
2. The fix MUST eliminate the vulnerability
3. The fix MUST preserve the original functionality
4. Use security best practices (parameterized queries, output encoding, etc.)
5. Minimize changes - only fix the vulnerability

## Fixed Code
\`\`\`${prompt.language}`;
  }

  private extractCode(response: string): string {
    // Extract code from markdown code block
    const match = response.match(/```[\w]*\n([\s\S]*?)```/);
    return match ? match[1].trim() : response.trim();
  }
}
```

### 3.6 Z3検証統合

```typescript
// DES-SEC-FIX-Z3-001: Z3 Verification Integration
// File: packages/security/src/remediation/verification/z3-verifier.ts
// Trace: REQ-SEC-FIX-002

import { Z3Solver, SMTExpression } from '@nahisaho/musubix-formal-verify';

interface Z3VerificationResult {
  verified: boolean;
  constraints: SMTConstraint[];
  model?: Z3Model;
  counterexample?: string;
  time: number;
}

class Z3Verifier {
  private solver: Z3Solver;

  async verifyFix(fix: FixCandidate): Promise<Z3VerificationResult> {
    const startTime = Date.now();
    
    // Step 1: Parse fixed code and build constraints
    const constraints = await this.buildConstraints(fix);
    
    // Step 2: Add vulnerability-specific assertions
    const assertions = this.buildSecurityAssertions(fix.vulnerability);
    
    // Step 3: Run Z3 verification
    const result = await this.solver.verify([
      ...constraints,
      ...assertions
    ]);

    return {
      verified: result.satisfiable === false, // UNSAT means secure
      constraints,
      model: result.model,
      counterexample: result.satisfiable ? this.extractCounterexample(result) : undefined,
      time: Date.now() - startTime
    };
  }

  private buildSecurityAssertions(vuln: Vulnerability): SMTExpression[] {
    switch (vuln.cwe) {
      case 'CWE-89': // SQL Injection
        return this.buildSQLInjectionAssertions(vuln);
      case 'CWE-78': // Command Injection
        return this.buildCommandInjectionAssertions(vuln);
      case 'CWE-79': // XSS
        return this.buildXSSAssertions(vuln);
      default:
        return this.buildGenericTaintAssertions(vuln);
    }
  }

  private buildSQLInjectionAssertions(vuln: Vulnerability): SMTExpression[] {
    // Assert: No tainted data reaches SQL query without parameterization
    return [
      // ∀ input. isUserInput(input) ∧ reachesSQLQuery(input) → isParameterized(input)
      {
        type: 'forall',
        variable: 'input',
        body: {
          type: 'implies',
          left: {
            type: 'and',
            args: [
              { type: 'predicate', name: 'isUserInput', args: ['input'] },
              { type: 'predicate', name: 'reachesSQLQuery', args: ['input'] }
            ]
          },
          right: { type: 'predicate', name: 'isParameterized', args: ['input'] }
        }
      }
    ];
  }
}
```

---

## 4. シーケンス図

### 4.1 セキュリティスキャン フロー

```
┌──────┐    ┌──────────────┐    ┌───────────┐    ┌────────────┐    ┌───────────┐
│ User │    │SecurityScanner│    │TaintAnalyzer│    │ RuleEngine │    │CVEDatabase│
└──┬───┘    └──────┬───────┘    └─────┬─────┘    └─────┬──────┘    └─────┬─────┘
   │               │                   │                │                 │
   │ scan(options) │                   │                │                 │
   │──────────────>│                   │                │                 │
   │               │                   │                │                 │
   │               │ analyze(files)    │                │                 │
   │               │──────────────────>│                │                 │
   │               │                   │                │                 │
   │               │                   │ buildCallGraph │                 │
   │               │                   │───────────────>│                 │
   │               │                   │                │                 │
   │               │                   │ traceTaint     │                 │
   │               │                   │<───────────────│                 │
   │               │                   │                │                 │
   │               │    TaintPath[]    │                │                 │
   │               │<──────────────────│                │                 │
   │               │                   │                │                 │
   │               │ match(ast)                         │                 │
   │               │───────────────────────────────────>│                 │
   │               │                   │                │                 │
   │               │                   │  RuleMatch[]   │                 │
   │               │<───────────────────────────────────│                 │
   │               │                   │                │                 │
   │               │ checkDependencies()                                  │
   │               │─────────────────────────────────────────────────────>│
   │               │                   │                │                 │
   │               │                   │                │   CVEFinding[]  │
   │               │<─────────────────────────────────────────────────────│
   │               │                   │                │                 │
   │  ScanResult   │                   │                │                 │
   │<──────────────│                   │                │                 │
   │               │                   │                │                 │
```

### 4.2 自動修正フロー

```
┌──────┐   ┌────────────┐   ┌───────────┐   ┌───────────┐   ┌──────────┐
│ User │   │FixGenerator│   │LLMProvider│   │FixVerifier│   │FixApplier│
└──┬───┘   └─────┬──────┘   └─────┬─────┘   └─────┬─────┘   └─────┬────┘
   │             │                │               │               │
   │ generateFix │                │               │               │
   │────────────>│                │               │               │
   │             │                │               │               │
   │             │ isAvailable()  │               │               │
   │             │───────────────>│               │               │
   │             │     true       │               │               │
   │             │<───────────────│               │               │
   │             │                │               │               │
   │             │ generateFix(prompt)            │               │
   │             │───────────────>│               │               │
   │             │                │               │               │
   │             │   fixedCode    │               │               │
   │             │<───────────────│               │               │
   │             │                │               │               │
   │             │ verify(fix)                    │               │
   │             │───────────────────────────────>│               │
   │             │                │               │               │
   │             │                │   Z3 verify   │               │
   │             │                │   ──────────> │               │
   │             │                │               │               │
   │             │                │   Taint check │               │
   │             │                │   ──────────> │               │
   │             │                │               │               │
   │             │  VerificationResult            │               │
   │             │<───────────────────────────────│               │
   │             │                │               │               │
   │ FixCandidate│                │               │               │
   │<────────────│                │               │               │
   │             │                │               │               │
   │ apply(fix)  │                │               │               │
   │─────────────────────────────────────────────────────────────>│
   │             │                │               │               │
   │             │                │               │   backup()    │
   │             │                │               │   ──────────> │
   │             │                │               │               │
   │             │                │               │   patch()     │
   │             │                │               │   ──────────> │
   │             │                │               │               │
   │ ApplyResult │                │               │               │
   │<─────────────────────────────────────────────────────────────│
   │             │                │               │               │
```

---

## 5. 信頼度計算

### 5.1 Fix Confidence Score

```typescript
// DES-SEC-FIX-CONF-001: Confidence Score Calculation
// Trace: REQ-SEC-FIX-003

interface ConfidenceFactors {
  llmConfidence: number;      // 0-1: LLM reported confidence
  z3Verified: boolean;        // Z3 verification passed
  patternMatched: boolean;    // Matches known fix pattern
  historicalSuccess: number;  // 0-1: Historical success rate for this CWE
}

function calculateConfidence(factors: ConfidenceFactors): number {
  const weights = {
    llmConfidence: 0.3,
    z3Verified: 0.4,
    patternMatched: 0.2,
    historicalSuccess: 0.1
  };

  return (
    factors.llmConfidence * weights.llmConfidence +
    (factors.z3Verified ? 1.0 : 0.0) * weights.z3Verified +
    (factors.patternMatched ? 1.0 : 0.0) * weights.patternMatched +
    factors.historicalSuccess * weights.historicalSuccess
  );
}

function getConfidenceLabel(score: number): ConfidenceLabel {
  if (score >= 0.9) return { label: 'high', autoApply: true };
  if (score >= 0.7) return { label: 'medium', autoApply: false, requiresReview: true };
  if (score >= 0.5) return { label: 'low', autoApply: false, requiresReview: true };
  return { label: 'unreliable', autoApply: false, rejected: true };
}
```

---

## 6. エラーハンドリング

### 6.1 エラー分類

| エラーコード | カテゴリ | 対応 |
|-------------|---------|------|
| SEC-E001 | Parse Error | ファイルスキップ、警告出力 |
| SEC-E002 | NVD API Error | キャッシュフォールバック |
| SEC-E003 | LLM Unavailable | 次のプロバイダーへフォールバック |
| SEC-E004 | Z3 Timeout | 検証スキップ、警告付きで返却 |
| SEC-E005 | Fix Apply Error | ロールバック実行 |

### 6.2 エラーハンドリング詳細

```typescript
// DES-SEC-ERROR-001: Error Handling Implementation

/**
 * Security module error codes
 */
export enum SecurityErrorCode {
  // Parse errors (SEC-E001)
  PARSE_ERROR = 'SEC-E001-001',
  INVALID_SYNTAX = 'SEC-E001-002',
  UNSUPPORTED_LANGUAGE = 'SEC-E001-003',
  
  // NVD API errors (SEC-E002)
  NVD_API_RATE_LIMIT = 'SEC-E002-001',
  NVD_API_TIMEOUT = 'SEC-E002-002',
  NVD_API_UNAUTHORIZED = 'SEC-E002-003',
  NVD_API_UNAVAILABLE = 'SEC-E002-004',
  
  // LLM errors (SEC-E003)
  LLM_NO_PROVIDER = 'SEC-E003-001',
  LLM_QUOTA_EXCEEDED = 'SEC-E003-002',
  LLM_INVALID_RESPONSE = 'SEC-E003-003',
  LLM_TIMEOUT = 'SEC-E003-004',
  
  // Z3 errors (SEC-E004)
  Z3_TIMEOUT = 'SEC-E004-001',
  Z3_UNKNOWN = 'SEC-E004-002',
  Z3_INVALID_CONSTRAINT = 'SEC-E004-003',
  
  // Fix apply errors (SEC-E005)
  FIX_BACKUP_FAILED = 'SEC-E005-001',
  FIX_PATCH_FAILED = 'SEC-E005-002',
  FIX_TEST_FAILED = 'SEC-E005-003',
  FIX_ROLLBACK_FAILED = 'SEC-E005-004',
}

/**
 * Error handler with recovery strategies
 */
class SecurityErrorHandler {
  async handle(error: SecurityError): Promise<RecoveryResult> {
    switch (error.category) {
      case 'SEC-E001':
        // Parse Error: Skip file, log warning
        return {
          recovered: true,
          action: 'skip',
          message: `Skipped file due to parse error: ${error.file}`,
        };
        
      case 'SEC-E002':
        // NVD API Error: Use cache fallback
        if (await this.cveCache.hasValidCache()) {
          return {
            recovered: true,
            action: 'cache-fallback',
            message: 'Using cached CVE data (may be stale)',
          };
        }
        return { recovered: false, action: 'abort', message: error.message };
        
      case 'SEC-E003':
        // LLM Unavailable: Try next provider
        const nextProvider = await this.providerRegistry.getNextAvailable();
        if (nextProvider) {
          return {
            recovered: true,
            action: 'fallback-provider',
            message: `Falling back to ${nextProvider.name}`,
            data: { provider: nextProvider },
          };
        }
        // Fall back to pattern-based fix
        return {
          recovered: true,
          action: 'pattern-fallback',
          message: 'Using pattern-based fix generation',
        };
        
      case 'SEC-E004':
        // Z3 Timeout: Skip verification, warn
        return {
          recovered: true,
          action: 'skip-verification',
          message: 'Z3 verification skipped due to timeout',
          warning: true,
        };
        
      case 'SEC-E005':
        // Fix Apply Error: Rollback
        await this.rollbackManager.rollback();
        return {
          recovered: true,
          action: 'rollback',
          message: 'Changes rolled back successfully',
        };
        
      default:
        return { recovered: false, action: 'abort', message: error.message };
    }
  }
}
```

---

## 7. YATA知識グラフ統合

### 7.1 テイントパスの知識グラフ保存

```typescript
// DES-SEC-YATA-001: YATA Integration for Taint Paths
// Trace: REQ-SEC-TAINT-004

import { YataLocal, Triple, Entity } from '@nahisaho/yata-local';

/**
 * YATA namespace for security ontology
 */
const SEC_NS = 'https://musubix.dev/ontology/security#';

/**
 * Security knowledge graph entities
 */
interface SecurityEntities {
  TaintSource: 'sec:TaintSource';
  TaintSink: 'sec:TaintSink';
  TaintPath: 'sec:TaintPath';
  Vulnerability: 'sec:Vulnerability';
  CVE: 'sec:CVE';
  Fix: 'sec:Fix';
  Rule: 'sec:Rule';
}

/**
 * Security knowledge graph predicates
 */
interface SecurityPredicates {
  hasSource: 'sec:hasSource';
  hasSink: 'sec:hasSink';
  flowsTo: 'sec:flowsTo';
  sanitizedBy: 'sec:sanitizedBy';
  affectedBy: 'sec:affectedBy';
  fixedBy: 'sec:fixedBy';
  detectedBy: 'sec:detectedBy';
  hasSeverity: 'sec:hasSeverity';
  hasCWE: 'sec:hasCWE';
  inFile: 'sec:inFile';
  atLine: 'sec:atLine';
}

/**
 * Store taint path in YATA knowledge graph
 */
class TaintPathStore {
  constructor(private yata: YataLocal) {}

  async storeTaintPath(path: TaintPath): Promise<void> {
    const pathUri = `${SEC_NS}path/${path.id}`;
    const sourceUri = `${SEC_NS}source/${path.source.id}`;
    const sinkUri = `${SEC_NS}sink/${path.sink.id}`;

    const triples: Triple[] = [
      // Path entity
      { subject: pathUri, predicate: 'rdf:type', object: 'sec:TaintPath' },
      { subject: pathUri, predicate: 'sec:hasSource', object: sourceUri },
      { subject: pathUri, predicate: 'sec:hasSink', object: sinkUri },
      { subject: pathUri, predicate: 'sec:confidence', object: path.confidence },
      { subject: pathUri, predicate: 'sec:sanitized', object: path.sanitized },
      
      // Source entity
      { subject: sourceUri, predicate: 'rdf:type', object: 'sec:TaintSource' },
      { subject: sourceUri, predicate: 'sec:category', object: path.source.category },
      { subject: sourceUri, predicate: 'sec:inFile', object: path.source.location.file },
      { subject: sourceUri, predicate: 'sec:atLine', object: path.source.location.line },
      { subject: sourceUri, predicate: 'sec:expression', object: path.source.expression },
      
      // Sink entity
      { subject: sinkUri, predicate: 'rdf:type', object: 'sec:TaintSink' },
      { subject: sinkUri, predicate: 'sec:category', object: path.sink.category },
      { subject: sinkUri, predicate: 'sec:hasSeverity', object: path.sink.severity },
      { subject: sinkUri, predicate: 'sec:inFile', object: path.sink.location.file },
      { subject: sinkUri, predicate: 'sec:atLine', object: path.sink.location.line },
    ];

    // Store flow steps
    for (let i = 0; i < path.steps.length; i++) {
      const step = path.steps[i];
      const stepUri = `${pathUri}/step/${i}`;
      triples.push(
        { subject: stepUri, predicate: 'rdf:type', object: 'sec:FlowStep' },
        { subject: pathUri, predicate: 'sec:hasStep', object: stepUri },
        { subject: stepUri, predicate: 'sec:index', object: i },
        { subject: stepUri, predicate: 'sec:expression', object: step.expression },
        { subject: stepUri, predicate: 'sec:inFile', object: step.location.file },
        { subject: stepUri, predicate: 'sec:atLine', object: step.location.line },
      );
      
      // Link flow: step[i] -> step[i+1]
      if (i > 0) {
        const prevStepUri = `${pathUri}/step/${i - 1}`;
        triples.push({ subject: prevStepUri, predicate: 'sec:flowsTo', object: stepUri });
      }
    }

    await this.yata.addTriples(triples);
  }

  /**
   * Query taint paths by sink category
   */
  async queryPathsBySink(category: TaintSinkCategory): Promise<TaintPath[]> {
    const query = `
      SELECT ?path ?source ?sink ?confidence
      WHERE {
        ?path rdf:type sec:TaintPath .
        ?path sec:hasSource ?source .
        ?path sec:hasSink ?sink .
        ?path sec:confidence ?confidence .
        ?sink sec:category "${category}" .
        ?path sec:sanitized false .
      }
      ORDER BY DESC(?confidence)
    `;
    return this.yata.query(query);
  }

  /**
   * Find similar vulnerabilities for pattern learning
   */
  async findSimilarVulnerabilities(vuln: Vulnerability): Promise<Vulnerability[]> {
    const query = `
      SELECT ?vuln ?fix ?confidence
      WHERE {
        ?vuln rdf:type sec:Vulnerability .
        ?vuln sec:hasCWE "${vuln.cwe}" .
        ?vuln sec:fixedBy ?fix .
        ?fix sec:confidence ?confidence .
        FILTER(?confidence >= 0.8)
      }
      ORDER BY DESC(?confidence)
      LIMIT 5
    `;
    return this.yata.query(query);
  }
}
```

### 7.2 学習済み修正パターンの保存

```typescript
// DES-SEC-YATA-002: Fix Pattern Learning Storage

/**
 * Store successful fix pattern for future learning
 */
async storeFixPattern(fix: FixCandidate, success: boolean): Promise<void> {
  const fixUri = `${SEC_NS}fix/${fix.id}`;
  const vulnUri = `${SEC_NS}vuln/${fix.vulnerability.id}`;

  const triples: Triple[] = [
    { subject: fixUri, predicate: 'rdf:type', object: 'sec:Fix' },
    { subject: fixUri, predicate: 'sec:forVulnerability', object: vulnUri },
    { subject: fixUri, predicate: 'sec:provider', object: fix.provider },
    { subject: fixUri, predicate: 'sec:confidence', object: fix.confidence },
    { subject: fixUri, predicate: 'sec:success', object: success },
    { subject: fixUri, predicate: 'sec:timestamp', object: new Date().toISOString() },
    { subject: vulnUri, predicate: 'sec:hasCWE', object: fix.vulnerability.cwe },
    { subject: vulnUri, predicate: 'sec:hasSeverity', object: fix.vulnerability.severity },
  ];

  // Store code pattern (hashed for privacy)
  const patternHash = this.hashPattern(fix.originalCode, fix.fixedCode);
  triples.push({ subject: fixUri, predicate: 'sec:patternHash', object: patternHash });

  await this.yata.addTriples(triples);

  // Update historical success rate for confidence calculation
  await this.updateHistoricalSuccessRate(fix.vulnerability.cwe, success);
}
```

---

## 8. 既存実装との移行パス

### 8.1 ディレクトリ構造の段階的移行

```
現状 → v2.1.0 移行計画

packages/security/src/
├── analysis/
│   ├── taint-analyzer.ts          # 維持（拡張）
│   ├── vulnerability-scanner.ts   # 維持
│   ├── dependency-auditor.ts      # 維持
│   ├── secret-detector.ts         # 維持
│   ├── interprocedural/           # 🆕 新規作成
│   │   ├── call-graph-builder.ts
│   │   ├── taint-propagator.ts
│   │   └── context-sensitivity.ts
│   ├── sources/                   # 🆕 taint-analyzer.tsから抽出
│   │   ├── source-registry.ts
│   │   └── builtin-sources.ts
│   ├── sinks/                     # 🆕 taint-analyzer.tsから抽出
│   │   ├── sink-registry.ts
│   │   └── builtin-sinks.ts
│   ├── sanitizers/                # 🆕 types/taint.tsから抽出
│   │   ├── sanitizer-registry.ts
│   │   └── builtin-sanitizers.ts
│   └── dfg-adapter.ts             # 🆕 新規作成
├── remediation/
│   ├── auto-fixer.ts              # → fix-generator.ts にリネーム・拡張
│   ├── fix-validator.ts           # → verification/fix-validator.ts に移動
│   ├── patch-generator.ts         # 維持
│   ├── remediation-planner.ts     # 維持
│   ├── secure-code-transformer.ts # 維持
│   ├── providers/                 # 🆕 新規作成
│   │   ├── provider-registry.ts
│   │   ├── vscode-lm-provider.ts
│   │   ├── ollama-provider.ts
│   │   └── pattern-fallback.ts
│   ├── prompts/                   # 🆕 新規作成
│   │   ├── fix-prompt-builder.ts
│   │   └── templates/
│   └── verification/              # 🆕 新規作成
│       ├── syntax-checker.ts
│       ├── taint-rechecker.ts
│       └── z3-verifier.ts
├── databases/                     # 🆕 新規作成
│   ├── cve-database.ts
│   ├── nvd-client.ts
│   ├── local-cache.ts
│   ├── cve-matcher.ts
│   └── cpe-mapper.ts
├── rules/                         # 🆕 新規作成
│   ├── rule-engine.ts
│   ├── rule-loader.ts
│   ├── rule-matcher.ts
│   ├── owasp/
│   │   └── *.yaml
│   └── cwe/
│       └── *.yaml
└── types/
    ├── taint.ts                   # 維持（既存実装を尊重）
    ├── vulnerability.ts           # 維持
    ├── cve.ts                     # 🆕 新規作成
    ├── rule.ts                    # 🆕 新規作成
    └── fix.ts                     # 維持（拡張）
```

### 8.2 後方互換性の維持

```typescript
// DES-SEC-COMPAT-001: Backward Compatibility Layer

/**
 * Legacy API compatibility wrapper
 * Ensures existing code continues to work during migration
 */

// Old API (deprecated but functional)
export { TaintAnalyzer } from './analysis/taint-analyzer.js';

// New API with enhanced features
export { 
  EnhancedTaintAnalyzer,
  InterproceduralAnalyzer,
  SourceRegistry,
  SinkRegistry,
} from './analysis/index.js';

// Deprecation notice
/** @deprecated Use EnhancedTaintAnalyzer instead. Will be removed in v3.0.0 */
export const analyzeTaint = async (files: string[]) => {
  console.warn('analyzeTaint() is deprecated. Use EnhancedTaintAnalyzer.analyze()');
  const analyzer = new EnhancedTaintAnalyzer();
  return analyzer.analyze(files);
};
```

---

## 9. トレーサビリティマトリクス

| 要件ID | 設計ID | 実装ファイル | 既存/新規 |
|--------|--------|-------------|----------|
| REQ-SEC-TAINT-001 | DES-SEC-TAINT-001 | analysis/interprocedural/* | 🆕 新規 |
| REQ-SEC-TAINT-002 | DES-SEC-TAINT-002 | analysis/sources/*, analysis/sinks/* | 🔄 リファクタ |
| REQ-SEC-TAINT-003 | DES-SEC-TAINT-003 | analysis/sanitizers/* | 🔄 リファクタ |
| REQ-SEC-TAINT-004 | DES-SEC-TAINT-004 | analysis/dfg-adapter.ts | 🆕 新規 |
| REQ-SEC-CVE-001 | DES-SEC-CVE-001 | databases/nvd-client.ts | 🆕 新規 |
| REQ-SEC-CVE-002 | DES-SEC-CVE-002 | databases/local-cache.ts | 🆕 新規 |
| REQ-SEC-CVE-003 | DES-SEC-CVE-003 | databases/cve-matcher.ts | 🆕 新規 |
| REQ-SEC-CVE-004 | DES-SEC-CVE-004 | databases/cve-database.ts | 🆕 新規 |
| REQ-SEC-RULES-001 | DES-SEC-RULES-001 | rules/owasp/* | 🆕 新規 |
| REQ-SEC-RULES-002 | DES-SEC-RULES-002 | rules/cwe/* | 🆕 新規 |
| REQ-SEC-RULES-003 | DES-SEC-RULES-003 | rules/rule-loader.ts | 🆕 新規 |
| REQ-SEC-RULES-004 | DES-SEC-RULES-004 | rules/rule-engine.ts | 🆕 新規 |
| REQ-SEC-FIX-001 | DES-SEC-FIX-001 | remediation/fix-generator.ts | 🔄 リネーム拡張 |
| REQ-SEC-FIX-002 | DES-SEC-FIX-002 | remediation/verification/* | 🆕 新規 |
| REQ-SEC-FIX-003 | DES-SEC-FIX-003 | remediation/fix-generator.ts | 🔄 拡張 |
| REQ-SEC-FIX-004 | DES-SEC-FIX-004 | remediation/fix-applier.ts | 🔄 拡張 |
| - | DES-SEC-YATA-001 | intelligence/yata-integration.ts | 🆕 新規 |
| - | DES-SEC-COMPAT-001 | index.ts (compatibility layer) | 🆕 新規 |

---

## 10. 承認

| 役割 | 名前 | 日付 | 署名 |
|------|------|------|------|
| 設計者 | AI Assistant | 2026-01-08 | ✓ |
| レビュアー | | | |
| 承認者 | | | |

---

## 付録A: 並列処理設計

### A.1 ScanCoordinator並列処理

```typescript
// DES-SEC-PARALLEL-001: Parallel Scan Coordination

interface ParallelScanOptions {
  /** Maximum concurrent file scans */
  concurrency: number;
  /** Chunk size for batch processing */
  chunkSize: number;
  /** Timeout per file in ms */
  fileTimeout: number;
}

class ScanCoordinator {
  async scanParallel(files: string[], options: ParallelScanOptions): Promise<ScanResult[]> {
    const { concurrency, chunkSize, fileTimeout } = options;
    
    // Split files into chunks
    const chunks = this.chunkArray(files, chunkSize);
    const results: ScanResult[] = [];
    
    // Process chunks with concurrency limit
    const semaphore = new Semaphore(concurrency);
    
    await Promise.all(
      chunks.map(async (chunk) => {
        await semaphore.acquire();
        try {
          const chunkResults = await Promise.allSettled(
            chunk.map(file => 
              this.withTimeout(this.scanFile(file), fileTimeout)
            )
          );
          
          for (const result of chunkResults) {
            if (result.status === 'fulfilled') {
              results.push(result.value);
            } else {
              // Handle timeout or error
              this.handleScanError(result.reason);
            }
          }
        } finally {
          semaphore.release();
        }
      })
    );
    
    return results;
  }
}
```

### A.2 インクリメンタルスキャン

```typescript
// DES-SEC-INCREMENTAL-001: Incremental Scan Design

interface FileCache {
  hash: string;
  lastScanned: Date;
  result: ScanResult;
}

class IncrementalScanner {
  private cache: Map<string, FileCache> = new Map();

  async scanIncremental(files: string[]): Promise<ScanResult[]> {
    const results: ScanResult[] = [];
    const toScan: string[] = [];

    for (const file of files) {
      const hash = await this.computeFileHash(file);
      const cached = this.cache.get(file);

      if (cached && cached.hash === hash) {
        // File unchanged, use cached result
        results.push(cached.result);
      } else {
        // File changed or new, need to scan
        toScan.push(file);
      }
    }

    // Scan changed files
    const newResults = await this.scanParallel(toScan);
    
    // Update cache
    for (let i = 0; i < toScan.length; i++) {
      const file = toScan[i];
      const hash = await this.computeFileHash(file);
      this.cache.set(file, {
        hash,
        lastScanned: new Date(),
        result: newResults[i],
      });
    }

    return [...results, ...newResults];
  }
}
```

---

## 付録B: CVEキャッシュ更新戦略

### B.1 キャッシュ更新タイミング

| トリガー | 更新範囲 | 説明 |
|---------|---------|------|
| **初回起動** | Full sync | 全CVEデータをダウンロード |
| **24時間経過** | Incremental | 最終同期以降の差分のみ |
| **手動要求** | Full/Incremental | ユーザー指定 |
| **CVEチェック時** | On-demand | 該当パッケージのみ |

### B.2 キャッシュ更新フロー

```typescript
// DES-SEC-CACHE-001: Cache Update Strategy

class CVECacheManager {
  async sync(options: SyncOptions = {}): Promise<SyncResult> {
    const lastSync = await this.getLastSyncTime();
    const now = new Date();
    const hoursSinceSync = (now.getTime() - lastSync.getTime()) / (1000 * 60 * 60);

    // Determine sync strategy
    if (options.full || !lastSync || hoursSinceSync > 168) { // 1 week
      return this.fullSync();
    } else if (hoursSinceSync > 24) {
      return this.incrementalSync(lastSync);
    } else {
      return { synced: false, reason: 'Cache is fresh' };
    }
  }

  private async incrementalSync(since: Date): Promise<SyncResult> {
    // Use NVD API's lastModStartDate parameter
    const cves = await this.nvdClient.getCVEs({
      lastModStartDate: since.toISOString(),
      resultsPerPage: 2000,
    });

    let updated = 0;
    for (const cve of cves) {
      await this.localCache.upsert(cve);
      updated++;
    }

    await this.setLastSyncTime(new Date());
    return { synced: true, updated, strategy: 'incremental' };
  }
}
```

---

**© 2026 MUSUBIX Project**
