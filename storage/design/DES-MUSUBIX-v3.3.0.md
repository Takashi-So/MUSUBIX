# MUSUBIX v3.3.0 設計書
# Scaffold Enhancement & Pattern Learning Integration

**文書ID**: DES-MUSUBIX-v3.3.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.1  
**作成日**: 2026-01-14  
**更新日**: 2026-01-14  
**ステータス**: Reviewed  
**準拠規格**: C4モデル  
**参照文書**: REQ-MUSUBIX-v3.3.0.md

---

## 1. 設計概要

### 1.1 目的

本文書は、v3.3.0の要件（REQ-MUSUBIX-v3.3.0.md）をC4モデルに基づいて設計する。Scaffold機能の強化、パターン学習の自動化、Expert-Delegation統合を実現するコンポーネント設計を定義する。

### 1.2 設計原則

| 原則 | 適用方法 |
|------|----------|
| **Single Responsibility** | 各コンポーネントは1つの責務のみ担当 |
| **Open-Closed** | 新パターン追加時に既存コード変更不要 |
| **Dependency Inversion** | 抽象インターフェースへの依存 |
| **Interface Segregation** | 必要最小限のインターフェース公開 |
| **Neuro-Symbolic分離** | MUSUBIX=構造化、Copilot=推論 |

### 1.3 影響範囲

| パッケージ | 変更種別 | 影響レベル |
|-----------|---------|-----------|
| `@nahisaho/musubix-core` | 機能追加 | 中 |
| `@nahisaho/musubix-pattern-mcp` | 機能追加 | 中 |
| `@nahisaho/musubix-expert-delegation` | 統合追加 | 低 |
| `@nahisaho/musubix-mcp-server` | プロンプト追加 | 低 |

---

## 2. C4モデル

### 2.1 Context図

```
┌──────────────────────────────────────────────────────────────────┐
│                         Developer                                 │
└───────────────────────────┬──────────────────────────────────────┘
                            │
                            ▼
┌──────────────────────────────────────────────────────────────────┐
│                      GitHub Copilot                               │
│  (sdd_expert_scaffold プロンプト / 対話処理)                       │
└───────────────────────────┬──────────────────────────────────────┘
                            │
                            ▼
┌──────────────────────────────────────────────────────────────────┐
│                        MUSUBIX CLI                                │
│  scaffold domain-model / learn recommend / learn extract          │
└───────────────────────────┬──────────────────────────────────────┘
                            │
        ┌───────────────────┼───────────────────┐
        ▼                   ▼                   ▼
┌───────────────┐   ┌───────────────┐   ┌───────────────┐
│ Scaffold      │   │ Pattern       │   │ Expert        │
│ Generator     │   │ Learning      │   │ Delegation    │
│ (Enhanced)    │   │ (Enhanced)    │   │ (Integrated)  │
└───────────────┘   └───────────────┘   └───────────────┘
        │                   │                   │
        └───────────────────┼───────────────────┘
                            ▼
                ┌───────────────────────┐
                │  storage/learning/    │
                │  (Pattern Library)    │
                └───────────────────────┘
```

### 2.2 Container図

```
┌─────────────────────────────────────────────────────────────────────────┐
│                              MUSUBIX System                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌──────────────────────────────────────────────────────────────────┐   │
│  │                    @nahisaho/musubix-core                         │   │
│  │  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐      │   │
│  │  │ ScaffoldEngine │  │ ValueObject    │  │ StatusMachine  │      │   │
│  │  │ (Enhanced)     │  │ Generator      │  │ Generator      │      │   │
│  │  │ [REQ-SCF-005]  │  │ [REQ-SCF-001]  │  │ [REQ-SCF-003]  │      │   │
│  │  └────────────────┘  └────────────────┘  └────────────────┘      │   │
│  │           │                  │                   │                │   │
│  │           └──────────────────┼───────────────────┘                │   │
│  │                              ▼                                    │   │
│  │                    ┌────────────────┐                             │   │
│  │                    │ ScaffoldResult │                             │   │
│  │                    │ Aggregator     │                             │   │
│  │                    └────────────────┘                             │   │
│  └──────────────────────────────────────────────────────────────────┘   │
│                                                                          │
│  ┌──────────────────────────────────────────────────────────────────┐   │
│  │                  @nahisaho/musubix-pattern-mcp                    │   │
│  │  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐      │   │
│  │  │ PatternAuto    │  │ PatternDecay   │  │ PatternRecom   │      │   │
│  │  │ Extractor      │  │ Manager        │  │ -mender        │      │   │
│  │  │ [REQ-PTN-001]  │  │ [REQ-PTN-004]  │  │ [REQ-PTN-005]  │      │   │
│  │  └────────────────┘  └────────────────┘  └────────────────┘      │   │
│  │           │                  │                   │                │   │
│  │           └──────────────────┴───────────────────┘                │   │
│  │                              │                                    │   │
│  │                    ┌─────────▼────────┐                           │   │
│  │                    │  PatternLibrary  │                           │   │
│  │                    │  (Enhanced)      │                           │   │
│  │                    └──────────────────┘                           │   │
│  └──────────────────────────────────────────────────────────────────┘   │
│                                                                          │
│  ┌──────────────────────────────────────────────────────────────────┐   │
│  │               @nahisaho/musubix-expert-delegation                 │   │
│  │  ┌────────────────┐  ┌────────────────┐                          │   │
│  │  │ ScaffoldExpert │  │ SecurityExpert │                          │   │
│  │  │ Integrator     │  │ Integrator     │                          │   │
│  │  │ [REQ-EXD-001]  │  │ [REQ-EXD-002]  │                          │   │
│  │  └────────────────┘  └────────────────┘                          │   │
│  └──────────────────────────────────────────────────────────────────┘   │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 3. Component設計

### 3.1 DES-SCF-001: Value Object Generator

**対応要件**: REQ-SCF-001, REQ-SCF-002

```typescript
// packages/core/src/cli/generators/value-object-generator.ts

/**
 * Value Object生成器
 * @traceability REQ-SCF-001, REQ-SCF-002
 */
export interface ValueObjectSpec {
  name: string;              // VO名（例: "Price"）
  validationType: 'range' | 'format' | 'custom';
  validationRules?: ValidationRule[];
}

export interface ValueObjectGeneratorConfig {
  domain: string;
  outputDir: string;
  generateTests: boolean;
}

export class ValueObjectGenerator {
  constructor(private config: ValueObjectGeneratorConfig) {}

  /**
   * VOファイルを生成
   */
  async generate(specs: ValueObjectSpec[]): Promise<GeneratedFile[]>;

  /**
   * テストファイルを生成
   */
  async generateTests(specs: ValueObjectSpec[]): Promise<GeneratedFile[]>;
}

// 生成テンプレート
const VALUE_OBJECT_TEMPLATE = `
// @traceability REQ-SCF-001
export interface {{Name}} {
  readonly {{field}}: {{type}};
}

export function create{{Name}}({{params}}): Result<{{Name}}, ValidationError> {
  {{validation}}
  return ok({ {{fields}} });
}

export function {{name}}Equals(a: {{Name}}, b: {{Name}}): boolean {
  return {{equalityCheck}};
}

export function is{{Name}}(value: unknown): value is {{Name}} {
  return typeof value === 'object' && value !== null && '{{field}}' in value;
}
`;
```

**ディレクトリ構造**:
```
packages/core/src/cli/
├── generators/
│   ├── value-object-generator.ts   # NEW
│   ├── status-machine-generator.ts # NEW
│   └── index.ts
└── commands/
    └── scaffold.ts                  # MODIFIED
```

---

### 3.2 DES-SCF-002: Status Machine Generator

**対応要件**: REQ-SCF-003, REQ-SCF-004

#### 📝 ADR-v3.3.0-001: -sオプション構文決定

| 項目 | 内容 |
|------|------|
| **決定** | `-s "Entity=initial_status"` (イコール区切り) を採用 |
| **理由** | -eオプションの`Entity:Relation`構文との競合回避 |
| **棄却案** | `:` 区切り、サブオプション、設定ファイル |
| **状態** | **確定** |

```typescript
// packages/core/src/cli/generators/status-machine-generator.ts

/**
 * Status Machine生成器
 * @traceability REQ-SCF-003, REQ-SCF-004
 * 
 * 設計決定: -sオプション構文（REQ-SCF-004）
 * 採用案: `-s "Entity=initial_status"` (イコール区切り)
 * 理由: -eオプション（Entity:Relation）との構文競合回避
 */
export interface StatusMachineSpec {
  entityName: string;
  initialStatus?: string;      // デフォルト: 最初のステータス
  statuses: string[];          // 例: ['draft', 'active', 'completed']
  transitions: StatusTransition[];
}

export interface StatusTransition {
  from: string;
  to: string[];
}

export interface StatusMachineGeneratorConfig {
  domain: string;
  outputDir: string;
  generateTests: boolean;
  generateEnum: boolean;       // --enum オプション対応
}

export class StatusMachineGenerator {
  constructor(private config: StatusMachineGeneratorConfig) {}

  /**
   * Status Machineファイルを生成
   */
  async generate(specs: StatusMachineSpec[]): Promise<GeneratedFile[]>;

  /**
   * 遷移バリデータを生成
   */
  private generateTransitionValidator(spec: StatusMachineSpec): string;

  /**
   * デフォルトステータス一覧を生成
   */
  private getDefaultStatuses(entityName: string): string[] {
    return ['draft', 'active', 'completed', 'cancelled'];
  }
}

// 生成テンプレート
const STATUS_MACHINE_TEMPLATE = `
// @traceability REQ-SCF-003
export type {{Name}}Status = {{statusUnion}};

export const {{name}}StatusList: readonly {{Name}}Status[] = [{{statuses}}] as const;

export const valid{{Name}}Transitions: Record<{{Name}}Status, {{Name}}Status[]> = {
  {{transitions}}
};

export function canTransition{{Name}}(from: {{Name}}Status, to: {{Name}}Status): boolean {
  return valid{{Name}}Transitions[from]?.includes(to) ?? false;
}

export function transition{{Name}}(
  entity: {{Name}},
  newStatus: {{Name}}Status
): Result<{{Name}}, StatusTransitionError> {
  if (!canTransition{{Name}}(entity.status, newStatus)) {
    return err(new StatusTransitionError(
      \`Cannot transition from \${entity.status} to \${newStatus}\`
    ));
  }
  return ok({ ...entity, status: newStatus });
}
`;
```

**-sオプション構文決定**:
```bash
# 採用構文（イコール区切り）
npx musubix scaffold domain-model order -e "Order,Task" -s "Order=draft,Task=pending"

# 解析ロジック
function parseStatusOption(input: string): Map<string, string> {
  // "Order=draft,Task=pending" → { Order: "draft", Task: "pending" }
  const map = new Map<string, string>();
  for (const pair of input.split(',')) {
    const [entity, status] = pair.split('=');
    if (entity && status) {
      map.set(entity.trim(), status.trim());
    }
  }
  return map;
}
```

---

### 3.3 DES-SCF-003: Scaffold Result Aggregator

**対応要件**: REQ-SCF-005, REQ-SCF-006

```typescript
// packages/core/src/cli/generators/scaffold-result-aggregator.ts

/**
 * Scaffold結果集約・表示
 * @traceability REQ-SCF-005, REQ-SCF-006
 */
export interface ScaffoldSummary {
  projectPath: string;
  entities: EntitySummary[];
  valueObjects: string[];
  statusMachines: string[];
  filesCreated: number;
  testsCreated: number;
  duration: number;           // ミリ秒
}

export interface EntitySummary {
  name: string;
  hasStatus: boolean;
  testCount: number;
}

export class ScaffoldResultAggregator {
  /**
   * 生成結果を集約
   */
  aggregate(results: GeneratedFile[]): ScaffoldSummary;

  /**
   * サマリーを整形して出力
   */
  format(summary: ScaffoldSummary, options?: FormatOptions): string;

  /**
   * Dry-runモード用のプレビュー表示
   */
  formatPreview(plan: GenerationPlan): string;
}

// 出力フォーマット例
const SUMMARY_TEMPLATE = `
✅ Created SDD project scaffold at {{projectPath}}

📊 Generation Summary:
   Entities: {{entityCount}} ({{entityNames}})
   Value Objects: {{voCount}} ({{voNames}})
   Status Machines: {{smCount}} ({{smNames}})
   Tests: {{testCount}} files
   Duration: {{duration}}ms

🚀 Next steps:
   cd {{projectName}}
   npm install
   npm run test
`;
```

---

### 3.4 DES-PTN-001: Pattern Auto Extractor

**対応要件**: REQ-PTN-001, REQ-PTN-002

```typescript
// packages/pattern-mcp/src/extractor/auto-extractor.ts

/**
 * Scaffold後自動パターン抽出
 * @traceability REQ-PTN-001, REQ-PTN-002
 */
export interface AutoExtractConfig {
  patterns: PatternDetector[];
  minConfidence: number;      // デフォルト: 60
  autoRegister: boolean;
}

export interface DetectedPattern {
  id: string;
  category: 'code' | 'design' | 'test';
  name: string;
  confidence: number;
  instances: number;
  sourceFiles: string[];
}

export class PatternAutoExtractor {
  constructor(
    private library: PatternLibrary,
    private config: AutoExtractConfig
  ) {}

  /**
   * ディレクトリからパターンを自動検出
   */
  async extractFromDirectory(path: string): Promise<DetectedPattern[]>;

  /**
   * Scaffold生成コードから自動抽出・登録
   */
  async extractAndRegister(files: GeneratedFile[]): Promise<void>;

  /**
   * 既存ライブラリとの重複チェック
   */
  private checkDuplicate(pattern: DetectedPattern): boolean;
}

// 組み込みパターン検出器
export const builtInDetectors: PatternDetector[] = [
  {
    id: 'entity-input-dto',
    pattern: /interface \w+Input\s*{/,
    category: 'code',
    confidence: 85,
  },
  {
    id: 'result-type',
    pattern: /Result<\w+,\s*\w+Error>/,
    category: 'code',
    confidence: 90,
  },
  {
    id: 'status-transition-map',
    pattern: /valid\w+Transitions:\s*Record</,
    category: 'design',
    confidence: 85,
  },
  {
    id: 'test-counter-reset',
    pattern: /beforeEach.*reset\w+Counter/s,
    category: 'test',
    confidence: 80,
  },
];
```

---

### 3.5 DES-PTN-003: Pattern Decay Manager

**対応要件**: REQ-PTN-003, REQ-PTN-004

```typescript
// packages/pattern-mcp/src/library/pattern-decay-manager.ts

/**
 * パターン信頼度管理・減衰
 * @traceability REQ-PTN-003, REQ-PTN-004
 */
export interface DecayConfig {
  decayRate: number;          // デフォルト: 10%
  archiveThreshold: number;   // デフォルト: 30%
  maxConfidence: number;      // デフォルト: 95%
  incrementRate: number;      // デフォルト: 5%
}

export interface DecayResult {
  decayed: { pattern: string; from: number; to: number }[];
  archived: string[];
}

export class PatternDecayManager {
  constructor(
    private library: PatternLibrary,
    private config: DecayConfig
  ) {}

  /**
   * 使用時に信頼度を増加
   */
  incrementConfidence(patternId: string): void {
    const pattern = this.library.get(patternId);
    if (pattern) {
      const newConfidence = Math.min(
        pattern.confidence + this.config.incrementRate,
        this.config.maxConfidence
      );
      this.library.update(patternId, { confidence: newConfidence });
    }
  }

  /**
   * 全パターンに減衰を適用
   */
  async applyDecay(): Promise<DecayResult> {
    const result: DecayResult = { decayed: [], archived: [] };
    
    for (const pattern of this.library.list()) {
      if (!pattern.lastUsed || this.isStale(pattern.lastUsed)) {
        const newConfidence = pattern.confidence - this.config.decayRate;
        
        if (newConfidence < this.config.archiveThreshold) {
          await this.library.archive(pattern.id);
          result.archived.push(pattern.id);
        } else {
          this.library.update(pattern.id, { confidence: newConfidence });
          result.decayed.push({
            pattern: pattern.id,
            from: pattern.confidence,
            to: newConfidence,
          });
        }
      }
    }
    
    return result;
  }
}
```

---

### 3.6 DES-PTN-004: Pattern Recommender

**対応要件**: REQ-PTN-005, REQ-PTN-006

```typescript
// packages/pattern-mcp/src/recommender/pattern-recommender.ts

/**
 * コンテキストベースパターン推薦
 * @traceability REQ-PTN-005, REQ-PTN-006
 * 
 * 実装方針: MUSUBIX + Copilot連携
 * - MUSUBIX: プロジェクト構造解析、パターンライブラリ検索
 * - Copilot: 意味的マッチング強化（MCP経由）
 */
export interface ProjectContext {
  projectName: string;
  domain?: string;
  entities: string[];
  existingPatterns: string[];
  fileTypes: string[];
}

export interface PatternRecommendation {
  patternId: string;
  patternName: string;
  confidence: number;
  reason: string;
  applicableEntities: string[];
}

export class PatternRecommender {
  constructor(
    private library: PatternLibrary,
    private contextAnalyzer: ContextAnalyzer
  ) {}

  /**
   * プロジェクトコンテキストを解析
   */
  async analyzeContext(projectPath: string): Promise<ProjectContext>;

  /**
   * パターンを推薦
   */
  async recommend(context: ProjectContext): Promise<PatternRecommendation[]> {
    // 1. キーワードマッチング（MUSUBIX内部）
    const keywordMatches = this.matchByKeywords(context);
    
    // 2. 構造的マッチング（MUSUBIX内部）
    const structuralMatches = this.matchByStructure(context);
    
    // 3. スコア統合
    return this.mergeAndRank([...keywordMatches, ...structuralMatches]);
  }

  /**
   * パターンテンプレートを適用
   */
  async applyPattern(
    patternId: string,
    context: ProjectContext
  ): Promise<GeneratedFile[]>;

  /**
   * Copilot連携用コンテキスト出力
   */
  exportContextForCopilot(context: ProjectContext): string {
    return JSON.stringify({
      project: context.projectName,
      domain: context.domain,
      entities: context.entities,
      availablePatterns: this.library.list().map(p => ({
        id: p.id,
        name: p.name,
        description: p.description,
        confidence: p.confidence,
      })),
    }, null, 2);
  }
}
```

---

### 3.7 DES-EXD-001: Scaffold Expert Integrator

**対応要件**: REQ-EXD-001

#### 📝 ADR-v3.3.0-002: Expert統合エラーハンドリング

| 項目 | 内容 |
|------|------|
| **決定** | LLM応答タイムアウト時はfallbackでscaffold続行 |
| **タイムアウト** | 30秒（デフォルト） |
| **Fallback動作** | Expert分析なしで基本scaffoldを実行 |
| **ユーザー通知** | 警告メッセージを出力 |
| **状態** | **確定** |

```typescript
// packages/expert-delegation/src/integrators/scaffold-expert-integrator.ts

/**
 * Scaffold時のArchitect Expert統合
 * @traceability REQ-EXD-001
 */
export interface ScaffoldExpertOptions {
  entities: string[];
  domain: string;
  expertTypes: ('architect' | 'security')[];
}

export interface ArchitectAnalysis {
  suggestedEntities: string[];
  suggestedValueObjects: string[];
  recommendedPatterns: string[];
  c4Suggestions?: string;
}

export interface ExpertIntegrationConfig {
  timeoutMs: number;           // デフォルト: 30000 (30秒)
  fallbackOnTimeout: boolean;  // デフォルト: true
  retryCount: number;          // デフォルト: 1
}

export const DEFAULT_EXPERT_CONFIG: ExpertIntegrationConfig = {
  timeoutMs: 30000,
  fallbackOnTimeout: true,
  retryCount: 1,
};

export class ScaffoldExpertIntegrator {
  constructor(
    private delegationEngine: DelegationEngine,
    private expertManager: ExpertManager,
    private config: ExpertIntegrationConfig = DEFAULT_EXPERT_CONFIG
  ) {}

  /**
   * Architect Expertを呼び出してエンティティ分析
   * タイムアウト時はfallbackで空の分析結果を返す
   */
  async analyzeWithArchitect(
    options: ScaffoldExpertOptions
  ): Promise<ArchitectAnalysis> {
    const context: DelegationContext = {
      type: 'scaffold-analysis',
      domain: options.domain,
      entities: options.entities,
    };

    try {
      const result = await this.withTimeout(
        this.delegationEngine.delegate(
          'architect',
          this.buildAnalysisPrompt(options),
          context
        ),
        this.config.timeoutMs
      );

      return this.parseArchitectResponse(result);
    } catch (error) {
      if (this.isTimeoutError(error) && this.config.fallbackOnTimeout) {
        console.warn('⚠️ Expert analysis timed out. Proceeding with basic scaffold.');
        return this.getEmptyAnalysis();
      }
      throw error;
    }
  }

  /**
   * タイムアウト付きPromise実行
   */
  private withTimeout<T>(promise: Promise<T>, ms: number): Promise<T> {
    return Promise.race([
      promise,
      new Promise<T>((_, reject) =>
        setTimeout(() => reject(new ExpertTimeoutError(ms)), ms)
      ),
    ]);
  }

  /**
   * Fallback用の空分析結果
   */
  private getEmptyAnalysis(): ArchitectAnalysis {
    return {
      suggestedEntities: [],
      suggestedValueObjects: [],
      recommendedPatterns: [],
      c4Suggestions: undefined,
    };
  }

  private isTimeoutError(error: unknown): boolean {
    return error instanceof ExpertTimeoutError;
  }

  private buildAnalysisPrompt(options: ScaffoldExpertOptions): string {
    return `
Analyze the following domain model scaffold request:
Domain: ${options.domain}
Entities: ${options.entities.join(', ')}

Please suggest:
1. Additional entities that might be needed
2. Value Objects for domain concepts
3. Recommended design patterns
4. Entity relationships (for C4 component diagram)

Format your response as JSON.
`;
  }
}

export class ExpertTimeoutError extends Error {
  constructor(public readonly timeoutMs: number) {
    super(`Expert analysis timed out after ${timeoutMs}ms`);
    this.name = 'ExpertTimeoutError';
  }
}
```

---

### 3.8 DES-EXD-002: Security Expert Integrator

**対応要件**: REQ-EXD-002

```typescript
// packages/expert-delegation/src/integrators/security-expert-integrator.ts

/**
 * Scaffold時のSecurity Expert統合
 * @traceability REQ-EXD-002
 */
export interface SecurityAnalysis {
  warnings: SecurityWarning[];
  recommendations: SecurityRecommendation[];
  validationStatus: 'pass' | 'warn' | 'fail';
}

export interface SecurityWarning {
  entity: string;
  field?: string;
  severity: 'low' | 'medium' | 'high';
  message: string;
}

export class SecurityExpertIntegrator {
  constructor(
    private delegationEngine: DelegationEngine,
    private expertManager: ExpertManager
  ) {}

  /**
   * 生成コードのセキュリティレビュー
   */
  async reviewGeneratedCode(
    files: GeneratedFile[],
    context: ScaffoldExpertOptions
  ): Promise<SecurityAnalysis> {
    const codeContent = files.map(f => f.content).join('\n---\n');
    
    const result = await this.delegationEngine.delegate(
      'security-analyst',
      this.buildSecurityPrompt(codeContent, context),
      { type: 'security-review' }
    );

    return this.parseSecurityResponse(result);
  }

  private buildSecurityPrompt(code: string, context: ScaffoldExpertOptions): string {
    return `
Review the following generated code for security issues:
Domain: ${context.domain}
Entities: ${context.entities.join(', ')}

Code:
${code}

Check for:
1. Input validation completeness
2. Sensitive data handling (passwords, tokens, PII)
3. Authentication/Authorization patterns
4. Injection vulnerabilities

Format your response as JSON with warnings and recommendations.
`;
  }
}
```

---

### 3.9 DES-EXD-003: Expert Scaffold Prompt

**対応要件**: REQ-EXD-003  
**実装方式**: GitHub Copilotプロンプト（MUSUBIXコード実装対象外）

```typescript
// packages/mcp-server/src/prompts/sdd-expert-scaffold.ts

/**
 * Expert対話モード用プロンプト定義
 * @traceability REQ-EXD-003
 * 
 * 注: このプロンプトはMCPサーバー経由でCopilotに提供される。
 * 対話ロジック自体はCopilotが処理する。
 */
export const sddExpertScaffoldPrompt = {
  name: 'sdd_expert_scaffold',
  description: 'Interactive scaffold guidance with domain expert questions',
  arguments: [
    { name: 'projectName', description: 'Project name', required: true },
    { name: 'initialEntities', description: 'Initial entity list', required: false },
  ],
  template: `
You are a Domain-Driven Design expert helping to scaffold a new project.

Project: {{projectName}}
Initial entities: {{initialEntities}}

Before generating the scaffold, ask the user clarifying questions:

1. **Domain Context**: What is the primary business domain? (e.g., e-commerce, healthcare, logistics)

2. **Entity Relationships**: How do the entities relate to each other?
   - One-to-many? Many-to-many?
   - Are there aggregate roots?

3. **Status Transitions**: Do any entities have status/state machines?
   - If yes, what are the valid status transitions?

4. **Value Objects**: Are there domain concepts that should be Value Objects?
   - Examples: Money, Address, Email, DateRange

5. **Security Concerns**: Does this domain handle sensitive data?
   - User credentials?
   - Payment information?
   - Personal identifiable information (PII)?

After gathering answers, use the MUSUBIX scaffold command with appropriate options:
\`\`\`bash
npx musubix scaffold domain-model {{projectName}} \\
  -d DOMAIN \\
  -e "Entity1,Entity2" \\
  -v "ValueObject1,ValueObject2" \\
  -s "Entity1=draft"
\`\`\`
`,
};
```

---

### 3.10 DES-NFR-001: Performance Optimization

**対応要件**: REQ-NFR-001, REQ-NFR-002

```typescript
// packages/core/src/cli/utils/performance.ts

/**
 * 性能最適化ユーティリティ
 * @traceability REQ-NFR-001, REQ-NFR-002
 */
export interface PerformanceMetrics {
  scaffoldDuration: number;
  patternSearchDuration: number;
  fileWriteDuration: number;
}

export class PerformanceOptimizer {
  /**
   * 並列ファイル生成
   */
  async generateFilesParallel(
    generators: (() => Promise<GeneratedFile>)[],
    concurrency: number = 5
  ): Promise<GeneratedFile[]>;

  /**
   * パターンライブラリのインデックス化
   */
  buildPatternIndex(patterns: Pattern[]): PatternIndex;

  /**
   * インデックス検索（O(1)〜O(log n)）
   */
  searchPatternIndex(index: PatternIndex, query: string): Pattern[];
}

// 性能目標
const PERFORMANCE_TARGETS = {
  scaffold: {
    entities5: 2000,   // ms
    entities10: 5000,  // ms
  },
  patternSearch: {
    patterns100: 20,   // ms
    patterns500: 50,   // ms
    patterns1000: 100, // ms
  },
};
```

---

### 3.11 DES-NFR-002: Backward Compatibility

**対応要件**: REQ-NFR-003

```typescript
// packages/core/src/cli/utils/compatibility.ts

/**
 * 後方互換性管理
 * @traceability REQ-NFR-003
 */
export interface CompatibilityCheck {
  version: string;
  isCompatible: boolean;
  migrationRequired: boolean;
  migrationSteps?: string[];
}

export class CompatibilityManager {
  /**
   * v3.2.0プロジェクトの互換性チェック
   */
  checkProjectCompatibility(projectPath: string): Promise<CompatibilityCheck>;

  /**
   * v3.2.0学習データの互換性チェック
   */
  checkLearningDataCompatibility(dataPath: string): Promise<CompatibilityCheck>;

  /**
   * 必要に応じてマイグレーション実行
   */
  migrate(path: string, fromVersion: string): Promise<void>;
}

// 互換性マトリクス
const COMPATIBILITY_MATRIX = {
  'v3.2.0': {
    scaffold: 'compatible',
    learningData: 'compatible',
    cli: 'compatible',
  },
  'v3.1.0': {
    scaffold: 'compatible',
    learningData: 'migration-required',
    cli: 'compatible',
  },
};
```

---

## 4. データフロー図

### 4.1 Scaffold Enhanced Flow

```
┌──────────────┐
│ CLI Input    │
│ -e -v -s     │
└──────┬───────┘
       │
       ▼
┌──────────────┐     ┌──────────────┐
│ Option       │────▶│ ValueObject  │
│ Parser       │     │ Generator    │
└──────────────┘     └──────┬───────┘
       │                    │
       │              ┌─────▼──────┐
       │              │ StatusMachine│
       │              │ Generator   │
       │              └─────┬──────┘
       │                    │
       ▼                    ▼
┌──────────────┐     ┌──────────────┐
│ Entity       │────▶│ Result       │
│ Generator    │     │ Aggregator   │
└──────────────┘     └──────┬───────┘
                            │
                            ▼
                     ┌──────────────┐
                     │ Pattern Auto │
                     │ Extractor    │
                     └──────┬───────┘
                            │
                            ▼
                     ┌──────────────┐
                     │ Pattern      │
                     │ Library      │
                     └──────────────┘
```

### 4.2 Pattern Recommendation Flow

```
┌──────────────┐
│ learn        │
│ recommend    │
└──────┬───────┘
       │
       ▼
┌──────────────┐
│ Context      │
│ Analyzer     │
└──────┬───────┘
       │
       ├───────────────┐
       ▼               ▼
┌──────────────┐ ┌──────────────┐
│ Keyword      │ │ Structural   │
│ Matcher      │ │ Matcher      │
└──────┬───────┘ └──────┬───────┘
       │               │
       └───────┬───────┘
               ▼
        ┌──────────────┐
        │ Score        │
        │ Merger       │
        └──────┬───────┘
               │
               ▼
        ┌──────────────┐
        │ Recommendation│
        │ Output       │
        └──────────────┘
               │
               ▼ (optional)
        ┌──────────────┐
        │ Copilot      │
        │ Enhancement  │
        └──────────────┘
```

---

## 5. ファイル構成

### 5.1 変更・追加ファイル一覧

```
packages/core/src/cli/
├── generators/                      # NEW directory
│   ├── index.ts                     # NEW
│   ├── value-object-generator.ts    # NEW (DES-SCF-001)
│   ├── status-machine-generator.ts  # NEW (DES-SCF-002)
│   └── scaffold-result-aggregator.ts # NEW (DES-SCF-003)
├── commands/
│   └── scaffold.ts                  # MODIFIED
└── utils/
    ├── performance.ts               # NEW (DES-NFR-001)
    └── compatibility.ts             # NEW (DES-NFR-002)

packages/pattern-mcp/src/
├── extractor/
│   └── auto-extractor.ts            # NEW (DES-PTN-001)
├── library/
│   └── pattern-decay-manager.ts     # NEW (DES-PTN-003)
└── recommender/                     # NEW directory
    └── pattern-recommender.ts       # NEW (DES-PTN-004)

packages/expert-delegation/src/
└── integrators/                     # NEW directory
    ├── index.ts                     # NEW
    ├── scaffold-expert-integrator.ts # NEW (DES-EXD-001)
    └── security-expert-integrator.ts # NEW (DES-EXD-002)

packages/mcp-server/src/
└── prompts/
    └── sdd-expert-scaffold.ts       # NEW (DES-EXD-003)
```

### 5.2 テストファイル一覧

```
packages/core/src/cli/generators/__tests__/
├── value-object-generator.test.ts
├── status-machine-generator.test.ts
└── scaffold-result-aggregator.test.ts

packages/pattern-mcp/src/__tests__/
├── auto-extractor.test.ts
├── pattern-decay-manager.test.ts
└── pattern-recommender.test.ts

packages/expert-delegation/src/__tests__/
├── scaffold-expert-integrator.test.ts
└── security-expert-integrator.test.ts
```

---

## 6. トレーサビリティマトリクス

| 要件ID | 設計ID | コンポーネント | ファイル |
|--------|--------|---------------|----------|
| REQ-SCF-001 | DES-SCF-001 | ValueObjectGenerator | value-object-generator.ts |
| REQ-SCF-002 | DES-SCF-001 | ValueObjectGenerator | value-object-generator.ts |
| REQ-SCF-003 | DES-SCF-002 | StatusMachineGenerator | status-machine-generator.ts |
| REQ-SCF-004 | DES-SCF-002 | StatusMachineGenerator | status-machine-generator.ts |
| REQ-SCF-005 | DES-SCF-003 | ScaffoldResultAggregator | scaffold-result-aggregator.ts |
| REQ-SCF-006 | DES-SCF-003 | ScaffoldResultAggregator | scaffold-result-aggregator.ts |
| REQ-PTN-001 | DES-PTN-001 | PatternAutoExtractor | auto-extractor.ts |
| REQ-PTN-002 | DES-PTN-001 | PatternAutoExtractor | auto-extractor.ts |
| REQ-PTN-003 | DES-PTN-003 | PatternDecayManager | pattern-decay-manager.ts |
| REQ-PTN-004 | DES-PTN-003 | PatternDecayManager | pattern-decay-manager.ts |
| REQ-PTN-005 | DES-PTN-004 | PatternRecommender | pattern-recommender.ts |
| REQ-PTN-006 | DES-PTN-004 | PatternRecommender | pattern-recommender.ts |
| REQ-EXD-001 | DES-EXD-001 | ScaffoldExpertIntegrator | scaffold-expert-integrator.ts |
| REQ-EXD-002 | DES-EXD-002 | SecurityExpertIntegrator | security-expert-integrator.ts |
| REQ-EXD-003 | DES-EXD-003 | sddExpertScaffoldPrompt | sdd-expert-scaffold.ts |
| REQ-EXD-004 | DES-EXD-004 | (P2: v3.4.0) | - |
| REQ-EXD-005 | DES-EXD-004 | (P2: v3.4.0) | - |
| REQ-NFR-001 | DES-NFR-001 | PerformanceOptimizer | performance.ts |
| REQ-NFR-002 | DES-NFR-001 | PerformanceOptimizer | performance.ts |
| REQ-NFR-003 | DES-NFR-002 | CompatibilityManager | compatibility.ts |

**注**: REQ-EXD-003はプロンプト定義のみ。MUSUBIXユニットテストの対象外。

---

## 7. 承認

| 役割 | 氏名 | 日付 | 署名 |
|------|------|------|------|
| 作成者 | AI Agent | 2026-01-14 | ✓ |
| レビュアー | | | |
| 承認者 | | | |

---

**文書終了**
