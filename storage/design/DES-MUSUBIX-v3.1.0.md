# MUSUBIX v3.1.0 設計書
# C4モデル準拠

**文書ID**: DES-MUSUBIX-v3.1.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-13  
**ステータス**: Draft  
**準拠規格**: C4 Model（Context, Container, Component, Code）  
**参照文書**: REQ-MUSUBIX-v3.1.0.md

---

## 1. 文書概要

### 1.1 目的

本文書は、MUSUBIX v3.1.0の設計をC4モデルに基づいて定義する。REQ-MUSUBIX-v3.1.0.mdで定義された15要件（P0: 4件、P1: 10件、P2: 1件）の実装設計を記述する。

### 1.2 設計ID体系

```
DES-<カテゴリ>-<連番>
```

| カテゴリ | 説明 |
|---------|------|
| CLI | コマンドラインインターフェース設計 |
| VAL | 検証機能設計 |
| LRN | 学習機能設計 |
| PAT | パターンライブラリ設計 |
| GEN | コード生成設計 |
| TST | テスト生成設計 |
| NFR | 非機能要件設計 |

---

## 2. C4 Context（システムコンテキスト）

```
┌─────────────────────────────────────────────────────────────────┐
│                        External Systems                          │
├─────────────────────────────────────────────────────────────────┤
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐        │
│  │Developer │  │ Claude   │  │  GitHub  │  │   npm    │        │
│  │  (User)  │  │  Code    │  │  Actions │  │ Registry │        │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘        │
│       │             │             │             │               │
│       ▼             ▼             ▼             ▼               │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                    MUSUBIX v3.1.0                        │   │
│  │  ┌─────────────────────────────────────────────────────┐│   │
│  │  │ CLI Layer (musubix)                                 ││   │
│  │  │  - init, requirements, design, codegen, learn, etc. ││   │
│  │  └─────────────────────────────────────────────────────┘│   │
│  │  ┌─────────────────────────────────────────────────────┐│   │
│  │  │ MCP Server Layer (@nahisaho/musubix-mcp-server)     ││   │
│  │  │  - 96 Tools, 5 Prompts                              ││   │
│  │  └─────────────────────────────────────────────────────┘│   │
│  │  ┌─────────────────────────────────────────────────────┐│   │
│  │  │ Core Packages                                        ││   │
│  │  │  - core, security, formal-verify, pattern-mcp, etc. ││   │
│  │  └─────────────────────────────────────────────────────┘│   │
│  └─────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
```

---

## 3. C4 Container（コンテナ設計）

### 3.1 影響を受けるコンテナ

| コンテナ | パッケージ | 変更種別 | 関連要件 |
|---------|-----------|----------|----------|
| **CLI** | `packages/core/src/cli/` | 機能追加・修正 | REQ-CLI-001〜003 |
| **Validators** | `packages/core/src/validators/` | 機能追加 | REQ-VAL-001〜002 |
| **Learning** | `packages/core/src/learning/` | 機能追加 | REQ-LRN-001〜002 |
| **Pattern Library** | `packages/pattern-mcp/` | パターン追加 | REQ-PAT-001〜002 |
| **Code Generator** | `packages/core/src/codegen/` | 機能追加 | REQ-GEN-001〜002 |
| **Test Generator** | `packages/core/src/codegen/` | 機能追加 | REQ-TST-001〜002 |

---

## 4. C4 Component（コンポーネント設計）

---

### 4.1 CLI機能設計

---

#### DES-CLI-001: initコマンドパス正規化

| 属性 | 値 |
|------|-----|
| **ID** | DES-CLI-001 |
| **対象要件** | REQ-CLI-001 |
| **変更ファイル** | `packages/core/src/cli/commands/init.ts` |
| **設計パターン** | Command Pattern, Path Normalization |

**コンポーネント図**:

```
┌─────────────────────────────────────────────────────────┐
│ InitCommand                                              │
├─────────────────────────────────────────────────────────┤
│ + execute(path: string, options: InitOptions): void     │
│ - normalizePath(inputPath: string): string  [NEW]       │
│ - isAbsolutePath(path: string): boolean     [NEW]       │
│ - validatePath(path: string): Result<string, PathError> │
└─────────────────────────────────────────────────────────┘
```

**設計詳細**:

```typescript
// packages/core/src/cli/commands/init.ts

interface PathNormalizationResult {
  normalizedPath: string;
  wasAbsolute: boolean;
  originalPath: string;
}

function normalizePath(inputPath: string, cwd: string): Result<PathNormalizationResult, PathError> {
  // 1. 絶対パス判定
  const isAbsolute = path.isAbsolute(inputPath);
  
  // 2. 絶対パスの場合はそのまま使用（cwdとの連結を回避）
  if (isAbsolute) {
    return ok({
      normalizedPath: path.normalize(inputPath),
      wasAbsolute: true,
      originalPath: inputPath,
    });
  }
  
  // 3. 相対パスの場合はcwdと結合
  return ok({
    normalizedPath: path.resolve(cwd, inputPath),
    wasAbsolute: false,
    originalPath: inputPath,
  });
}
```

**受入基準マッピング**:

| 受入基準 | 実装箇所 |
|---------|---------|
| AC-001-1 | `normalizePath()` - 絶対パス分岐 |
| AC-001-2 | `normalizePath()` - 相対パス分岐 |
| AC-001-3 | `execute()` - options.force対応 |
| AC-001-4 | `validatePath()` - エラーメッセージ生成 |

**後方互換性・移行ガイド**:

| 観点 | 対応 |
|------|------|
| 既存動作 | 相対パス指定時の動作は変更なし |
| 破壊的変更 | 絶対パス指定時の二重連結バグを修正（バグ修正であり仕様変更ではない） |
| 移行手順 | 不要（修正は透過的） |
| テスト | 既存テストに絶対パスケースを追加 |

```typescript
// 移行不要: 修正は透過的
// 既存スクリプトが絶対パスを使用している場合、修正後は正しく動作する
// Before (バグ): musubix init /home/user/project → /cwd/home/user/project
// After (修正): musubix init /home/user/project → /home/user/project
```

---

#### DES-CLI-002: feedbackコマンドガイダンス

| 属性 | 値 |
|------|-----|
| **ID** | DES-CLI-002 |
| **対象要件** | REQ-CLI-002 |
| **変更ファイル** | `packages/core/src/cli/commands/learn.ts` |
| **設計パターン** | Command Pattern, Builder Pattern (Interactive) |

**コンポーネント図**:

```
┌─────────────────────────────────────────────────────────┐
│ LearnFeedbackCommand                                     │
├─────────────────────────────────────────────────────────┤
│ + execute(id: string, options: FeedbackOptions): void   │
│ - validateRequiredOptions(options): Result<void, Error> │
│ - showGuidance(missingOptions: string[]): void  [NEW]   │
│ - runInteractiveMode(): Promise<FeedbackOptions> [NEW]  │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ InteractiveFeedbackBuilder                     [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + promptArtifactType(): Promise<ArtifactType>           │
│ + promptFeedbackType(): Promise<FeedbackType>           │
│ + promptReason(): Promise<string>                       │
│ + build(): FeedbackOptions                               │
└─────────────────────────────────────────────────────────┘
```

**設計詳細**:

```typescript
// packages/core/src/cli/commands/learn.ts

// Commanderオプション定義の修正
program
  .command('feedback <artifact-id>')
  .option('-t, --type <type>', 'Feedback type: accept|reject|modify')
  .option('-a, --artifact-type <type>', 'Artifact type: design|code|test')  // エイリアス追加
  .option('-r, --reason <reason>', 'Reason for feedback')
  .option('-i, --interactive', 'Interactive mode')  // 新規追加
  .action(async (artifactId, options) => {
    if (options.interactive) {
      const builder = new InteractiveFeedbackBuilder();
      options = await builder.build();
    }
    
    const validation = validateRequiredOptions(options);
    if (validation.isErr()) {
      showGuidance(validation.error.missingOptions);
      process.exit(1);
    }
    // ...
  });

function showGuidance(missingOptions: string[]): void {
  console.error(chalk.red('Error: Missing required options'));
  console.error('');
  console.error(chalk.yellow('Required:'));
  for (const opt of missingOptions) {
    console.error(`  ${opt}`);
  }
  console.error('');
  console.error(chalk.cyan('Example:'));
  console.error('  musubix learn feedback "DES-001" -t accept -a design -r "LGTM"');
  console.error('');
  console.error(chalk.gray("Run 'musubix learn feedback --help' for more information."));
}
```

**受入基準マッピング**:

| 受入基準 | 実装箇所 |
|---------|---------|
| AC-002-1 | `showGuidance()` |
| AC-002-2 | Commander `-a` エイリアス定義 |
| AC-002-3 | `InteractiveFeedbackBuilder` |

---

#### DES-CLI-003: scaffoldドメインモデル生成

| 属性 | 値 |
|------|-----|
| **ID** | DES-CLI-003 |
| **対象要件** | REQ-CLI-003 |
| **変更ファイル** | `packages/core/src/cli/commands/scaffold.ts` |
| **設計パターン** | Factory Pattern, Template Method Pattern |

**コンポーネント図**:

```
┌─────────────────────────────────────────────────────────┐
│ ScaffoldDomainModelCommand                               │
├─────────────────────────────────────────────────────────┤
│ + execute(name: string, options: ScaffoldOptions): void │
│ - parseEntities(entityList: string): string[]           │
│ - generateEntity(name: string): GeneratedFiles  [NEW]   │
│ - applyPatterns(entity: EntityDef): EntityDef   [NEW]   │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ EntityTemplateFactory                          [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + createBrandedId(entityName: string): string           │
│ + createInputDTO(entityName: string): string            │
│ + createFactory(entityName: string): string             │
│ + createResultTypes(entityName: string): string         │
│ + createTestFile(entityName: string): string            │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ PatternApplicator                              [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + applyBPCODE001(entity: EntityDef): EntityDef          │
│ + applyBPCODE002(entity: EntityDef): EntityDef          │
│ + applyBPCODE004(entity: EntityDef): EntityDef          │
│ + applyBPCODE005(entity: EntityDef): EntityDef          │
└─────────────────────────────────────────────────────────┘
```

**生成テンプレート例**:

```typescript
// EntityTemplateFactory.createBrandedId()
export function generateEntityTemplate(entityName: string): string {
  const pascalName = toPascalCase(entityName);
  const camelName = toCamelCase(entityName);
  
  return `
// ${entityName}.ts
// Generated by MUSUBIX scaffold domain-model
// Patterns: BP-CODE-001, BP-CODE-002, BP-CODE-004, BP-CODE-005

// === Branded ID (BP-CODE-002) ===
export type ${pascalName}Id = string & { readonly _brand: '${pascalName}Id' };

let ${camelName}Counter = 0;

export function generate${pascalName}Id(): ${pascalName}Id {
  const today = new Date().toISOString().slice(0, 10).replace(/-/g, '');
  ${camelName}Counter++;
  return \`${pascalName.toUpperCase()}-\${today}-\${String(${camelName}Counter).padStart(3, '0')}\` as ${pascalName}Id;
}

export function reset${pascalName}Counter(): void {
  ${camelName}Counter = 0;
}

// === Input DTO (BP-CODE-001) ===
export interface ${pascalName}Input {
  // TODO: Define input fields
}

// === Result Type (BP-CODE-005) ===
export type ${pascalName}Result<T> = 
  | { ok: true; value: T }
  | { ok: false; error: ${pascalName}Error };

export interface ${pascalName}Error {
  code: string;
  message: string;
}

// === Factory Function (BP-CODE-004) ===
export interface ${pascalName} {
  readonly id: ${pascalName}Id;
  readonly createdAt: Date;
  readonly updatedAt: Date;
  // TODO: Define entity fields
}

export function create${pascalName}(input: ${pascalName}Input): ${pascalName}Result<${pascalName}> {
  // TODO: Implement validation and creation logic
  const id = generate${pascalName}Id();
  const now = new Date();
  
  return {
    ok: true,
    value: {
      id,
      createdAt: now,
      updatedAt: now,
    },
  };
}
`;
}
```

**受入基準マッピング**:

| 受入基準 | 実装箇所 |
|---------|---------|
| AC-003-1 | `EntityTemplateFactory` |
| AC-003-2 | `EntityTemplateFactory.createTestFile()` |
| AC-003-3 | `PatternApplicator.applyBPCODE005()` |
| AC-003-4 | `PatternApplicator.applyBPCODE002()` |
| AC-003-5 | テストテンプレート - beforeEach |

---

### 4.2 検証機能設計

---

#### DES-VAL-001: Markdown内EARS検出

| 属性 | 値 |
|------|-----|
| **ID** | DES-VAL-001 |
| **対象要件** | REQ-VAL-001 |
| **変更ファイル** | `packages/core/src/validators/ears-validator.ts` |
| **設計パターン** | Strategy Pattern, Parser Combinator |

**コンポーネント図**:

```
┌─────────────────────────────────────────────────────────┐
│ EarsValidator                                            │
├─────────────────────────────────────────────────────────┤
│ + validate(content: string): EarsValidationResult       │
│ - detectMarkdownContext(line: string): MarkdownContext  │
│ - parseEarsInTable(tableContent: string): EarsReq[]     │
│ - parseEarsInList(listContent: string): EarsReq[]       │
│ - isCodeBlock(line: string, state: ParserState): bool   │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ MarkdownEarsParser                             [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + parse(markdown: string): ParsedRequirement[]          │
│ - parseTable(lines: string[]): TableRequirement[]       │
│ - parseBulletList(lines: string[]): ListRequirement[]   │
│ - parseBlockquote(lines: string[]): QuoteRequirement[]  │
│ - skipCodeBlocks(lines: string[]): string[]             │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ EarsPatternMatcher                                       │
├─────────────────────────────────────────────────────────┤
│ + matchUbiquitous(text: string): EarsMatch | null       │
│ + matchEventDriven(text: string): EarsMatch | null      │
│ + matchStateDriven(text: string): EarsMatch | null      │
│ + matchUnwanted(text: string): EarsMatch | null         │
│ + matchOptional(text: string): EarsMatch | null         │
└─────────────────────────────────────────────────────────┘
```

**設計詳細**:

```typescript
// packages/core/src/validators/markdown-ears-parser.ts

interface ParsedRequirement {
  id?: string;
  pattern: EarsPattern;
  text: string;
  lineNumber: number;
  context: 'table' | 'list' | 'blockquote' | 'paragraph';
}

class MarkdownEarsParser {
  parse(markdown: string): ParsedRequirement[] {
    const lines = markdown.split('\n');
    const requirements: ParsedRequirement[] = [];
    let inCodeBlock = false;
    let codeBlockDelimiter = '';
    
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      
      // コードブロック検出（スキップ）
      if (line.startsWith('```') || line.startsWith('~~~')) {
        if (!inCodeBlock) {
          inCodeBlock = true;
          codeBlockDelimiter = line.slice(0, 3);
        } else if (line.startsWith(codeBlockDelimiter)) {
          inCodeBlock = false;
        }
        continue;
      }
      
      if (inCodeBlock) continue;
      
      // テーブル行検出
      if (line.includes('|') && this.isTableRow(line)) {
        const tableReqs = this.parseTableRow(line, i + 1);
        requirements.push(...tableReqs);
        continue;
      }
      
      // 箇条書き検出
      if (line.match(/^[\s]*[-*+]\s+/)) {
        const listReqs = this.parseListItem(line, i + 1);
        requirements.push(...listReqs);
        continue;
      }
      
      // 通常テキスト
      const paragraphReqs = this.parseParagraph(line, i + 1);
      requirements.push(...paragraphReqs);
    }
    
    return requirements;
  }
}
```

**受入基準マッピング**:

| 受入基準 | 実装箇所 |
|---------|---------|
| AC-004-1 | `parseTableRow()` |
| AC-004-2 | `parseListItem()` |
| AC-004-3 | コードブロック検出ロジック |
| AC-004-4 | `ParsedRequirement` インターフェース |

---

#### DES-VAL-002: 設計トレーサビリティ検証

| 属性 | 値 |
|------|-----|
| **ID** | DES-VAL-002 |
| **対象要件** | REQ-VAL-002 |
| **変更ファイル** | `packages/core/src/cli/commands/design.ts`, `packages/core/src/validators/traceability-validator.ts` |
| **設計パターン** | Visitor Pattern, Graph Analysis |

**コンポーネント図**:

```
┌─────────────────────────────────────────────────────────┐
│ DesignValidateCommand                          [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + execute(options: ValidateOptions): void               │
│ - loadRequirements(specsDir: string): Requirement[]     │
│ - loadDesigns(designDir: string): Design[]              │
│ - buildTraceabilityGraph(): TraceabilityGraph           │
│ - reportResults(result: TraceabilityResult): void       │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ TraceabilityValidator                          [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + validate(reqs: Req[], designs: Design[]): Result      │
│ - findOrphanRequirements(): Requirement[]               │
│ - findOrphanDesigns(): Design[]                         │
│ - calculateCoverage(): number                           │
└─────────────────────────────────────────────────────────┘
```

**設計詳細**:

```typescript
// packages/core/src/validators/traceability-validator.ts

interface TraceabilityResult {
  orphanRequirements: Requirement[];
  orphanDesigns: Design[];
  linkedPairs: Array<{ req: Requirement; design: Design }>;
  coverage: number;  // 0-100%
}

class TraceabilityValidator {
  validate(requirements: Requirement[], designs: Design[]): TraceabilityResult {
    const reqIds = new Set(requirements.map(r => r.id));
    const designReqRefs = new Map<string, string[]>();
    
    // 設計から参照されている要件IDを抽出
    for (const design of designs) {
      const refs = this.extractReqReferences(design);
      designReqRefs.set(design.id, refs);
    }
    
    // 孤立要件（どの設計からも参照されていない）
    const referencedReqIds = new Set(
      Array.from(designReqRefs.values()).flat()
    );
    const orphanRequirements = requirements.filter(
      r => !referencedReqIds.has(r.id)
    );
    
    // 過剰設計（存在しない要件を参照）
    const orphanDesigns = designs.filter(d => {
      const refs = designReqRefs.get(d.id) || [];
      return refs.some(ref => !reqIds.has(ref));
    });
    
    // カバレッジ計算
    const coverage = (referencedReqIds.size / reqIds.size) * 100;
    
    return {
      orphanRequirements,
      orphanDesigns,
      linkedPairs: this.buildLinkedPairs(requirements, designs, designReqRefs),
      coverage,
    };
  }
}
```

---

### 4.3 学習機能設計

---

#### DES-LRN-001: パターン推薦ガイダンス

| 属性 | 値 |
|------|-----|
| **ID** | DES-LRN-001 |
| **対象要件** | REQ-LRN-001 |
| **変更ファイル** | `packages/core/src/learning/pattern-recommender.ts` |
| **設計パターン** | Strategy Pattern, Recommendation Engine |

**コンポーネント図**:

```
┌─────────────────────────────────────────────────────────┐
│ PatternRecommender                             [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + recommend(context: FileContext): Recommendation[]     │
│ - analyzeFileType(filePath: string): FileType           │
│ - matchPatterns(context: Context): Pattern[]            │
│ - rankByConfidence(patterns: Pattern[]): Pattern[]      │
│ - generateSnippet(pattern: Pattern): string             │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ Recommendation                                           │
├─────────────────────────────────────────────────────────┤
│ + pattern: Pattern                                       │
│ + confidence: number                                     │
│ + reason: string                                         │
│ + snippet: string                                        │
│ + usageCount: number                                     │
└─────────────────────────────────────────────────────────┘
```

---

#### DES-LRN-002: ドメイン固有パターン学習

| 属性 | 値 |
|------|-----|
| **ID** | DES-LRN-002 |
| **対象要件** | REQ-LRN-002 |
| **変更ファイル** | `packages/core/src/learning/domain-pattern-classifier.ts` |
| **設計パターン** | Classification Pattern, Tag-based Filtering |

**コンポーネント図**:

```
┌─────────────────────────────────────────────────────────┐
│ DomainPatternClassifier                        [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + classify(pattern: Pattern, usages: Usage[]): Domain   │
│ + getDomainsForPattern(patternId: string): Domain[]     │
│ + recommendByDomain(domain: Domain): Pattern[]          │
│ - calculateDomainAffinity(usages: Usage[]): DomainScore │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ DomainRegistry                                 [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + domains: Map<DomainId, DomainDefinition>              │
│ + patternDomainMap: Map<PatternId, DomainId[]>          │
│ + addDomainTag(patternId: string, domain: Domain): void │
│ + getDomainPatterns(domain: Domain): Pattern[]          │
└─────────────────────────────────────────────────────────┘
```

---

### 4.4 パターンライブラリ設計

---

#### DES-PAT-001: 同時実行パターン追加

| 属性 | 値 |
|------|-----|
| **ID** | DES-PAT-001 |
| **対象要件** | REQ-PAT-001 |
| **変更ファイル** | `packages/pattern-mcp/src/patterns/concurrency/` |
| **設計パターン** | Pattern Catalog |

**パターン定義**:

```typescript
// packages/pattern-mcp/src/patterns/concurrency/index.ts

export const concurrencyPatterns: PatternDefinition[] = [
  {
    id: 'PAT-CONC-001',
    name: 'Optimistic Locking',
    category: 'concurrency',
    description: '楽観的ロック - バージョン番号による競合検出',
    template: `
interface VersionedEntity {
  id: string;
  version: number;
  // ...other fields
}

function updateWithOptimisticLock<T extends VersionedEntity>(
  entity: T,
  updates: Partial<T>,
  currentVersion: number
): Result<T, ConcurrencyError> {
  if (entity.version !== currentVersion) {
    return err({ code: 'CONCURRENT_MODIFICATION', message: 'Entity was modified' });
  }
  return ok({ ...entity, ...updates, version: entity.version + 1 });
}
    `,
    guidance: 'Read-heavy workloads with rare conflicts',
  },
  {
    id: 'PAT-CONC-002',
    name: 'Pessimistic Locking',
    // ...
  },
  {
    id: 'PAT-CONC-003',
    name: 'Hold Pattern',
    // ...
  },
  {
    id: 'PAT-CONC-004',
    name: 'Idempotency Key',
    // ...
  },
];
```

---

#### DES-PAT-002: 時間制約パターン追加

| 属性 | 値 |
|------|-----|
| **ID** | DES-PAT-002 |
| **対象要件** | REQ-PAT-002 |
| **変更ファイル** | `packages/pattern-mcp/src/patterns/time/` |
| **設計パターン** | Pattern Catalog |

**パターン定義**:

```typescript
// packages/pattern-mcp/src/patterns/time/index.ts

export const timePatterns: PatternDefinition[] = [
  {
    id: 'PAT-TIME-001',
    name: 'Expiry Check',
    category: 'time',
    description: '有効期限チェック',
    template: `
interface Expirable {
  expiresAt: Date;
}

function isExpired(entity: Expirable, now: Date = new Date()): boolean {
  return entity.expiresAt <= now;
}

function getRemainingTime(entity: Expirable, now: Date = new Date()): number {
  return Math.max(0, entity.expiresAt.getTime() - now.getTime());
}
    `,
  },
  {
    id: 'PAT-TIME-002',
    name: 'Scheduled Action',
    // ...
  },
  {
    id: 'PAT-TIME-003',
    name: 'Interval Management',
    // ...
  },
  {
    id: 'PAT-TIME-004',
    name: 'Streak Calculation',
    // ...
  },
];
```

---

### 4.5 コード生成設計

---

#### DES-GEN-001: Value Object自動生成

| 属性 | 値 |
|------|-----|
| **ID** | DES-GEN-001 |
| **対象要件** | REQ-GEN-001 |
| **変更ファイル** | `packages/core/src/codegen/vo-generator.ts` |
| **設計パターン** | Factory Pattern, Template Pattern |

**コンポーネント図**:

```
┌─────────────────────────────────────────────────────────┐
│ ValueObjectGenerator                           [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + generate(name: string, type: VOType): GeneratedCode   │
│ - selectTemplate(type: VOType): VOTemplate              │
│ - applyBPCODE004(template: VOTemplate): string          │
│ - applyBPCODE005(template: VOTemplate): string          │
│ - generateValidation(type: VOType): string              │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ VOTemplateRegistry                             [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + templates: Map<VOType, VOTemplate>                    │
│ + register(type: VOType, template: VOTemplate): void    │
│ + get(type: VOType): VOTemplate                         │
└─────────────────────────────────────────────────────────┘
```

---

#### DES-GEN-002: Status Transition Map生成

| 属性 | 値 |
|------|-----|
| **ID** | DES-GEN-002 |
| **対象要件** | REQ-GEN-002 |
| **変更ファイル** | `packages/core/src/codegen/status-generator.ts` |
| **設計パターン** | State Machine Pattern, Code Generation |

**コンポーネント図**:

```
┌─────────────────────────────────────────────────────────┐
│ StatusTransitionGenerator                      [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + generate(entity: string, states: string[]): Generated │
│ - buildTransitionMap(states: string[]): TransitionMap   │
│ - generateTransitionFunction(): string                  │
│ - generateMermaidDiagram(map: TransitionMap): string    │
└─────────────────────────────────────────────────────────┘
```

---

### 4.6 テスト生成設計

---

#### DES-TST-001: Status Transitionテスト生成

| 属性 | 値 |
|------|-----|
| **ID** | DES-TST-001 |
| **対象要件** | REQ-TST-001 |
| **変更ファイル** | `packages/core/src/codegen/test-generator.ts` |
| **設計パターン** | Template Pattern, Test Matrix |

**コンポーネント図**:

```
┌─────────────────────────────────────────────────────────┐
│ StatusTransitionTestGenerator                  [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + generate(entity: string, transitions: Map): TestCode  │
│ - generateValidTransitionTests(): string                │
│ - generateInvalidTransitionTests(): string              │
│ - generateTerminalStateTests(): string                  │
│ - buildTestMatrix(transitions: Map): TestCase[]         │
└─────────────────────────────────────────────────────────┘
```

**設計詳細**:

```typescript
// packages/core/src/codegen/test-generator.ts

interface TestCase {
  from: string;
  to: string;
  expected: 'valid' | 'invalid';
  description: string;
}

class StatusTransitionTestGenerator {
  generate(entityName: string, transitions: Map<string, string[]>): string {
    const testCases = this.buildTestMatrix(transitions);
    const validTests = this.generateValidTransitionTests(entityName, testCases);
    const invalidTests = this.generateInvalidTransitionTests(entityName, testCases);
    const terminalTests = this.generateTerminalStateTests(entityName, transitions);
    
    return `
describe('${entityName} Status Transitions', () => {
  ${validTests}
  
  ${invalidTests}
  
  ${terminalTests}
});
    `;
  }
  
  private buildTestMatrix(transitions: Map<string, string[]>): TestCase[] {
    const allStates = Array.from(transitions.keys());
    const testCases: TestCase[] = [];
    
    for (const from of allStates) {
      const validTargets = transitions.get(from) || [];
      for (const to of allStates) {
        if (from === to) continue;
        testCases.push({
          from,
          to,
          expected: validTargets.includes(to) ? 'valid' : 'invalid',
          description: `${from} → ${to}`,
        });
      }
    }
    return testCases;
  }
}
```

**受入基準マッピング**:

| 受入基準 | 実装箇所 |
|---------|---------||
| AC-012-1 | `generateValidTransitionTests()` |
| AC-012-2 | `generateInvalidTransitionTests()` |
| AC-012-3 | `generateTerminalStateTests()` |

---

#### DES-TST-002: カウンターリセット自動挿入

| 属性 | 値 |
|------|-----|
| **ID** | DES-TST-002 |
| **対象要件** | REQ-TST-002 |
| **変更ファイル** | `packages/core/src/codegen/test-generator.ts` |
| **設計パターン** | Decorator Pattern |

**コンポーネント図**:

```
┌─────────────────────────────────────────────────────────┐
│ TestFileDecorator                              [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + decorate(testCode: string, options: Options): string  │
│ - injectBeforeEach(code: string): string                │
│ - detectCounterResets(entityName: string): string[]     │
│ - generateResetCalls(resets: string[]): string          │
└─────────────────────────────────────────────────────────┘
```

**設計詳細**:

```typescript
// packages/core/src/codegen/test-generator.ts

class TestFileDecorator {
  decorate(testCode: string, entityNames: string[]): string {
    const resetCalls = this.detectCounterResets(entityNames);
    const beforeEachBlock = this.generateBeforeEach(resetCalls);
    
    // describe ブロックの先頭に beforeEach を挿入
    return testCode.replace(
      /describe\(['"](.+?)['"],\s*\(\)\s*=>\s*\{/,
      `describe('$1', () => {\n  ${beforeEachBlock}\n`
    );
  }
  
  private generateBeforeEach(resetCalls: string[]): string {
    if (resetCalls.length === 0) return '';
    
    return `
  beforeEach(() => {
    ${resetCalls.join('\n    ')}
  });
    `.trim();
  }
  
  private detectCounterResets(entityNames: string[]): string[] {
    return entityNames.map(name => {
      const pascalName = toPascalCase(name);
      return `reset${pascalName}Counter();`;
    });
  }
}
```

**受入基準マッピング**:

| 受入基準 | 実装箇所 |
|---------|---------||
| AC-013-1 | `generateBeforeEach()` |
| AC-013-2 | `detectCounterResets()` |
| AC-013-3 | テスト間独立性はbeforeEachで保証 |

---

### 4.7 非機能要件設計

---

#### DES-NFR-001: アクショナブルエラーメッセージ

| 属性 | 値 |
|------|-----|
| **ID** | DES-NFR-001 |
| **対象要件** | REQ-NFR-001 |
| **変更ファイル** | `packages/core/src/error/actionable-error.ts` |
| **設計パターン** | Error Handling Pattern |

**コンポーネント図**:

```
┌─────────────────────────────────────────────────────────┐
│ ActionableError                                [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + code: string                                           │
│ + message: string                                        │
│ + cause: string                                          │
│ + suggestions: string[]                                  │
│ + example: string                                        │
│ + helpCommand: string                                    │
│ + format(): string                                       │
└─────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────┐
│ ErrorFormatter                                 [NEW]     │
├─────────────────────────────────────────────────────────┤
│ + format(error: ActionableError): string                │
│ - formatCause(): string                                  │
│ - formatSuggestions(): string                            │
│ - formatExample(): string                                │
│ - formatHelpHint(): string                               │
└─────────────────────────────────────────────────────────┘
```

---

#### DES-NFR-002: コマンド応答性能

| 属性 | 値 |
|------|-----|
| **ID** | DES-NFR-002 |
| **対象要件** | REQ-NFR-002 |
| **変更ファイル** | `packages/core/src/cli/performance.ts` |
| **設計パターン** | Performance Optimization, Lazy Loading |

**性能最適化手法**:

| 手法 | 対象コマンド | 期待効果 |
|------|-------------|----------|
| **Lazy Loading** | 全コマンド | 起動時間短縮（未使用モジュールの遅延読込） |
| **並列処理** | `requirements validate` | ファイル並列解析で50%高速化 |
| **キャッシュ** | `learn status` | パターンライブラリのメモリキャッシュ |
| **インクリメンタル検証** | `design validate` | 変更ファイルのみ再検証 |

**設計詳細**:

```typescript
// packages/core/src/cli/performance.ts

// 1. Lazy Loading - コマンドモジュールの遅延読込
const commandLoaders: Record<string, () => Promise<Command>> = {
  'requirements': () => import('./commands/requirements'),
  'design': () => import('./commands/design'),
  'learn': () => import('./commands/learn'),
};

// 2. 並列処理 - Promise.all による並列ファイル解析
async function validateRequirementsParallel(files: string[]): Promise<ValidationResult[]> {
  const BATCH_SIZE = 10;
  const results: ValidationResult[] = [];
  
  for (let i = 0; i < files.length; i += BATCH_SIZE) {
    const batch = files.slice(i, i + BATCH_SIZE);
    const batchResults = await Promise.all(
      batch.map(file => validateFile(file))
    );
    results.push(...batchResults);
  }
  return results;
}

// 3. キャッシュ - LRUキャッシュによるパターンライブラリ高速化
class PatternCache {
  private cache = new Map<string, { data: Pattern; timestamp: number }>();
  private readonly TTL = 60_000; // 1分
  
  get(key: string): Pattern | undefined {
    const entry = this.cache.get(key);
    if (!entry) return undefined;
    if (Date.now() - entry.timestamp > this.TTL) {
      this.cache.delete(key);
      return undefined;
    }
    return entry.data;
  }
}
```

**性能目標**:

| コマンド | 目標 | 計測方法 |
|---------|------|----------|
| `requirements validate` (100件) | ≤5秒 | CI環境でのベンチマーク |
| `learn status` | ≤1秒 | ローカル環境での計測 |
| `design validate` (50件) | ≤3秒 | CI環境でのベンチマーク |

**受入基準マッピング**:

| 受入基準 | 実装箇所 |
|---------|---------||
| AC-015-1 | `validateRequirementsParallel()` |
| AC-015-2 | `PatternCache` |
| AC-015-3 | インクリメンタル検証ロジック |

---

## 5. トレーサビリティマトリクス

| 要件ID | 設計ID | 変更ファイル | 優先度 |
|--------|--------|--------------|--------|
| REQ-CLI-001 | DES-CLI-001 | `cli/commands/init.ts` | P0 |
| REQ-CLI-002 | DES-CLI-002 | `cli/commands/learn.ts` | P1 |
| REQ-CLI-003 | DES-CLI-003 | `cli/commands/scaffold.ts` | P1 |
| REQ-VAL-001 | DES-VAL-001 | `validators/ears-validator.ts` | P0 |
| REQ-VAL-002 | DES-VAL-002 | `validators/traceability-validator.ts` | P1 |
| REQ-LRN-001 | DES-LRN-001 | `learning/pattern-recommender.ts` | P1 |
| REQ-LRN-002 | DES-LRN-002 | `learning/domain-pattern-classifier.ts` | P1 |
| REQ-PAT-001 | DES-PAT-001 | `patterns/concurrency/` | P0 |
| REQ-PAT-002 | DES-PAT-002 | `patterns/time/` | P1 |
| REQ-GEN-001 | DES-GEN-001 | `codegen/vo-generator.ts` | P1 |
| REQ-GEN-002 | DES-GEN-002 | `codegen/status-generator.ts` | P1 |
| REQ-TST-001 | DES-TST-001 | `codegen/test-generator.ts` | P1 |
| REQ-TST-002 | DES-TST-002 | `codegen/test-generator.ts` | P0 |
| REQ-NFR-001 | DES-NFR-001 | `error/actionable-error.ts` | P1 |
| REQ-NFR-002 | DES-NFR-002 | `cli/performance.ts` | P2 |

---

## 6. 変更履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|----------|--------|
| 1.0 | 2026-01-13 | 初版作成 - REQ-MUSUBIX-v3.1.0に基づく設計 | AI Agent |
| 1.1 | 2026-01-13 | レビュー修正: DES-CLI-001に後方互換性セクション追加、DES-TST-001/002にコード詳細追加、DES-NFR-002に性能最適化手法追加 | AI Agent |

---

## 7. 承認

| 役割 | 氏名 | 署名 | 日付 |
|------|------|------|------|
| 作成者 | AI Agent | - | 2026-01-13 |
| レビュアー | | | |
| 承認者 | | | |

---

**文書終端**
