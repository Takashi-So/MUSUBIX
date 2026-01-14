# TSK-BUGFIX-v3.3.10: 実装タスク分解

## 概要

DES-BUGFIX-v3.3.10で定義された設計を実装するためのタスク分解です。

## トレーサビリティ

| タスクID | 対応設計 | 対応要件 |
|----------|----------|----------|
| TSK-BUGFIX-001 | DES-BUGFIX-001 | REQ-BUGFIX-001 |
| TSK-BUGFIX-002 | DES-BUGFIX-002 | REQ-BUGFIX-002 |
| TSK-BUGFIX-003 | DES-BUGFIX-003 | REQ-BUGFIX-003 |
| TSK-BUGFIX-004 | DES-BUGFIX-004 | REQ-BUGFIX-004 |
| TSK-BUGFIX-005 | DES-BUGFIX-005 | REQ-BUGFIX-005 |
| TSK-BUGFIX-006 | DES-BUGFIX-006 | REQ-BUGFIX-006 |

---

## TSK-BUGFIX-001: scaffoldコマンド出力改善

### タスク一覧

| ID | タスク | 見積 | 依存 | 優先度 |
|----|--------|------|------|--------|
| TSK-001-01 | OutputFormatter実装 | 2h | - | P0 |
| TSK-001-02 | DirectoryChecker実装 | 1h | - | P1 |
| TSK-001-03 | ErrorGuidance実装 | 1h | - | P1 |
| TSK-001-04 | scaffold.tsへの統合 | 1h | 01,02,03 | P0 |
| TSK-001-05 | 単体テスト作成 | 1h | 04 | P0 |

### TSK-001-01: OutputFormatter実装

**ファイル**: `packages/core/src/cli/commands/scaffold.ts`

**実装内容**:
```typescript
interface ScaffoldStats {
  totalFiles: number;
  totalLines: number;
  totalSize: number;
}

function formatScaffoldOutput(files: GeneratedFile[], stats: ScaffoldStats): void {
  console.log('\n📁 Generated files:');
  for (const file of files) {
    console.log(`   ✅ ${file.path} (${file.lines} lines)`);
  }
  console.log(`\n📊 Summary: ${stats.totalFiles} files, ${stats.totalLines} lines`);
}
```

### TSK-001-02: DirectoryChecker実装

**実装内容**:
```typescript
function checkDirectory(targetDir: string): { exists: boolean; writable: boolean; error?: string } {
  try {
    if (!existsSync(targetDir)) {
      return { exists: false, writable: false, error: `Directory does not exist: ${targetDir}` };
    }
    accessSync(targetDir, constants.W_OK);
    return { exists: true, writable: true };
  } catch {
    return { exists: true, writable: false, error: `Directory is not writable: ${targetDir}` };
  }
}
```

---

## TSK-BUGFIX-002: getMissingQuestions堅牢性向上

### タスク一覧

| ID | タスク | 見積 | 依存 | 優先度 |
|----|--------|------|------|--------|
| TSK-002-01 | 型ガード関数実装 | 1h | - | P0 |
| TSK-002-02 | オーバーロード実装 | 2h | 01 | P0 |
| TSK-002-03 | エラーメッセージ改善 | 0.5h | 02 | P1 |
| TSK-002-04 | 単体テスト追加 | 1h | 03 | P0 |

### TSK-002-01: 型ガード関数実装

**ファイル**: `packages/core/src/requirements/clarifying-questions.ts`

**実装内容**:
```typescript
function isStringArray(input: unknown): input is readonly string[] {
  return Array.isArray(input) && input.every(item => typeof item === 'string');
}

function isClarificationContext(input: unknown): input is ClarificationContext {
  if (typeof input !== 'object' || input === null) return false;
  const ctx = input as Record<string, unknown>;
  return ['purpose', 'targetUser', 'expectedOutcome', 'constraints', 'successCriteria']
    .some(key => typeof ctx[key] === 'string');
}
```

### TSK-002-02: オーバーロード実装

**実装内容**:
```typescript
export function getMissingQuestions(input?: readonly string[] | ClarificationContext): ClarifyingQuestion[] {
  // undefined or empty → return all questions
  if (input === undefined) {
    return [...CORE_QUESTIONS];
  }
  
  // string[] → filter by IDs
  if (isStringArray(input)) {
    if (input.length === 0) return [...CORE_QUESTIONS];
    return CORE_QUESTIONS.filter(q => input.includes(q.id));
  }
  
  // ClarificationContext → analyze and get missing
  if (isClarificationContext(input)) {
    const analysis = analyzeContextCompleteness(input);
    return analysis.missingQuestions;
  }
  
  // Invalid type
  throw new TypeError(
    `getMissingQuestions: Expected string[], ClarificationContext, or undefined, but received ${typeof input}`
  );
}
```

---

## TSK-BUGFIX-003: codegenコマンド完全実装

### タスク一覧

| ID | タスク | 見積 | 依存 | 優先度 |
|----|--------|------|------|--------|
| TSK-003-01 | C4DesignParser強化 | 2h | - | P1 |
| TSK-003-02 | SkeletonGenerator拡張（4ファイル生成） | 3h | 01 | P1 |
| TSK-003-03 | TraceabilityInjector実装 | 1h | 02 | P1 |
| TSK-003-04 | codegen.tsへの統合 | 1h | 03 | P1 |
| TSK-003-05 | 単体テスト作成 | 2h | 04 | P1 |

### TSK-003-02: SkeletonGenerator拡張

**実装内容**:
```typescript
interface GeneratedSkeleton {
  interface: GeneratedFile;
  implementation: GeneratedFile;
  test: GeneratedFile;
  index: GeneratedFile;
}

function generateFullSkeleton(component: C4Component, options: GenerateOptions): GeneratedSkeleton {
  const baseName = toKebabCase(component.name);
  return {
    interface: {
      filename: `${baseName}.interface.ts`,
      content: generateInterface(component),
    },
    implementation: {
      filename: `${baseName}.ts`,
      content: generateImplementation(component, options.patterns),
    },
    test: {
      filename: `${baseName}.test.ts`,
      content: generateTestSkeleton(component),
    },
    index: {
      filename: 'index.ts',
      content: generateIndexExports([component]),
    },
  };
}
```

---

## TSK-BUGFIX-004: APIドキュメント改善

### タスク一覧

| ID | タスク | 見積 | 依存 | 優先度 |
|----|--------|------|------|--------|
| TSK-004-01 | quality-gate.ts JSDoc追加 | 1h | - | P2 |
| TSK-004-02 | API-REFERENCE.md更新 | 2h | 01 | P2 |

### TSK-004-01: JSDoc追加

**ファイル**: `packages/core/src/symbolic/quality-gate.ts`

**実装内容**:
```typescript
/**
 * QualityGateValidator - Neuro-Symbolic integration validator
 * 
 * @example
 * ```typescript
 * const validator = new QualityGateValidator({
 *   symbolicThreshold: 0.8,
 *   neuralThreshold: 0.7,
 * });
 * 
 * const result = await validator.validate({
 *   neural: { confidence: 0.85, result: generatedCode },
 *   symbolic: { valid: true, issues: [] },
 * });
 * 
 * if (result.passed) {
 *   // Use result.finalResult
 * }
 * ```
 */
export class QualityGateValidator {
  // ...
}
```

---

## TSK-BUGFIX-005: CLIバージョン管理改善

### タスク一覧

| ID | タスク | 見積 | 依存 | 優先度 |
|----|--------|------|------|--------|
| TSK-005-01 | DependencyVersionCollector実装 | 1h | - | P1 |
| TSK-005-02 | VersionMismatchDetector実装 | 1h | - | P1 |
| TSK-005-03 | カスタムversionアクション実装 | 2h | 01,02 | P1 |
| TSK-005-04 | CacheGuidance実装 | 0.5h | 03 | P1 |
| TSK-005-05 | 単体テスト作成 | 1h | 04 | P1 |

### TSK-005-01: DependencyVersionCollector実装

**ファイル**: `packages/core/src/version.ts`

**実装内容**:
```typescript
interface DependencyVersions {
  core: string;
  mcpServer: string;
  knowledge: string;
  policy: string;
  decisions: string;
}

function collectDependencyVersions(): DependencyVersions {
  return {
    core: require('@nahisaho/musubix-core/package.json').version,
    mcpServer: tryGetVersion('@nahisaho/musubix-mcp-server'),
    knowledge: tryGetVersion('@musubix/knowledge'),
    policy: tryGetVersion('@musubix/policy'),
    decisions: tryGetVersion('@musubix/decisions'),
  };
}

function tryGetVersion(pkg: string): string {
  try {
    return require(`${pkg}/package.json`).version;
  } catch {
    return 'not installed';
  }
}
```

### TSK-005-03: カスタムversionアクション実装

**ファイル**: `packages/core/src/cli/base.ts`

**実装内容**:
```typescript
program
  .option('-v, --version', 'Display version number')
  .on('option:version', () => {
    const verbose = process.argv.includes('--verbose');
    console.log(`musubix v${VERSION}`);
    
    if (verbose) {
      const deps = collectDependencyVersions();
      console.log('\nDependencies:');
      console.log(`  @nahisaho/musubix-core: ${deps.core}`);
      console.log(`  @nahisaho/musubix-mcp-server: ${deps.mcpServer}`);
      console.log(`  @musubix/knowledge: ${deps.knowledge}`);
      console.log(`  @musubix/policy: ${deps.policy}`);
      console.log(`  @musubix/decisions: ${deps.decisions}`);
    }
    
    // Check version mismatch
    const mismatch = checkVersionMismatch();
    if (mismatch.hasMismatch) {
      console.warn(`\n⚠️ Version mismatch: config expects ${mismatch.expected}, but ${mismatch.actual} is installed`);
      console.log('   Run: npx --yes musubix@latest');
    }
    
    process.exit(0);
  });
```

---

## TSK-BUGFIX-006: テスト生成機能統合

### タスク一覧

| ID | タスク | 見積 | 依存 | 優先度 |
|----|--------|------|------|--------|
| TSK-006-01 | TestIntegrator実装 | 2h | - | P1 |
| TSK-006-02 | --with-testsオプション追加 | 1h | 01 | P1 |
| TSK-006-03 | TestFileNamer実装 | 0.5h | - | P1 |
| TSK-006-04 | 単体テスト作成 | 1h | 02,03 | P1 |

### TSK-006-01: TestIntegrator実装

**ファイル**: `packages/core/src/codegen/test-integrator.ts`（新規）

**実装内容**:
```typescript
import { UnitTestGenerator, createUnitTestGenerator } from './unit-test-generator.js';

export interface TestGenerationOptions {
  withTests: boolean;
  testDir: 'same' | '__tests__';
  framework: 'vitest' | 'jest';
}

export function integrateTestGeneration(
  component: GeneratedCode,
  options: TestGenerationOptions
): GeneratedCode[] {
  const results: GeneratedCode[] = [component];
  
  if (!options.withTests) return results;
  
  const generator = createUnitTestGenerator({
    framework: options.framework,
    style: 'expect',
  });
  
  const testFile = generator.generateFromCode(component.content);
  const testPath = getTestFilePath(component.filename, options.testDir);
  
  results.push({
    filename: testPath,
    language: component.language,
    content: testFile.code,
  });
  
  return results;
}

function getTestFilePath(componentPath: string, testDir: 'same' | '__tests__'): string {
  const dir = dirname(componentPath);
  const base = basename(componentPath, '.ts');
  
  if (testDir === '__tests__') {
    return join(dir, '__tests__', `${base}.test.ts`);
  }
  return join(dir, `${base}.test.ts`);
}
```

---

## 実行順序

### Phase 1: P0タスク（必須）
1. TSK-001-01 → TSK-001-04 → TSK-001-05
2. TSK-002-01 → TSK-002-02 → TSK-002-04

### Phase 2: P1タスク（重要）
3. TSK-001-02, TSK-001-03
4. TSK-002-03
5. TSK-003-01 → TSK-003-02 → TSK-003-03 → TSK-003-04 → TSK-003-05
6. TSK-005-01, TSK-005-02 → TSK-005-03 → TSK-005-04 → TSK-005-05
7. TSK-006-01, TSK-006-03 → TSK-006-02 → TSK-006-04

### Phase 3: P2タスク（任意）
8. TSK-004-01 → TSK-004-02

---

## 工数サマリー

| タスクグループ | タスク数 | 合計見積 |
|---------------|---------|---------|
| TSK-BUGFIX-001 | 5 | 6h |
| TSK-BUGFIX-002 | 4 | 4.5h |
| TSK-BUGFIX-003 | 5 | 9h |
| TSK-BUGFIX-004 | 2 | 3h |
| TSK-BUGFIX-005 | 5 | 5.5h |
| TSK-BUGFIX-006 | 4 | 4.5h |
| **合計** | **25** | **32.5h** |

---

## 承認

| 役割 | 名前 | 日付 | 署名 |
|------|------|------|------|
| 作成者 | AI Agent | 2026-01-14 | ✅ |
| レビュアー | | | |
| 承認者 | | | |
