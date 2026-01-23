/**
 * TestPlacement Types
 *
 * @description
 * テスト配置検証の型定義
 *
 * @see TSK-FR-048 - TestPlacement型定義
 * @see REQ-FR-046〜050 - TestPlacementValidator
 * @trace DES-MUSUBIX-FR-001 DES-CODEGRAPH-001
 */

/**
 * テスト配置のステータス
 */
export type PlacementStatus =
  | 'valid'       // 適切な配置
  | 'warning'     // 警告（許容範囲内）
  | 'invalid';    // 不適切な配置

/**
 * テストファイルの種類
 */
export type TestFileType =
  | 'unit'        // ユニットテスト
  | 'integration' // 統合テスト
  | 'e2e'         // E2Eテスト
  | 'snapshot'    // スナップショットテスト
  | 'unknown';    // 不明

/**
 * テスト配置ルール
 */
export interface PlacementRule {
  readonly id: string;
  readonly name: string;
  readonly description: string;
  readonly pattern: string;       // テストファイルパターン (glob)
  readonly expectedLocation: string; // 期待される配置パターン
  readonly severity: 'error' | 'warning' | 'info';
  readonly enabled: boolean;
}

/**
 * テスト配置情報
 */
export interface TestPlacement {
  readonly testFilePath: string;
  readonly sourceFilePath: string | null;
  readonly type: TestFileType;
  readonly status: PlacementStatus;
  readonly violations: readonly PlacementViolation[];
  readonly suggestions: readonly string[];
  readonly metadata?: Readonly<Record<string, unknown>>;
}

/**
 * 配置違反
 */
export interface PlacementViolation {
  readonly ruleId: string;
  readonly ruleName: string;
  readonly message: string;
  readonly severity: 'error' | 'warning' | 'info';
  readonly suggestedPath?: string;
}

/**
 * 配置検証結果
 */
export interface PlacementValidationResult {
  readonly isValid: boolean;
  readonly placements: readonly TestPlacement[];
  readonly summary: PlacementSummary;
  readonly timestamp: number;
}

/**
 * 配置サマリー
 */
export interface PlacementSummary {
  readonly totalTests: number;
  readonly validCount: number;
  readonly warningCount: number;
  readonly invalidCount: number;
  readonly byType: Readonly<Record<TestFileType, number>>;
  readonly coverageEstimate: number;
}

/**
 * TestPlacementValidator設定
 */
export interface TestPlacementConfig {
  readonly rules: readonly PlacementRule[];
  readonly ignorePatterns: readonly string[];
  readonly strictMode: boolean;
}

/**
 * デフォルトの配置ルール
 */
export const DEFAULT_PLACEMENT_RULES: readonly PlacementRule[] = Object.freeze([
  {
    id: 'TPR-001',
    name: 'Co-located Unit Tests',
    description: 'Unit tests should be co-located with source files in __tests__ directory',
    pattern: '**/*.test.ts',
    expectedLocation: '{dir}/__tests__/{name}.test.ts',
    severity: 'error',
    enabled: true,
  },
  {
    id: 'TPR-002',
    name: 'Integration Tests Location',
    description: 'Integration tests should be in a dedicated integration directory',
    pattern: '**/*.integration.test.ts',
    expectedLocation: '**/integration/**/*.integration.test.ts',
    severity: 'warning',
    enabled: true,
  },
  {
    id: 'TPR-003',
    name: 'E2E Tests Location',
    description: 'E2E tests should be in e2e or tests/e2e directory',
    pattern: '**/*.e2e.test.ts',
    expectedLocation: '**/e2e/**/*.e2e.test.ts',
    severity: 'warning',
    enabled: true,
  },
  {
    id: 'TPR-004',
    name: 'Test File Naming',
    description: 'Test files should follow naming convention: {source}.test.ts',
    pattern: '**/__tests__/*.ts',
    expectedLocation: '**/__tests__/*.test.ts',
    severity: 'info',
    enabled: true,
  },
]);

/**
 * デフォルト設定
 */
export const DEFAULT_TEST_PLACEMENT_CONFIG: TestPlacementConfig = Object.freeze({
  rules: DEFAULT_PLACEMENT_RULES,
  ignorePatterns: Object.freeze(['**/node_modules/**', '**/dist/**', '**/build/**']),
  strictMode: false,
});

/**
 * テストファイルタイプを推定
 */
export function inferTestFileType(filePath: string): TestFileType {
  const lowerPath = filePath.toLowerCase();

  if (lowerPath.includes('.e2e.') || lowerPath.includes('/e2e/')) {
    return 'e2e';
  }
  if (lowerPath.includes('.integration.') || lowerPath.includes('/integration/')) {
    return 'integration';
  }
  if (lowerPath.includes('.snap') || lowerPath.includes('snapshot')) {
    return 'snapshot';
  }
  if (lowerPath.includes('.test.') || lowerPath.includes('.spec.') || lowerPath.includes('__tests__')) {
    return 'unit';
  }

  return 'unknown';
}

/**
 * ソースファイルパスを推定
 */
export function inferSourceFilePath(testFilePath: string): string | null {
  // __tests__/Foo.test.ts → ../Foo.ts
  const match = testFilePath.match(/(.+)\/__tests__\/(.+)\.test\.ts$/);
  if (match) {
    return `${match[1]}/${match[2]}.ts`;
  }

  // Foo.test.ts → Foo.ts (same directory)
  const simpleMatch = testFilePath.match(/(.+)\.test\.ts$/);
  if (simpleMatch) {
    return `${simpleMatch[1]}.ts`;
  }

  return null;
}

/**
 * TestPlacementを作成
 */
export function createTestPlacement(
  testFilePath: string,
  violations: readonly PlacementViolation[] = [],
  suggestions: readonly string[] = []
): TestPlacement {
  const type = inferTestFileType(testFilePath);
  const sourceFilePath = inferSourceFilePath(testFilePath);

  let status: PlacementStatus;
  if (violations.some(v => v.severity === 'error')) {
    status = 'invalid';
  } else if (violations.some(v => v.severity === 'warning')) {
    status = 'warning';
  } else {
    status = 'valid';
  }

  return Object.freeze({
    testFilePath,
    sourceFilePath,
    type,
    status,
    violations: Object.freeze(violations),
    suggestions: Object.freeze(suggestions),
  });
}

/**
 * 配置サマリーを計算
 */
export function calculatePlacementSummary(placements: readonly TestPlacement[]): PlacementSummary {
  const byType: Record<TestFileType, number> = {
    unit: 0,
    integration: 0,
    e2e: 0,
    snapshot: 0,
    unknown: 0,
  };

  let validCount = 0;
  let warningCount = 0;
  let invalidCount = 0;

  for (const p of placements) {
    byType[p.type]++;
    switch (p.status) {
      case 'valid':
        validCount++;
        break;
      case 'warning':
        warningCount++;
        break;
      case 'invalid':
        invalidCount++;
        break;
    }
  }

  const totalTests = placements.length;
  const coverageEstimate = totalTests > 0 ? validCount / totalTests : 0;

  return Object.freeze({
    totalTests,
    validCount,
    warningCount,
    invalidCount,
    byType: Object.freeze(byType),
    coverageEstimate,
  });
}
