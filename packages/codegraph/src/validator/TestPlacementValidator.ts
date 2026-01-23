/**
 * TestPlacementValidator - テスト配置検証
 *
 * @description
 * テストファイルの配置が規約に従っているか検証し、
 * 適切な配置を提案する。EXIT_GATE層でPhase 4完了時に検証。
 *
 * @see DES-CODEGRAPH-001 - テスト配置検証システム
 * @see TSK-FR-048 - TestPlacementValidatorインターフェース定義
 * @see TSK-FR-049 - validateFile/validateAll実装
 * @see TSK-FR-050 - suggestPlacement実装
 * @see TSK-FR-051 - QualityGate統合
 * @trace REQ-FR-006 - テスト品質保証
 */

import type {
  TestPlacement,
  PlacementRule,
  PlacementViolation,
  PlacementValidationResult,
  TestPlacementConfig,
} from '../types/TestPlacement.js';

import {
  createTestPlacement,
  inferTestFileType,
  inferSourceFilePath,
  calculatePlacementSummary,
  DEFAULT_TEST_PLACEMENT_CONFIG,
} from '../types/TestPlacement.js';

/**
 * 検証統計
 */
export interface ValidationStats {
  readonly totalValidations: number;
  readonly validCount: number;
  readonly warningCount: number;
  readonly invalidCount: number;
  readonly lastValidatedAt: number | null;
}

/**
 * TestPlacementValidatorインターフェース
 *
 * @trace DES-CODEGRAPH-001
 */
export interface ITestPlacementValidator {
  /**
   * 単一テストファイルを検証
   */
  validateFile(testFilePath: string): Promise<TestPlacement>;

  /**
   * 複数テストファイルを検証
   */
  validateAll(testFilePaths: readonly string[]): Promise<PlacementValidationResult>;

  /**
   * 配置提案を取得
   */
  suggestPlacement(testFilePath: string): Promise<readonly string[]>;

  /**
   * 特定ルールをチェック
   */
  checkRule(testFilePath: string, ruleId: string): Promise<PlacementViolation | null>;

  /**
   * ルール一覧を取得
   */
  getRules(): readonly PlacementRule[];

  /**
   * ルールを追加
   */
  addRule(rule: PlacementRule): void;

  /**
   * ルールを有効化
   */
  enableRule(ruleId: string): void;

  /**
   * ルールを無効化
   */
  disableRule(ruleId: string): void;

  /**
   * 統計を取得
   */
  getStats(): ValidationStats;
}

/**
 * TestPlacementValidator実装
 *
 * @trace DES-CODEGRAPH-001
 */
export class TestPlacementValidator implements ITestPlacementValidator {
  private readonly rules: Map<string, PlacementRule> = new Map();
  private readonly config: TestPlacementConfig;
  private stats: ValidationStats = {
    totalValidations: 0,
    validCount: 0,
    warningCount: 0,
    invalidCount: 0,
    lastValidatedAt: null,
  };

  constructor(config: TestPlacementConfig = DEFAULT_TEST_PLACEMENT_CONFIG) {
    this.config = config;

    // デフォルトルールを登録
    for (const rule of config.rules) {
      this.rules.set(rule.id, rule);
    }
  }

  /**
   * @trace TSK-FR-049
   */
  async validateFile(testFilePath: string): Promise<TestPlacement> {
    const violations: PlacementViolation[] = [];
    const suggestions: string[] = [];

    // 有効なルールでチェック
    for (const rule of this.rules.values()) {
      if (!rule.enabled) continue;

      const violation = await this.checkRuleInternal(testFilePath, rule);
      if (violation) {
        violations.push(violation);
      }
    }

    // 提案を生成
    if (violations.length > 0) {
      const suggested = await this.suggestPlacement(testFilePath);
      suggestions.push(...suggested);
    }

    const placement = createTestPlacement(testFilePath, violations, suggestions);

    // 統計更新
    this.updateStats(placement);

    return placement;
  }

  /**
   * @trace TSK-FR-049
   */
  async validateAll(testFilePaths: readonly string[]): Promise<PlacementValidationResult> {
    const placements: TestPlacement[] = [];

    for (const path of testFilePaths) {
      const placement = await this.validateFile(path);
      placements.push(placement);
    }

    const summary = calculatePlacementSummary(placements);

    const isValid = this.config.strictMode
      ? summary.invalidCount === 0 && summary.warningCount === 0
      : summary.invalidCount === 0;

    return Object.freeze({
      isValid,
      placements: Object.freeze(placements),
      summary,
      timestamp: Date.now(),
    });
  }

  /**
   * @trace TSK-FR-050
   */
  async suggestPlacement(testFilePath: string): Promise<readonly string[]> {
    const suggestions: string[] = [];
    const type = inferTestFileType(testFilePath);

    // パスからディレクトリとファイル名を抽出
    const parts = testFilePath.split('/');
    const fileName = parts.pop() || '';
    const baseName = fileName.replace(/\.test\.ts$/, '').replace(/\.spec\.ts$/, '');

    // ディレクトリパス
    const dirPath = parts.join('/');

    // __tests__ディレクトリの提案
    if (!testFilePath.includes('__tests__') && type === 'unit') {
      suggestions.push(`${dirPath}/__tests__/${baseName}.test.ts`);
    }

    // integrationテストの場合
    if (testFilePath.includes('.integration.') && !testFilePath.includes('/integration/')) {
      suggestions.push(`${dirPath}/integration/${baseName}.integration.test.ts`);
    }

    // e2eテストの場合
    if (testFilePath.includes('.e2e.') && !testFilePath.includes('/e2e/')) {
      const rootDir = parts[0] || 'tests';
      suggestions.push(`${rootDir}/e2e/${baseName}.e2e.test.ts`);
    }

    // ソースファイルに近い場所を提案
    const sourcePath = inferSourceFilePath(testFilePath);
    if (sourcePath) {
      const sourceDir = sourcePath.split('/').slice(0, -1).join('/');
      const sourceBaseName = sourcePath.split('/').pop()?.replace('.ts', '') || baseName;
      if (!suggestions.some(s => s.includes('__tests__'))) {
        suggestions.push(`${sourceDir}/__tests__/${sourceBaseName}.test.ts`);
      }
    }

    return Object.freeze(suggestions);
  }

  async checkRule(testFilePath: string, ruleId: string): Promise<PlacementViolation | null> {
    const rule = this.rules.get(ruleId);
    if (!rule) {
      return null;
    }

    return this.checkRuleInternal(testFilePath, rule);
  }

  private async checkRuleInternal(testFilePath: string, rule: PlacementRule): Promise<PlacementViolation | null> {
    // シンプルなパターンマッチング
    const matchesPattern = this.matchesGlob(testFilePath, rule.pattern);

    if (!matchesPattern) {
      // パターンに該当しない場合は違反なし
      return null;
    }

    // 期待される配置パターンと比較
    const matchesExpected = this.matchesExpectedLocation(testFilePath, rule.expectedLocation);

    if (!matchesExpected) {
      const suggestedPath = this.generateSuggestedPath(testFilePath, rule.expectedLocation);

      return {
        ruleId: rule.id,
        ruleName: rule.name,
        message: `${rule.description}. Current: ${testFilePath}`,
        severity: rule.severity,
        suggestedPath,
      };
    }

    return null;
  }

  private matchesGlob(path: string, pattern: string): boolean {
    // シンプルなglobマッチング実装
    const regexPattern = pattern
      .replace(/\*\*/g, '.*')
      .replace(/\*/g, '[^/]*')
      .replace(/\?/g, '.');

    const regex = new RegExp(`^${regexPattern}$`);
    return regex.test(path);
  }

  private matchesExpectedLocation(path: string, expectedPattern: string): boolean {
    // テンプレートパターンを正規表現に変換
    const regexPattern = expectedPattern
      .replace(/\{dir\}/g, '.*')
      .replace(/\{name\}/g, '[^/]+')
      .replace(/\*\*/g, '.*')
      .replace(/\*/g, '[^/]*');

    const regex = new RegExp(`^${regexPattern}$`);
    return regex.test(path);
  }

  private generateSuggestedPath(currentPath: string, expectedPattern: string): string {
    // シンプルな提案パス生成
    const parts = currentPath.split('/');
    const fileName = parts.pop() || '';
    const baseName = fileName.replace(/\.test\.ts$/, '').replace(/\.spec\.ts$/, '');
    const dir = parts.join('/');

    // {dir}/__tests__/{name}.test.ts パターンの場合
    if (expectedPattern.includes('__tests__')) {
      return `${dir}/__tests__/${baseName}.test.ts`;
    }

    return currentPath;
  }

  getRules(): readonly PlacementRule[] {
    return Object.freeze(Array.from(this.rules.values()));
  }

  addRule(rule: PlacementRule): void {
    this.rules.set(rule.id, rule);
  }

  enableRule(ruleId: string): void {
    const rule = this.rules.get(ruleId);
    if (rule) {
      this.rules.set(ruleId, { ...rule, enabled: true });
    }
  }

  disableRule(ruleId: string): void {
    const rule = this.rules.get(ruleId);
    if (rule) {
      this.rules.set(ruleId, { ...rule, enabled: false });
    }
  }

  getStats(): ValidationStats {
    return { ...this.stats };
  }

  private updateStats(placement: TestPlacement): void {
    this.stats = {
      totalValidations: this.stats.totalValidations + 1,
      validCount: this.stats.validCount + (placement.status === 'valid' ? 1 : 0),
      warningCount: this.stats.warningCount + (placement.status === 'warning' ? 1 : 0),
      invalidCount: this.stats.invalidCount + (placement.status === 'invalid' ? 1 : 0),
      lastValidatedAt: Date.now(),
    };
  }
}

/**
 * ファクトリ関数
 *
 * @trace TSK-FR-048
 */
export function createTestPlacementValidator(config?: TestPlacementConfig): ITestPlacementValidator {
  return new TestPlacementValidator(config);
}
