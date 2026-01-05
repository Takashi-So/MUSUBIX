/**
 * @file rule-config.ts
 * @description ExtensibleRuleConfig - 設定ロード/スキーマ検証
 * @requirement REQ-NFR-002
 * @design DES-SYMB-001 §6.2
 * @task TSK-SYMB-016
 */

import * as fs from 'fs';
import * as path from 'path';
import type { Explanation } from './types.js';

// ============================================================================
// Types
// ============================================================================

/**
 * ルールの重大度
 */
export type RuleSeverity = 'error' | 'warning' | 'info';

/**
 * コード言語
 */
export type CodeLanguage =
  | 'typescript'
  | 'javascript'
  | 'python'
  | 'java'
  | 'rust'
  | 'go'
  | 'csharp'
  | 'other';

/**
 * 憲法の enforcement レベル
 */
export type ConstitutionEnforcement = 'strict' | 'warning' | 'advisory';

/**
 * 憲法のステージ
 */
export type ConstitutionStage = 'requirements' | 'design' | 'implementation' | 'testing' | 'review';

/**
 * セマンティックフィルタールール設定
 */
export interface SemanticFilterRuleConfig {
  /** ルールID */
  id: string;
  /** 有効/無効 */
  enabled: boolean;
  /** 重大度 */
  severity: RuleSeverity;
  /** 説明 */
  description: string;
  /** 対象言語（未指定は全言語） */
  languages?: CodeLanguage[];
  /** タグ（owasp, secrets, project-api等） */
  tags?: string[];
  /** カスタムパターン（正規表現） */
  pattern?: string;
  /** 修正提案 */
  suggestion?: string;
}

/**
 * 憲法ルール設定
 */
export interface ConstitutionRuleConfig {
  /** 条項番号 (1-9) */
  article: 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9;
  /** enforcement レベル */
  enforcement: ConstitutionEnforcement;
  /** バリデーション対象ステージ */
  stages: ConstitutionStage[];
  /** パラメータ */
  params?: Record<string, string | number | boolean>;
}

/**
 * ルール設定バンドル
 */
export interface RuleConfigBundle {
  /** バージョン */
  version: 1;
  /** セマンティックフィルタールール */
  semanticFilterRules?: SemanticFilterRuleConfig[];
  /** 憲法ルール */
  constitutionRules?: ConstitutionRuleConfig[];
  /** メタデータ */
  metadata?: {
    name?: string;
    description?: string;
    lastUpdated?: string;
  };
}

/**
 * Artifact参照
 */
export interface ArtifactRef {
  /** 種別 */
  kind: 'requirements' | 'design' | 'code' | 'tests' | 'traceability' | 'steering' | 'config';
  /** パス */
  path: string;
  /** ハッシュ（オプション） */
  hash?: string;
}

/**
 * 設定ロード結果
 */
export interface ConfigLoadResult {
  /** 成功/失敗 */
  success: boolean;
  /** 設定バンドル */
  config?: RuleConfigBundle;
  /** エラー */
  errors: ConfigValidationError[];
  /** 参照したファイル */
  artifactRefs: ArtifactRef[];
  /** 説明 */
  explanation: Explanation;
}

/**
 * 設定検証エラー
 */
export interface ConfigValidationError {
  /** エラーコード */
  code: string;
  /** メッセージ */
  message: string;
  /** パス（JSONPath形式） */
  path?: string;
  /** 重大度 */
  severity: RuleSeverity;
}

/**
 * ローダー設定
 */
export interface RuleConfigLoaderOptions {
  /** 設定ディレクトリのベースパス */
  basePath?: string;
  /** スキーマ検証を有効にするか */
  validateSchema?: boolean;
  /** 環境変数の展開を許可するか */
  allowEnvExpansion?: boolean;
}

// ============================================================================
// Constants
// ============================================================================

/**
 * デフォルト設定パス
 */
export const DEFAULT_CONFIG_PATHS = {
  semanticFilter: 'storage/rules/semantic-filter.yml',
  constitutionRules: 'storage/rules/constitution-rules.yml',
  constitution: 'steering/rules/constitution.md',
};

/**
 * 有効な条項番号
 */
const VALID_ARTICLES = [1, 2, 3, 4, 5, 6, 7, 8, 9] as const;

/**
 * 有効なステージ
 */
const VALID_STAGES: ConstitutionStage[] = [
  'requirements',
  'design',
  'implementation',
  'testing',
  'review',
];

/**
 * 有効なenforcement
 */
const VALID_ENFORCEMENTS: ConstitutionEnforcement[] = ['strict', 'warning', 'advisory'];

// ============================================================================
// ExtensibleRuleConfig Class
// ============================================================================

/**
 * 拡張可能なルール設定マネージャー
 */
export class ExtensibleRuleConfig {
  private config: RuleConfigBundle | null = null;
  private readonly options: Required<RuleConfigLoaderOptions>;
  private loadedArtifacts: ArtifactRef[] = [];

  constructor(options: RuleConfigLoaderOptions = {}) {
    this.options = {
      basePath: options.basePath ?? process.cwd(),
      validateSchema: options.validateSchema ?? true,
      allowEnvExpansion: options.allowEnvExpansion ?? false,
    };
  }

  /**
   * 設定ファイルをロード
   */
  async loadConfig(configPath?: string): Promise<ConfigLoadResult> {
    const errors: ConfigValidationError[] = [];
    const artifactRefs: ArtifactRef[] = [];

    try {
      const fullPath = configPath
        ? path.resolve(this.options.basePath, configPath)
        : path.resolve(this.options.basePath, DEFAULT_CONFIG_PATHS.semanticFilter);

      // ファイル存在確認
      if (!fs.existsSync(fullPath)) {
        // ファイルが存在しない場合はデフォルト設定を返す
        this.config = this.getDefaultConfig();
        return {
          success: true,
          config: this.config,
          errors: [],
          artifactRefs: [],
          explanation: {
            summary: 'Using default configuration (config file not found)',
            reasoning: [`Config file not found at: ${fullPath}`, 'Default rules applied'],
            evidence: [],
            relatedRequirements: ['REQ-NFR-002'],
          },
        };
      }

      // ファイル読み込み
      const content = fs.readFileSync(fullPath, 'utf-8');
      artifactRefs.push({
        kind: 'config',
        path: fullPath,
        hash: this.computeHash(content),
      });

      // パース（YAML/JSON）
      const parsed = this.parseConfig(content, fullPath);
      if (!parsed) {
        errors.push({
          code: 'PARSE_ERROR',
          message: `Failed to parse config file: ${fullPath}`,
          severity: 'error',
        });
        return {
          success: false,
          errors,
          artifactRefs,
          explanation: {
            summary: 'Configuration loading failed',
            reasoning: ['Failed to parse configuration file', 'Check YAML/JSON syntax'],
            evidence: [],
            relatedRequirements: ['REQ-NFR-002'],
          },
        };
      }

      // スキーマ検証
      if (this.options.validateSchema) {
        const validationErrors = this.validateSchema(parsed);
        errors.push(...validationErrors);

        if (validationErrors.some((e) => e.severity === 'error')) {
          return {
            success: false,
            errors,
            artifactRefs,
            explanation: {
              summary: 'Configuration validation failed',
              reasoning: validationErrors.map((e) => e.message),
              evidence: [],
              relatedRequirements: ['REQ-NFR-002'],
            },
          };
        }
      }

      this.config = parsed as RuleConfigBundle;
      this.loadedArtifacts = artifactRefs;

      return {
        success: true,
        config: this.config,
        errors,
        artifactRefs,
        explanation: {
          summary: `Configuration loaded successfully from ${path.basename(fullPath)}`,
          reasoning: [
            `Loaded ${this.config.semanticFilterRules?.length ?? 0} semantic filter rules`,
            `Loaded ${this.config.constitutionRules?.length ?? 0} constitution rules`,
          ],
          evidence: artifactRefs.map((ref) => ({
            type: 'artifact' as const,
            content: ref.path,
            source: ref.kind,
            confidence: 1,
          })),
          relatedRequirements: ['REQ-NFR-002'],
        },
      };
    } catch (error) {
      const message = error instanceof Error ? error.message : 'Unknown error';
      errors.push({
        code: 'LOAD_ERROR',
        message,
        severity: 'error',
      });

      return {
        success: false,
        errors,
        artifactRefs,
        explanation: {
          summary: 'Configuration loading failed with error',
          reasoning: [message],
          evidence: [],
          relatedRequirements: ['REQ-NFR-002'],
        },
      };
    }
  }

  /**
   * JSONオブジェクトから設定をロード
   */
  loadFromObject(configObj: unknown): ConfigLoadResult {
    const errors: ConfigValidationError[] = [];

    // スキーマ検証
    if (this.options.validateSchema) {
      const validationErrors = this.validateSchema(configObj);
      errors.push(...validationErrors);

      if (validationErrors.some((e) => e.severity === 'error')) {
        return {
          success: false,
          errors,
          artifactRefs: [],
          explanation: {
            summary: 'Configuration validation failed',
            reasoning: validationErrors.map((e) => e.message),
            evidence: [],
            relatedRequirements: ['REQ-NFR-002'],
          },
        };
      }
    }

    this.config = configObj as RuleConfigBundle;

    return {
      success: true,
      config: this.config,
      errors,
      artifactRefs: [],
      explanation: {
        summary: 'Configuration loaded from object',
        reasoning: [
          `Loaded ${this.config.semanticFilterRules?.length ?? 0} semantic filter rules`,
          `Loaded ${this.config.constitutionRules?.length ?? 0} constitution rules`,
        ],
        evidence: [],
        relatedRequirements: ['REQ-NFR-002'],
      },
    };
  }

  /**
   * 現在の設定を取得
   */
  getConfig(): RuleConfigBundle | null {
    return this.config;
  }

  /**
   * セマンティックフィルタールールを取得
   */
  getSemanticFilterRules(options?: {
    language?: CodeLanguage;
    tags?: string[];
    enabledOnly?: boolean;
  }): SemanticFilterRuleConfig[] {
    const rules = this.config?.semanticFilterRules ?? [];

    return rules.filter((rule) => {
      if (options?.enabledOnly && !rule.enabled) {
        return false;
      }

      if (options?.language && rule.languages && !rule.languages.includes(options.language)) {
        return false;
      }

      if (options?.tags && options.tags.length > 0) {
        if (!rule.tags || !options.tags.some((t) => rule.tags?.includes(t))) {
          return false;
        }
      }

      return true;
    });
  }

  /**
   * 憲法ルールを取得
   */
  getConstitutionRules(options?: {
    articles?: number[];
    stage?: ConstitutionStage;
    enforcement?: ConstitutionEnforcement;
  }): ConstitutionRuleConfig[] {
    const rules = this.config?.constitutionRules ?? [];

    return rules.filter((rule) => {
      if (options?.articles && !options.articles.includes(rule.article)) {
        return false;
      }

      if (options?.stage && !rule.stages.includes(options.stage)) {
        return false;
      }

      if (options?.enforcement && rule.enforcement !== options.enforcement) {
        return false;
      }

      return true;
    });
  }

  /**
   * ルールを追加
   */
  addSemanticFilterRule(rule: SemanticFilterRuleConfig): void {
    if (!this.config) {
      this.config = this.getDefaultConfig();
    }

    if (!this.config.semanticFilterRules) {
      this.config.semanticFilterRules = [];
    }

    // 既存ルールの更新または新規追加
    const existingIndex = this.config.semanticFilterRules.findIndex((r) => r.id === rule.id);
    if (existingIndex >= 0) {
      this.config.semanticFilterRules[existingIndex] = rule;
    } else {
      this.config.semanticFilterRules.push(rule);
    }
  }

  /**
   * ロードしたArtifactRefを取得
   */
  getLoadedArtifacts(): ArtifactRef[] {
    return [...this.loadedArtifacts];
  }

  /**
   * 設定をエクスポート
   */
  exportConfig(): string {
    return JSON.stringify(this.config ?? this.getDefaultConfig(), null, 2);
  }

  // ============================================================================
  // Private Methods
  // ============================================================================

  /**
   * 設定をパース
   */
  private parseConfig(content: string, _filePath: string): unknown | null {
    try {
      // まずJSONとしてパース
      return JSON.parse(content);
    } catch {
      // YAMLとしてパース（簡易実装）
      try {
        return this.parseSimpleYaml(content);
      } catch {
        return null;
      }
    }
  }

  /**
   * 簡易YAMLパーサー
   */
  private parseSimpleYaml(content: string): unknown {
    // 非常に簡易的なYAMLパース（本番では js-yaml を使用）
    const lines = content.split('\n');
    const result: Record<string, unknown> = {};

    let currentArray: unknown[] | null = null;

    for (const line of lines) {
      const trimmed = line.trim();
      if (!trimmed || trimmed.startsWith('#')) continue;

      if (trimmed.startsWith('- ')) {
        if (currentArray) {
          const value = trimmed.slice(2).trim();
          currentArray.push(this.parseYamlValue(value));
        }
      } else if (trimmed.includes(':')) {
        const colonIndex = trimmed.indexOf(':');
        const key = trimmed.slice(0, colonIndex).trim();
        const value = trimmed.slice(colonIndex + 1).trim();

        if (value === '') {
          // key is now used as the array key
          currentArray = [];
          result[key] = currentArray;
        } else {
          result[key] = this.parseYamlValue(value);
          currentArray = null;
        }
      }
    }

    return result;
  }

  /**
   * YAML値をパース
   */
  private parseYamlValue(value: string): unknown {
    if (value === 'true') return true;
    if (value === 'false') return false;
    if (value === 'null') return null;
    if (!isNaN(Number(value))) return Number(value);
    return value.replace(/^["']|["']$/g, '');
  }

  /**
   * スキーマ検証
   */
  private validateSchema(config: unknown): ConfigValidationError[] {
    const errors: ConfigValidationError[] = [];

    if (!config || typeof config !== 'object') {
      errors.push({
        code: 'INVALID_TYPE',
        message: 'Configuration must be an object',
        severity: 'error',
      });
      return errors;
    }

    const cfg = config as Record<string, unknown>;

    // version検証
    if (cfg.version !== undefined && cfg.version !== 1) {
      errors.push({
        code: 'INVALID_VERSION',
        message: `Invalid version: ${cfg.version}. Only version 1 is supported`,
        path: 'version',
        severity: 'error',
      });
    }

    // semanticFilterRules検証
    if (cfg.semanticFilterRules) {
      if (!Array.isArray(cfg.semanticFilterRules)) {
        errors.push({
          code: 'INVALID_TYPE',
          message: 'semanticFilterRules must be an array',
          path: 'semanticFilterRules',
          severity: 'error',
        });
      } else {
        cfg.semanticFilterRules.forEach((rule, index) => {
          errors.push(...this.validateSemanticFilterRule(rule, index));
        });
      }
    }

    // constitutionRules検証
    if (cfg.constitutionRules) {
      if (!Array.isArray(cfg.constitutionRules)) {
        errors.push({
          code: 'INVALID_TYPE',
          message: 'constitutionRules must be an array',
          path: 'constitutionRules',
          severity: 'error',
        });
      } else {
        cfg.constitutionRules.forEach((rule, index) => {
          errors.push(...this.validateConstitutionRule(rule, index));
        });
      }
    }

    return errors;
  }

  /**
   * セマンティックフィルタールールを検証
   */
  private validateSemanticFilterRule(rule: unknown, index: number): ConfigValidationError[] {
    const errors: ConfigValidationError[] = [];
    const prefix = `semanticFilterRules[${index}]`;

    if (!rule || typeof rule !== 'object') {
      errors.push({
        code: 'INVALID_TYPE',
        message: `${prefix} must be an object`,
        path: prefix,
        severity: 'error',
      });
      return errors;
    }

    const r = rule as Record<string, unknown>;

    // 必須フィールド
    if (!r.id || typeof r.id !== 'string') {
      errors.push({
        code: 'MISSING_FIELD',
        message: `${prefix}.id is required and must be a string`,
        path: `${prefix}.id`,
        severity: 'error',
      });
    }

    if (r.enabled === undefined || typeof r.enabled !== 'boolean') {
      errors.push({
        code: 'MISSING_FIELD',
        message: `${prefix}.enabled is required and must be a boolean`,
        path: `${prefix}.enabled`,
        severity: 'error',
      });
    }

    if (!r.severity || !['error', 'warning', 'info'].includes(r.severity as string)) {
      errors.push({
        code: 'INVALID_VALUE',
        message: `${prefix}.severity must be one of: error, warning, info`,
        path: `${prefix}.severity`,
        severity: 'error',
      });
    }

    if (!r.description || typeof r.description !== 'string') {
      errors.push({
        code: 'MISSING_FIELD',
        message: `${prefix}.description is required and must be a string`,
        path: `${prefix}.description`,
        severity: 'error',
      });
    }

    return errors;
  }

  /**
   * 憲法ルールを検証
   */
  private validateConstitutionRule(rule: unknown, index: number): ConfigValidationError[] {
    const errors: ConfigValidationError[] = [];
    const prefix = `constitutionRules[${index}]`;

    if (!rule || typeof rule !== 'object') {
      errors.push({
        code: 'INVALID_TYPE',
        message: `${prefix} must be an object`,
        path: prefix,
        severity: 'error',
      });
      return errors;
    }

    const r = rule as Record<string, unknown>;

    // article検証
    if (!VALID_ARTICLES.includes(r.article as (typeof VALID_ARTICLES)[number])) {
      errors.push({
        code: 'INVALID_VALUE',
        message: `${prefix}.article must be 1-9`,
        path: `${prefix}.article`,
        severity: 'error',
      });
    }

    // enforcement検証
    if (!VALID_ENFORCEMENTS.includes(r.enforcement as ConstitutionEnforcement)) {
      errors.push({
        code: 'INVALID_VALUE',
        message: `${prefix}.enforcement must be one of: ${VALID_ENFORCEMENTS.join(', ')}`,
        path: `${prefix}.enforcement`,
        severity: 'error',
      });
    }

    // stages検証
    if (!Array.isArray(r.stages) || r.stages.length === 0) {
      errors.push({
        code: 'INVALID_VALUE',
        message: `${prefix}.stages must be a non-empty array`,
        path: `${prefix}.stages`,
        severity: 'error',
      });
    } else {
      for (const stage of r.stages) {
        if (!VALID_STAGES.includes(stage as ConstitutionStage)) {
          errors.push({
            code: 'INVALID_VALUE',
            message: `${prefix}.stages contains invalid stage: ${stage}`,
            path: `${prefix}.stages`,
            severity: 'error',
          });
        }
      }
    }

    return errors;
  }

  /**
   * 簡易ハッシュ計算
   */
  private computeHash(content: string): string {
    let hash = 0;
    for (let i = 0; i < content.length; i++) {
      const char = content.charCodeAt(i);
      hash = (hash << 5) - hash + char;
      hash |= 0;
    }
    return Math.abs(hash).toString(16).padStart(8, '0');
  }

  /**
   * デフォルト設定を取得
   */
  private getDefaultConfig(): RuleConfigBundle {
    return {
      version: 1,
      semanticFilterRules: [],
      constitutionRules: VALID_ARTICLES.map((article) => ({
        article,
        enforcement: 'strict' as ConstitutionEnforcement,
        stages: VALID_STAGES.slice(),
      })),
      metadata: {
        name: 'default',
        description: 'Default rule configuration',
        lastUpdated: new Date().toISOString(),
      },
    };
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * ExtensibleRuleConfigを作成
 */
export function createRuleConfig(options?: RuleConfigLoaderOptions): ExtensibleRuleConfig {
  return new ExtensibleRuleConfig(options);
}

/**
 * 設定ファイルをロード（簡易関数）
 */
export async function loadRuleConfig(
  configPath?: string,
  basePath?: string,
): Promise<ConfigLoadResult> {
  const config = new ExtensibleRuleConfig({ basePath });
  return config.loadConfig(configPath);
}
