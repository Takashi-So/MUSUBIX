/**
 * Pattern Deserializer
 *
 * @module learning/sharing/pattern-deserializer
 * @description パターンのJSON/N3デシリアライズ
 * @requirements REQ-SHARE-002, REQ-SHARE-003
 * @design DES-SHARE-002
 */

import { createHash } from 'crypto';
import type {
  SharedPattern,
  ImportResult,
  ImportOptions,
  ValidationResult,
  ValidationError,
  ValidationWarning,
} from './types.js';

/**
 * デフォルトのインポートオプション
 */
const DEFAULT_IMPORT_OPTIONS: ImportOptions = {
  skipValidation: false,
  conflictStrategy: 'skip',
  overwrite: false,
};

/**
 * エクスポートデータの構造
 */
interface ExportData {
  version?: string;
  exportedAt: string;
  patternCount: number;
  patterns: SharedPattern[];
}

/**
 * パターンデシリアライザ
 * REQ-SHARE-002: パターンインポート
 */
export class PatternDeserializer {
  private supportedVersions: string[];

  constructor(options?: { supportedVersions?: string[] }) {
    this.supportedVersions = options?.supportedVersions ?? ['1.0.0', '1.0.1', '1.1.0'];
  }

  /**
   * データをインポート
   */
  async import(data: string, options: Partial<ImportOptions> = {}): Promise<ImportResult> {
    const opts: ImportOptions = { ...DEFAULT_IMPORT_OPTIONS, ...options };

    const errors: string[] = [];
    const warnings: string[] = [];
    const patterns: SharedPattern[] = [];
    let skippedCount = 0;

    try {
      // フォーマット検出とパース
      const parsed = this.parse(data);

      // バージョンチェック
      if (parsed.version && !this.supportedVersions.includes(parsed.version)) {
        warnings.push(
          `Version ${parsed.version} may not be fully compatible. Supported: ${this.supportedVersions.join(', ')}`
        );
      }

      // 検証（オプション）
      if (!opts.skipValidation) {
        const validation = this.validate(data);
        if (!validation.valid) {
          return {
            success: false,
            importedCount: 0,
            skippedCount: 0,
            conflictCount: 0,
            patterns: [],
            errors: validation.errors.map((e) => e.message),
            warnings: validation.warnings.map((w) => w.message),
          };
        }
        warnings.push(...validation.warnings.map((w) => w.message));
      }

      // パターンの処理
      for (const pattern of parsed.patterns) {
        try {
          const validated = this.validatePattern(pattern);
          if (validated) {
            // メタデータを更新
            validated.metadata.source = 'imported';
            validated.metadata.importedFrom = 'external';
            validated.metadata.originalId = validated.id;
            patterns.push(validated);
          } else {
            skippedCount++;
          }
        } catch (err) {
          errors.push(`Failed to process pattern: ${(err as Error).message}`);
          skippedCount++;
        }
      }

      return {
        success: true,
        importedCount: patterns.length,
        skippedCount,
        conflictCount: 0, // 競合検出は ConflictResolver で行う
        patterns,
        errors,
        warnings,
      };
    } catch (err) {
      return {
        success: false,
        importedCount: 0,
        skippedCount: 0,
        conflictCount: 0,
        patterns: [],
        errors: [`Parse error: ${(err as Error).message}`],
        warnings,
      };
    }
  }

  /**
   * データを検証
   * REQ-SHARE-003: オントロジー制約検証
   */
  validate(data: string): ValidationResult {
    const startTime = Date.now();
    const errors: ValidationError[] = [];
    const warnings: ValidationWarning[] = [];
    let patternCount = 0;

    try {
      const parsed = this.parse(data);
      patternCount = parsed.patterns?.length ?? 0;

      // 基本構造の検証
      if (!parsed.patterns || !Array.isArray(parsed.patterns)) {
        errors.push({
          code: 'INVALID_STRUCTURE',
          message: 'Data must contain a "patterns" array',
        });
        return {
          valid: false,
          errors,
          warnings,
          patternCount: 0,
          validationTime: Date.now() - startTime,
        };
      }

      // 各パターンの検証
      parsed.patterns.forEach((pattern, index) => {
        const patternErrors = this.validatePatternStructure(pattern, index);
        errors.push(...patternErrors.errors);
        warnings.push(...patternErrors.warnings);
      });

      // 重複ID検証
      const ids = parsed.patterns.map((p) => p.id).filter((id) => id);
      const duplicates = ids.filter((id, index) => ids.indexOf(id) !== index);
      if (duplicates.length > 0) {
        errors.push({
          code: 'DUPLICATE_IDS',
          message: `Duplicate pattern IDs found: ${duplicates.join(', ')}`,
        });
      }

      // 循環参照チェック（将来実装）

      return {
        valid: errors.length === 0,
        errors,
        warnings,
        patternCount,
        validationTime: Date.now() - startTime,
      };
    } catch (err) {
      errors.push({
        code: 'PARSE_ERROR',
        message: `Failed to parse data: ${(err as Error).message}`,
      });
      return {
        valid: false,
        errors,
        warnings,
        patternCount: 0,
        validationTime: Date.now() - startTime,
      };
    }
  }

  /**
   * データをパース
   */
  private parse(data: string): ExportData {
    // Base64デコードを試みる
    let decoded = data;
    if (this.isBase64(data)) {
      decoded = Buffer.from(data, 'base64').toString('utf8');
    }

    // N3形式のチェック
    if (decoded.trim().startsWith('@prefix')) {
      return this.parseN3(decoded);
    }

    // JSON形式
    return JSON.parse(decoded) as ExportData;
  }

  /**
   * Base64かどうかをチェック
   */
  private isBase64(str: string): boolean {
    // 基本的なBase64パターンチェック
    const base64Regex = /^[A-Za-z0-9+/=]+$/;
    return base64Regex.test(str) && str.length % 4 === 0 && str.length > 100;
  }

  /**
   * N3形式をパース
   */
  private parseN3(data: string): ExportData {
    const patterns: SharedPattern[] = [];
    const lines = data.split('\n');

    // トリプルを抽出
    const triples = new Map<string, Map<string, string>>();

    for (const line of lines) {
      if (line.startsWith('@prefix') || line.trim() === '') continue;

      // 簡易パーサー: subject predicate object .
      const match = line.match(/^(musubix:pattern\/[^\s]+)\s+([^\s]+)\s+"?([^"]+)"?\s*\./);
      if (match) {
        const [, subject, predicate, object] = match;
        if (!triples.has(subject)) {
          triples.set(subject, new Map());
        }
        const predicateName = predicate.replace('musubix:', '');
        triples.get(subject)!.set(predicateName, object);
      }
    }

    // トリプルからパターンを構築
    for (const [subject, properties] of triples) {
      const id = subject.replace('musubix:pattern/', '');
      const pattern: SharedPattern = {
        id,
        name: properties.get('name') ?? '',
        category: (properties.get('category') as SharedPattern['category']) ?? 'code',
        description: properties.get('description') ?? '',
        confidence: parseFloat(properties.get('confidence') ?? '0'),
        usageCount: parseInt(properties.get('usageCount') ?? '0', 10),
        template: properties.get('template'),
        context: {
          language: properties.get('language'),
        },
        metadata: {
          source: 'imported',
          tags: [],
        },
        createdAt: properties.get('createdAt') ?? new Date().toISOString(),
        updatedAt: properties.get('updatedAt') ?? new Date().toISOString(),
        version: parseInt(properties.get('version') ?? '1', 10),
      };
      patterns.push(pattern);
    }

    return {
      exportedAt: new Date().toISOString(),
      patternCount: patterns.length,
      patterns,
    };
  }

  /**
   * パターン構造の検証
   */
  private validatePatternStructure(
    pattern: Partial<SharedPattern>,
    index: number
  ): { errors: ValidationError[]; warnings: ValidationWarning[] } {
    const errors: ValidationError[] = [];
    const warnings: ValidationWarning[] = [];
    const location = `patterns[${index}]`;

    // 必須フィールドの検証
    if (!pattern.name || pattern.name.trim() === '') {
      errors.push({
        code: 'MISSING_NAME',
        message: 'Pattern name is required',
        patternId: pattern.id,
        location,
      });
    }

    if (pattern.confidence === undefined || pattern.confidence === null) {
      errors.push({
        code: 'MISSING_CONFIDENCE',
        message: 'Pattern confidence is required',
        patternId: pattern.id,
        location,
      });
    } else if (pattern.confidence < 0 || pattern.confidence > 1) {
      errors.push({
        code: 'INVALID_CONFIDENCE',
        message: 'Confidence must be between 0 and 1',
        patternId: pattern.id,
        location,
      });
    }

    // カテゴリの検証
    const validCategories = ['code', 'design', 'test', 'architecture'];
    if (pattern.category && !validCategories.includes(pattern.category)) {
      warnings.push({
        code: 'UNKNOWN_CATEGORY',
        message: `Unknown category "${pattern.category}", defaulting to "code"`,
        patternId: pattern.id,
        suggestion: `Use one of: ${validCategories.join(', ')}`,
      });
    }

    // 日付形式の検証
    if (pattern.createdAt && isNaN(Date.parse(pattern.createdAt))) {
      warnings.push({
        code: 'INVALID_DATE',
        message: 'Invalid createdAt date format',
        patternId: pattern.id,
        suggestion: 'Use ISO 8601 format',
      });
    }

    // 説明の長さ警告
    if (pattern.description && pattern.description.length > 1000) {
      warnings.push({
        code: 'LONG_DESCRIPTION',
        message: 'Description is very long (>1000 chars)',
        patternId: pattern.id,
        suggestion: 'Consider shortening the description',
      });
    }

    return { errors, warnings };
  }

  /**
   * 単一パターンの検証と正規化
   */
  private validatePattern(pattern: Partial<SharedPattern>): SharedPattern | null {
    if (!pattern.name || pattern.confidence === undefined) {
      return null;
    }

    const now = new Date().toISOString();

    return {
      id: pattern.id ?? this.generateId(pattern.name),
      name: pattern.name,
      category: pattern.category ?? 'code',
      description: pattern.description ?? '',
      confidence: Math.max(0, Math.min(1, pattern.confidence)),
      usageCount: pattern.usageCount ?? 0,
      template: pattern.template,
      context: pattern.context ?? {},
      metadata: pattern.metadata ?? { source: 'imported' },
      createdAt: pattern.createdAt ?? now,
      updatedAt: now,
      version: pattern.version ?? 1,
    };
  }

  /**
   * パターンIDを生成
   */
  private generateId(name: string): string {
    const hash = createHash('sha256')
      .update(`${name}-${Date.now()}`)
      .digest('hex')
      .substring(0, 8);
    return `PTN-${hash.toUpperCase()}`;
  }

  /**
   * サポートされているバージョンを取得
   */
  getSupportedVersions(): string[] {
    return [...this.supportedVersions];
  }

  /**
   * サポートバージョンを追加
   */
  addSupportedVersion(version: string): void {
    if (!this.supportedVersions.includes(version)) {
      this.supportedVersions.push(version);
    }
  }
}
