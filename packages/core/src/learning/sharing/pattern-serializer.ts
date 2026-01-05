/**
 * Pattern Serializer
 *
 * @module learning/sharing/pattern-serializer
 * @description パターンのJSON/N3シリアライズ
 * @requirements REQ-SHARE-001, REQ-SHARE-004
 * @design DES-SHARE-001
 */

import { createHash } from 'crypto';
import type {
  SharedPattern,
  ExportOptions,
  ExportResult,
  SanitizeConfig,
  PatternMetadata,
  PatternContext,
} from './types.js';

/**
 * デフォルトのエクスポートオプション
 */
const DEFAULT_EXPORT_OPTIONS: ExportOptions = {
  sanitize: true,
  format: 'json',
  compress: false,
  includeVersion: true,
  includeMetadata: true,
};

/**
 * デフォルトのサニタイズ設定
 */
const DEFAULT_SANITIZE_CONFIG: SanitizeConfig = {
  removePaths: true,
  removeAuthor: false,
  customPatterns: [
    /\/Users\/[^\/]+/g, // macOS user paths
    /\/home\/[^\/]+/g, // Linux user paths
    /C:\\Users\\[^\\]+/gi, // Windows user paths
    /[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}/g, // Email addresses
    /\b(?:\d{1,3}\.){3}\d{1,3}\b/g, // IP addresses
  ],
  removeFields: ['absolutePath', 'localPath', 'userHome'],
};

/**
 * パターンシリアライザ
 * REQ-SHARE-001: パターンエクスポート
 */
export class PatternSerializer {
  private sanitizeConfig: SanitizeConfig;
  private version: string;

  constructor(options?: { sanitizeConfig?: Partial<SanitizeConfig>; version?: string }) {
    this.sanitizeConfig = {
      ...DEFAULT_SANITIZE_CONFIG,
      ...options?.sanitizeConfig,
    };
    this.version = options?.version ?? '1.0.0';
  }

  /**
   * パターンをエクスポート形式に変換
   */
  export(patterns: Partial<SharedPattern>[], options: Partial<ExportOptions> = {}): ExportResult {
    const opts: ExportOptions = { ...DEFAULT_EXPORT_OPTIONS, ...options };

    // パターンを共有形式に変換
    const sharedPatterns = patterns.map((p) => this.toSharedPattern(p));

    // サニタイズ
    const sanitizedPatterns = opts.sanitize
      ? sharedPatterns.map((p) => this.sanitize(p))
      : sharedPatterns;

    // シリアライズ
    let data: string;
    if (opts.format === 'n3') {
      data = this.toN3(sanitizedPatterns, opts);
    } else {
      data = this.toJSON(sanitizedPatterns, opts);
    }

    // 圧縮（オプション）
    if (opts.compress) {
      data = this.compress(data);
    }

    // チェックサム計算
    const checksum = this.calculateChecksum(data);

    return {
      data,
      patternCount: sanitizedPatterns.length,
      size: Buffer.byteLength(data, 'utf8'),
      format: opts.format,
      exportedAt: new Date().toISOString(),
      version: this.version,
      checksum,
    };
  }

  /**
   * Partial<SharedPattern> を SharedPattern に変換
   */
  private toSharedPattern(pattern: Partial<SharedPattern>): SharedPattern {
    const now = new Date().toISOString();

    return {
      id: pattern.id ?? this.generateId(pattern),
      name: pattern.name ?? 'Unknown Pattern',
      category: pattern.category ?? this.categorize(pattern),
      description: pattern.description ?? '',
      confidence: pattern.confidence ?? 0,
      usageCount: pattern.usageCount ?? 0,
      template: pattern.template,
      context: this.extractContext(pattern),
      metadata: this.createMetadata(pattern),
      createdAt: pattern.createdAt ?? now,
      updatedAt: pattern.updatedAt ?? now,
      version: pattern.version ?? 1,
    };
  }

  /**
   * パターンをカテゴリに分類
   */
  private categorize(pattern: Partial<SharedPattern>): SharedPattern['category'] {
    const name = (pattern.name ?? '').toLowerCase();

    if (name.includes('test') || name.includes('spec') || name.includes('mock')) {
      return 'test';
    }
    if (
      name.includes('pattern') ||
      name.includes('repository') ||
      name.includes('factory') ||
      name.includes('service')
    ) {
      return 'design';
    }
    if (name.includes('architecture') || name.includes('layer') || name.includes('module')) {
      return 'architecture';
    }
    return 'code';
  }

  /**
   * パターンからコンテキストを抽出
   */
  private extractContext(pattern: Partial<SharedPattern>): PatternContext {
    return {
      language: pattern.context?.language ?? 'typescript',
      framework: pattern.context?.framework,
      domain: pattern.context?.domain,
      applicableWhen: pattern.context?.applicableWhen,
      prerequisites: pattern.context?.prerequisites,
    };
  }

  /**
   * メタデータを作成
   */
  private createMetadata(pattern: Partial<SharedPattern>): PatternMetadata {
    return {
      source: pattern.metadata?.source ?? 'local',
      importedFrom: pattern.metadata?.importedFrom,
      originalId: pattern.metadata?.originalId,
      tags: pattern.metadata?.tags ?? [],
      author: pattern.metadata?.author,
      license: pattern.metadata?.license,
    };
  }

  /**
   * パターンIDを生成
   */
  private generateId(pattern: Partial<SharedPattern>): string {
    const hash = createHash('sha256')
      .update(`${pattern.name}-${pattern.confidence}-${Date.now()}`)
      .digest('hex')
      .substring(0, 8);
    return `PTN-${hash.toUpperCase()}`;
  }

  /**
   * JSONシリアライズ
   */
  private toJSON(patterns: SharedPattern[], options: ExportOptions): string {
    const exportData = {
      version: options.includeVersion ? this.version : undefined,
      exportedAt: new Date().toISOString(),
      patternCount: patterns.length,
      patterns,
    };

    return JSON.stringify(exportData, null, 2);
  }

  /**
   * N3/Turtle シリアライズ
   */
  private toN3(patterns: SharedPattern[], _options: ExportOptions): string {
    const prefixes = `
@prefix musubix: <http://musubix.dev/ontology#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

`;

    const triples = patterns.map((p) => this.patternToTriples(p)).join('\n');

    return prefixes + triples;
  }

  /**
   * パターンをRDFトリプルに変換
   */
  private patternToTriples(pattern: SharedPattern): string {
    const subject = `musubix:pattern/${pattern.id}`;
    const triples: string[] = [
      `${subject} a musubix:Pattern .`,
      `${subject} musubix:name "${this.escapeString(pattern.name)}" .`,
      `${subject} musubix:category "${pattern.category}" .`,
      `${subject} musubix:description "${this.escapeString(pattern.description)}" .`,
      `${subject} musubix:confidence "${pattern.confidence}"^^xsd:decimal .`,
      `${subject} musubix:usageCount "${pattern.usageCount}"^^xsd:integer .`,
      `${subject} musubix:version "${pattern.version}"^^xsd:integer .`,
      `${subject} musubix:createdAt "${pattern.createdAt}"^^xsd:dateTime .`,
      `${subject} musubix:updatedAt "${pattern.updatedAt}"^^xsd:dateTime .`,
    ];

    if (pattern.template) {
      triples.push(`${subject} musubix:template "${this.escapeString(pattern.template)}" .`);
    }

    if (pattern.context?.language) {
      triples.push(`${subject} musubix:language "${pattern.context.language}" .`);
    }

    if (pattern.metadata.tags) {
      pattern.metadata.tags.forEach((tag) => {
        triples.push(`${subject} musubix:tag "${this.escapeString(tag)}" .`);
      });
    }

    return triples.join('\n');
  }

  /**
   * 文字列エスケープ（N3用）
   */
  private escapeString(str: string): string {
    return str
      .replace(/\\/g, '\\\\')
      .replace(/"/g, '\\"')
      .replace(/\n/g, '\\n')
      .replace(/\r/g, '\\r')
      .replace(/\t/g, '\\t');
  }

  /**
   * サニタイズ処理
   * REQ-SHARE-004: 機密データ除去
   */
  sanitize(pattern: SharedPattern): SharedPattern {
    const sanitized = JSON.parse(JSON.stringify(pattern)) as SharedPattern;

    // パスの除去
    if (this.sanitizeConfig.removePaths) {
      sanitized.template = this.sanitizeText(sanitized.template);
      sanitized.description = this.sanitizeText(sanitized.description) ?? '';
    }

    // 作者情報の除去
    if (this.sanitizeConfig.removeAuthor) {
      sanitized.metadata.author = undefined;
    }

    // カスタムパターンの適用
    if (this.sanitizeConfig.customPatterns) {
      this.sanitizeConfig.customPatterns.forEach((regex) => {
        sanitized.template = sanitized.template?.replace(regex, '[REDACTED]');
        sanitized.description = sanitized.description.replace(regex, '[REDACTED]');
      });
    }

    // 指定フィールドの除去
    if (this.sanitizeConfig.removeFields) {
      this.sanitizeConfig.removeFields.forEach((field) => {
        this.removeField(sanitized as unknown as Record<string, unknown>, field);
      });
    }

    return sanitized;
  }

  /**
   * テキストのサニタイズ
   */
  private sanitizeText(text?: string): string | undefined {
    if (!text) return text;

    let sanitized = text;

    this.sanitizeConfig.customPatterns?.forEach((regex) => {
      sanitized = sanitized.replace(regex, '[REDACTED]');
    });

    return sanitized;
  }

  /**
   * オブジェクトからフィールドを除去
   */
  private removeField(obj: Record<string, unknown>, field: string): void {
    const parts = field.split('.');
    let current: Record<string, unknown> = obj;

    for (let i = 0; i < parts.length - 1; i++) {
      if (current[parts[i]] && typeof current[parts[i]] === 'object') {
        current = current[parts[i]] as Record<string, unknown>;
      } else {
        return;
      }
    }

    delete current[parts[parts.length - 1]];
  }

  /**
   * データ圧縮（Base64エンコード、将来的にzlib対応）
   */
  private compress(data: string): string {
    // 簡易実装: Base64エンコード
    // TODO: zlib圧縮の追加
    return Buffer.from(data, 'utf8').toString('base64');
  }

  /**
   * チェックサム計算
   */
  private calculateChecksum(data: string): string {
    return createHash('sha256').update(data).digest('hex');
  }

  /**
   * チェックサムの検証
   */
  verifyChecksum(data: string, expectedChecksum: string): boolean {
    const actualChecksum = this.calculateChecksum(data);
    return actualChecksum === expectedChecksum;
  }

  /**
   * バージョン取得
   */
  getVersion(): string {
    return this.version;
  }

  /**
   * サニタイズ設定を更新
   */
  updateSanitizeConfig(config: Partial<SanitizeConfig>): void {
    this.sanitizeConfig = {
      ...this.sanitizeConfig,
      ...config,
    };
  }
}
