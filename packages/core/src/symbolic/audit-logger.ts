/**
 * @file audit-logger.ts
 * @description AuditLogger - 監査ログのハッシュチェーン/保持/アーカイブ
 * @requirement REQ-NFR-006
 * @design DES-SYMB-001 §6.6
 * @task TSK-SYMB-017
 */

import * as fs from 'fs';
import * as path from 'path';
import * as crypto from 'crypto';

// ============================================================================
// Types
// ============================================================================

/**
 * 監査イベントタイプ
 */
export type AuditEventType =
  | 'constitution_check'
  | 'semantic_filter'
  | 'formal_verify'
  | 'route_decision'
  | 'security_scan'
  | 'config_change'
  | 'access_control'
  | 'data_export'
  | 'system_event';

/**
 * 監査結果
 */
export type AuditResult = 'pass' | 'fail' | 'warn' | 'error';

/**
 * 監査ログエントリ
 */
export interface AuditLogEntry {
  /** バージョン */
  version: 1;
  /** タイムスタンプ */
  timestamp: string;
  /** 相関ID */
  correlationId: string;
  /** イベントタイプ */
  eventType: AuditEventType;
  /** 関連アーティファクトID */
  artifactIds: string[];
  /** 結果 */
  result: AuditResult;
  /** サマリー */
  summary: string;
  /** 証跡への参照 */
  evidenceRef?: string;
  /** 前のハッシュ */
  prevHash?: string;
  /** 現在のハッシュ */
  hash: string;
  /** メタデータ */
  metadata?: Record<string, unknown>;
}

/**
 * チェックポイント
 */
export interface Checkpoint {
  /** チェックポイントID */
  id: string;
  /** 作成日時 */
  timestamp: string;
  /** 最後のエントリハッシュ */
  lastEntryHash: string;
  /** エントリ数 */
  entryCount: number;
  /** チェックポイントハッシュ */
  checkpointHash: string;
}

/**
 * 整合性検証結果
 */
export interface IntegrityVerificationResult {
  /** 検証成功 */
  valid: boolean;
  /** 検証したエントリ数 */
  entriesVerified: number;
  /** 最初の不整合のインデックス（-1 = なし） */
  firstInconsistencyAt: number;
  /** エラーメッセージ */
  errors: string[];
  /** 検証に使用したチェックポイント */
  usedCheckpoint?: Checkpoint;
}

/**
 * アーカイブ結果
 */
export interface ArchiveResult {
  /** アーカイブ成功 */
  success: boolean;
  /** アーカイブしたエントリ数 */
  archivedCount: number;
  /** アーカイブファイルパス */
  archivePath?: string;
  /** アーカイブハッシュ */
  archiveHash?: string;
  /** エラー */
  error?: string;
}

/**
 * AuditLogger設定
 */
export interface AuditLoggerConfig {
  /** ログディレクトリ */
  logDirectory?: string;
  /** アーカイブディレクトリ */
  archiveDirectory?: string;
  /** 保持日数 */
  retentionDays?: number;
  /** チェックポイント間隔（エントリ数） */
  checkpointInterval?: number;
  /** ログファイルの最大サイズ（バイト） */
  maxLogFileSize?: number;
  /** 自動アーカイブを有効にするか */
  autoArchive?: boolean;
}

// ============================================================================
// Constants
// ============================================================================

/**
 * デフォルト設定
 */
export const DEFAULT_AUDIT_CONFIG: Required<AuditLoggerConfig> = {
  logDirectory: 'storage/audit',
  archiveDirectory: 'storage/archive/audit',
  retentionDays: 90,
  checkpointInterval: 100,
  maxLogFileSize: 10 * 1024 * 1024, // 10MB
  autoArchive: true,
};

/**
 * ログファイル名パターン
 */
const LOG_FILE_NAME = 'audit-log.jsonl';
const CHECKPOINT_FILE_NAME = 'checkpoints.json';

// ============================================================================
// AuditLogger Class
// ============================================================================

/**
 * 監査ログマネージャー
 * @description ハッシュチェーンによる改ざん検出、保持、アーカイブを提供
 */
export class AuditLogger {
  private readonly config: Required<AuditLoggerConfig>;
  private lastHash: string | null = null;
  private entryCount = 0;
  private checkpoints: Checkpoint[] = [];
  private initialized = false;

  constructor(config: AuditLoggerConfig = {}) {
    this.config = { ...DEFAULT_AUDIT_CONFIG, ...config };
  }

  /**
   * 初期化（ディレクトリ作成、既存ログの読み込み）
   */
  async initialize(): Promise<void> {
    if (this.initialized) return;

    // ディレクトリ作成
    this.ensureDirectories();

    // 既存ログの読み込み
    await this.loadExistingState();

    this.initialized = true;
  }

  /**
   * 監査イベントを記録
   */
  async log(event: {
    eventType: AuditEventType;
    artifactIds: string[];
    result: AuditResult;
    summary: string;
    evidenceRef?: string;
    correlationId?: string;
    metadata?: Record<string, unknown>;
  }): Promise<AuditLogEntry> {
    await this.initialize();

    const entry: AuditLogEntry = {
      version: 1,
      timestamp: new Date().toISOString(),
      correlationId: event.correlationId ?? this.generateCorrelationId(),
      eventType: event.eventType,
      artifactIds: event.artifactIds,
      result: event.result,
      summary: event.summary,
      evidenceRef: event.evidenceRef,
      prevHash: this.lastHash ?? undefined,
      hash: '', // 後で計算
      metadata: event.metadata,
    };

    // ハッシュ計算
    entry.hash = this.computeEntryHash(entry);
    this.lastHash = entry.hash;
    this.entryCount++;

    // ファイルに追記
    await this.appendEntry(entry);

    // チェックポイント作成確認
    if (this.entryCount % this.config.checkpointInterval === 0) {
      await this.createCheckpoint();
    }

    // 自動アーカイブ確認
    if (this.config.autoArchive) {
      await this.checkAndArchive();
    }

    return entry;
  }

  /**
   * 整合性を検証
   */
  async verifyIntegrity(options?: { fromCheckpoint?: boolean }): Promise<IntegrityVerificationResult> {
    await this.initialize();

    const entries = await this.readAllEntries();
    const errors: string[] = [];

    if (entries.length === 0) {
      return {
        valid: true,
        entriesVerified: 0,
        firstInconsistencyAt: -1,
        errors: [],
      };
    }

    // チェックポイントから開始する場合
    let startIndex = 0;
    let expectedPrevHash: string | undefined;
    let usedCheckpoint: Checkpoint | undefined;

    if (options?.fromCheckpoint && this.checkpoints.length > 0) {
      usedCheckpoint = this.checkpoints[this.checkpoints.length - 1];
      // チェックポイント以降のエントリを検証
      const checkpointEntryIndex = entries.findIndex(
        (e) => e.hash === usedCheckpoint!.lastEntryHash,
      );
      if (checkpointEntryIndex >= 0) {
        startIndex = checkpointEntryIndex + 1;
        expectedPrevHash = usedCheckpoint.lastEntryHash;
      }
    }

    // ハッシュチェーンを検証
    for (let i = startIndex; i < entries.length; i++) {
      const entry = entries[i];

      // prevHashの検証
      if (i === 0) {
        if (entry.prevHash !== undefined) {
          errors.push(`Entry 0: prevHash should be undefined for first entry`);
        }
      } else {
        const expected = expectedPrevHash ?? entries[i - 1].hash;
        if (entry.prevHash !== expected) {
          return {
            valid: false,
            entriesVerified: i,
            firstInconsistencyAt: i,
            errors: [`Entry ${i}: prevHash mismatch. Expected ${expected}, got ${entry.prevHash}`],
            usedCheckpoint,
          };
        }
      }

      // ハッシュの検証
      const computed = this.computeEntryHash(entry);
      if (entry.hash !== computed) {
        return {
          valid: false,
          entriesVerified: i,
          firstInconsistencyAt: i,
          errors: [`Entry ${i}: hash mismatch. Expected ${computed}, got ${entry.hash}`],
          usedCheckpoint,
        };
      }

      expectedPrevHash = entry.hash;
    }

    return {
      valid: errors.length === 0,
      entriesVerified: entries.length - startIndex,
      firstInconsistencyAt: -1,
      errors,
      usedCheckpoint,
    };
  }

  /**
   * チェックポイントを作成
   */
  async createCheckpoint(): Promise<Checkpoint> {
    const checkpoint: Checkpoint = {
      id: `CP-${Date.now()}`,
      timestamp: new Date().toISOString(),
      lastEntryHash: this.lastHash ?? '',
      entryCount: this.entryCount,
      checkpointHash: '', // 後で計算
    };

    // チェックポイントハッシュを計算
    checkpoint.checkpointHash = this.computeCheckpointHash(checkpoint);

    this.checkpoints.push(checkpoint);
    await this.saveCheckpoints();

    return checkpoint;
  }

  /**
   * 古いログをアーカイブ
   */
  async archive(options?: { beforeDate?: Date; force?: boolean }): Promise<ArchiveResult> {
    await this.initialize();

    const cutoffDate = options?.beforeDate ?? new Date(Date.now() - this.config.retentionDays * 24 * 60 * 60 * 1000);
    const entries = await this.readAllEntries();

    // アーカイブ対象を抽出
    const toArchive = entries.filter((e) => new Date(e.timestamp) < cutoffDate);

    if (toArchive.length === 0 && !options?.force) {
      return {
        success: true,
        archivedCount: 0,
      };
    }

    try {
      // アーカイブファイル作成
      const archiveName = `audit-archive-${cutoffDate.toISOString().split('T')[0]}.jsonl`;
      const archivePath = path.join(this.config.archiveDirectory, archiveName);

      // アーカイブディレクトリ確認
      if (!fs.existsSync(this.config.archiveDirectory)) {
        fs.mkdirSync(this.config.archiveDirectory, { recursive: true });
      }

      // アーカイブ書き込み
      const archiveContent = toArchive.map((e) => JSON.stringify(e)).join('\n') + '\n';
      fs.writeFileSync(archivePath, archiveContent);

      // アーカイブハッシュ計算
      const archiveHash = crypto.createHash('sha256').update(archiveContent).digest('hex');

      // ハッシュファイル作成
      fs.writeFileSync(`${archivePath}.sha256`, archiveHash);

      // 元のログからアーカイブ済みを削除
      const remaining = entries.filter((e) => new Date(e.timestamp) >= cutoffDate);
      await this.rewriteLog(remaining);

      return {
        success: true,
        archivedCount: toArchive.length,
        archivePath,
        archiveHash,
      };
    } catch (error) {
      return {
        success: false,
        archivedCount: 0,
        error: error instanceof Error ? error.message : 'Unknown error',
      };
    }
  }

  /**
   * エントリを検索
   */
  async query(filter: {
    eventTypes?: AuditEventType[];
    results?: AuditResult[];
    startDate?: Date;
    endDate?: Date;
    correlationId?: string;
    artifactId?: string;
    limit?: number;
  }): Promise<AuditLogEntry[]> {
    await this.initialize();

    const entries = await this.readAllEntries();

    return entries
      .filter((entry) => {
        if (filter.eventTypes && !filter.eventTypes.includes(entry.eventType)) {
          return false;
        }
        if (filter.results && !filter.results.includes(entry.result)) {
          return false;
        }
        if (filter.startDate && new Date(entry.timestamp) < filter.startDate) {
          return false;
        }
        if (filter.endDate && new Date(entry.timestamp) > filter.endDate) {
          return false;
        }
        if (filter.correlationId && entry.correlationId !== filter.correlationId) {
          return false;
        }
        if (filter.artifactId && !entry.artifactIds.includes(filter.artifactId)) {
          return false;
        }
        return true;
      })
      .slice(0, filter.limit ?? 1000);
  }

  /**
   * 統計を取得
   */
  async getStats(): Promise<{
    totalEntries: number;
    entriesByType: Record<AuditEventType, number>;
    entriesByResult: Record<AuditResult, number>;
    checkpointCount: number;
    lastEntryTimestamp?: string;
  }> {
    await this.initialize();

    const entries = await this.readAllEntries();

    const entriesByType: Record<string, number> = {};
    const entriesByResult: Record<string, number> = {};

    for (const entry of entries) {
      entriesByType[entry.eventType] = (entriesByType[entry.eventType] ?? 0) + 1;
      entriesByResult[entry.result] = (entriesByResult[entry.result] ?? 0) + 1;
    }

    return {
      totalEntries: entries.length,
      entriesByType: entriesByType as Record<AuditEventType, number>,
      entriesByResult: entriesByResult as Record<AuditResult, number>,
      checkpointCount: this.checkpoints.length,
      lastEntryTimestamp: entries.length > 0 ? entries[entries.length - 1].timestamp : undefined,
    };
  }

  // ============================================================================
  // Private Methods
  // ============================================================================

  /**
   * ディレクトリを確認・作成
   */
  private ensureDirectories(): void {
    if (!fs.existsSync(this.config.logDirectory)) {
      fs.mkdirSync(this.config.logDirectory, { recursive: true });
    }
    if (!fs.existsSync(this.config.archiveDirectory)) {
      fs.mkdirSync(this.config.archiveDirectory, { recursive: true });
    }
  }

  /**
   * 既存状態を読み込み
   */
  private async loadExistingState(): Promise<void> {
    // チェックポイント読み込み
    const checkpointPath = path.join(this.config.logDirectory, CHECKPOINT_FILE_NAME);
    if (fs.existsSync(checkpointPath)) {
      const content = fs.readFileSync(checkpointPath, 'utf-8');
      this.checkpoints = JSON.parse(content);
    }

    // 最後のハッシュを取得
    const entries = await this.readAllEntries();
    if (entries.length > 0) {
      this.lastHash = entries[entries.length - 1].hash;
      this.entryCount = entries.length;
    }
  }

  /**
   * すべてのエントリを読み込み
   */
  private async readAllEntries(): Promise<AuditLogEntry[]> {
    const logPath = path.join(this.config.logDirectory, LOG_FILE_NAME);
    if (!fs.existsSync(logPath)) {
      return [];
    }

    const content = fs.readFileSync(logPath, 'utf-8');
    return content
      .split('\n')
      .filter((line) => line.trim())
      .map((line) => JSON.parse(line) as AuditLogEntry);
  }

  /**
   * エントリを追記
   */
  private async appendEntry(entry: AuditLogEntry): Promise<void> {
    const logPath = path.join(this.config.logDirectory, LOG_FILE_NAME);
    fs.appendFileSync(logPath, JSON.stringify(entry) + '\n');
  }

  /**
   * ログを書き換え
   */
  private async rewriteLog(entries: AuditLogEntry[]): Promise<void> {
    const logPath = path.join(this.config.logDirectory, LOG_FILE_NAME);
    const content = entries.map((e) => JSON.stringify(e)).join('\n') + (entries.length > 0 ? '\n' : '');
    fs.writeFileSync(logPath, content);

    // 状態更新
    if (entries.length > 0) {
      this.lastHash = entries[entries.length - 1].hash;
      this.entryCount = entries.length;
    } else {
      this.lastHash = null;
      this.entryCount = 0;
    }
  }

  /**
   * チェックポイントを保存
   */
  private async saveCheckpoints(): Promise<void> {
    const checkpointPath = path.join(this.config.logDirectory, CHECKPOINT_FILE_NAME);
    fs.writeFileSync(checkpointPath, JSON.stringify(this.checkpoints, null, 2));
  }

  /**
   * エントリのハッシュを計算
   */
  private computeEntryHash(entry: AuditLogEntry): string {
    const data = {
      version: entry.version,
      timestamp: entry.timestamp,
      correlationId: entry.correlationId,
      eventType: entry.eventType,
      artifactIds: entry.artifactIds,
      result: entry.result,
      summary: entry.summary,
      evidenceRef: entry.evidenceRef,
      prevHash: entry.prevHash,
    };
    return crypto.createHash('sha256').update(JSON.stringify(data)).digest('hex').slice(0, 16);
  }

  /**
   * チェックポイントのハッシュを計算
   */
  private computeCheckpointHash(checkpoint: Checkpoint): string {
    const data = {
      id: checkpoint.id,
      timestamp: checkpoint.timestamp,
      lastEntryHash: checkpoint.lastEntryHash,
      entryCount: checkpoint.entryCount,
    };
    return crypto.createHash('sha256').update(JSON.stringify(data)).digest('hex').slice(0, 16);
  }

  /**
   * 相関IDを生成
   */
  private generateCorrelationId(): string {
    return `AUDIT-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
  }

  /**
   * アーカイブが必要か確認して実行
   */
  private async checkAndArchive(): Promise<void> {
    const logPath = path.join(this.config.logDirectory, LOG_FILE_NAME);
    if (!fs.existsSync(logPath)) return;

    const stats = fs.statSync(logPath);
    if (stats.size > this.config.maxLogFileSize) {
      await this.archive();
    }
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * AuditLoggerを作成
 */
export function createAuditLogger(config?: AuditLoggerConfig): AuditLogger {
  return new AuditLogger(config);
}

/**
 * シングルトンインスタンス
 */
let defaultAuditLogger: AuditLogger | null = null;

/**
 * デフォルトのAuditLoggerを取得
 */
export function getDefaultAuditLogger(): AuditLogger {
  if (!defaultAuditLogger) {
    defaultAuditLogger = new AuditLogger();
  }
  return defaultAuditLogger;
}

/**
 * 監査ログを記録（簡易関数）
 */
export async function auditLog(
  eventType: AuditEventType,
  result: AuditResult,
  summary: string,
  options?: {
    artifactIds?: string[];
    evidenceRef?: string;
    correlationId?: string;
    metadata?: Record<string, unknown>;
  },
): Promise<AuditLogEntry> {
  const logger = getDefaultAuditLogger();
  return logger.log({
    eventType,
    result,
    summary,
    artifactIds: options?.artifactIds ?? [],
    evidenceRef: options?.evidenceRef,
    correlationId: options?.correlationId,
    metadata: options?.metadata,
  });
}
