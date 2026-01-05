/**
 * Conflict Resolver
 *
 * @module learning/sharing/conflict-resolver
 * @description パターン競合の検出と解決
 * @requirements REQ-SHARE-005
 * @design DES-SHARE-005
 */

import type {
  SharedPattern,
  Conflict,
  ConflictStrategy,
  Resolution,
} from './types.js';

/**
 * 競合解決のコールバック（'prompt'戦略用）
 */
export type ConflictPromptCallback = (conflict: Conflict) => Promise<ConflictStrategy>;

/**
 * 競合解決オプション
 */
export interface ResolverOptions {
  /** デフォルト戦略 */
  defaultStrategy: ConflictStrategy;
  /** マージ時に信頼度が高い方を優先 */
  preferHigherConfidence: boolean;
  /** マージ時に新しい方を優先 */
  preferNewer: boolean;
  /** プロンプトコールバック */
  promptCallback?: ConflictPromptCallback;
}

/**
 * デフォルトオプション
 */
const DEFAULT_OPTIONS: ResolverOptions = {
  defaultStrategy: 'skip',
  preferHigherConfidence: true,
  preferNewer: true,
};

/**
 * 競合解決器
 * REQ-SHARE-005: 競合解決戦略
 */
export class ConflictResolver {
  private strategy: ConflictStrategy;
  private options: ResolverOptions;
  private localPatterns: Map<string, SharedPattern> = new Map();

  constructor(options: Partial<ResolverOptions> = {}) {
    this.options = { ...DEFAULT_OPTIONS, ...options };
    this.strategy = this.options.defaultStrategy;
  }

  /**
   * 解決戦略を設定
   */
  setStrategy(strategy: ConflictStrategy): void {
    this.strategy = strategy;
  }

  /**
   * 現在の戦略を取得
   */
  getStrategy(): ConflictStrategy {
    return this.strategy;
  }

  /**
   * ローカルパターンを設定
   */
  setLocalPatterns(patterns: SharedPattern[]): void {
    this.localPatterns.clear();
    for (const pattern of patterns) {
      this.localPatterns.set(pattern.id, pattern);
    }
  }

  /**
   * ローカルパターンを追加
   */
  addLocalPattern(pattern: SharedPattern): void {
    this.localPatterns.set(pattern.id, pattern);
  }

  /**
   * 競合を検出
   */
  detectConflicts(remotePatterns: SharedPattern[]): Conflict[] {
    const conflicts: Conflict[] = [];

    for (const remote of remotePatterns) {
      // ID競合
      const localById = this.localPatterns.get(remote.id);
      if (localById) {
        const conflict = this.createConflict(localById, remote, 'id');
        if (conflict) {
          conflicts.push(conflict);
        }
        continue;
      }

      // 名前競合
      const localByName = this.findByName(remote.name);
      if (localByName) {
        conflicts.push(this.createConflict(localByName, remote, 'name')!);
        continue;
      }

      // コンテンツ競合（類似テンプレート）
      const similar = this.findSimilar(remote);
      if (similar) {
        conflicts.push(this.createConflict(similar, remote, 'content')!);
      }
    }

    return conflicts;
  }

  /**
   * 競合を解決
   */
  async resolve(conflicts: Conflict[]): Promise<Resolution> {
    const resolvedPatterns: SharedPattern[] = [];
    const pendingConflicts: Conflict[] = [];

    for (const conflict of conflicts) {
      const strategy = await this.getStrategyForConflict(conflict);

      switch (strategy) {
        case 'keep-local':
          resolvedPatterns.push(conflict.localPattern);
          break;

        case 'keep-remote':
          resolvedPatterns.push(conflict.remotePattern);
          break;

        case 'merge':
          const merged = this.mergePatterns(conflict.localPattern, conflict.remotePattern);
          resolvedPatterns.push(merged);
          break;

        case 'prompt':
          // プロンプトでユーザーに確認
          if (this.options.promptCallback) {
            const userStrategy = await this.options.promptCallback(conflict);
            const result = await this.resolveWithStrategy(conflict, userStrategy);
            if (result) {
              resolvedPatterns.push(result);
            } else {
              pendingConflicts.push(conflict);
            }
          } else {
            pendingConflicts.push(conflict);
          }
          break;

        case 'skip':
        default:
          // スキップ - 何もしない
          pendingConflicts.push(conflict);
          break;
      }
    }

    return {
      resolvedCount: resolvedPatterns.length,
      resolvedPatterns,
      pendingConflicts,
      strategy: this.strategy,
    };
  }

  /**
   * 特定の戦略で解決
   */
  private async resolveWithStrategy(
    conflict: Conflict,
    strategy: ConflictStrategy
  ): Promise<SharedPattern | null> {
    switch (strategy) {
      case 'keep-local':
        return conflict.localPattern;
      case 'keep-remote':
        return conflict.remotePattern;
      case 'merge':
        return this.mergePatterns(conflict.localPattern, conflict.remotePattern);
      default:
        return null;
    }
  }

  /**
   * 競合に対する戦略を取得
   */
  private async getStrategyForConflict(conflict: Conflict): Promise<ConflictStrategy> {
    // バージョン競合は自動的にマージ
    if (conflict.type === 'version') {
      return 'merge';
    }

    // ID競合で同一内容なら skip
    if (
      conflict.type === 'id' &&
      this.arePatternsSame(conflict.localPattern, conflict.remotePattern)
    ) {
      return 'skip';
    }

    return this.strategy;
  }

  /**
   * 競合を作成
   */
  private createConflict(
    local: SharedPattern,
    remote: SharedPattern,
    type: Conflict['type']
  ): Conflict | null {
    // 完全に同じなら競合なし
    if (this.arePatternsSame(local, remote)) {
      return null;
    }

    let details: string;
    switch (type) {
      case 'id':
        details = `Both patterns have ID: ${local.id}`;
        break;
      case 'name':
        details = `Both patterns have name: ${local.name}`;
        break;
      case 'content':
        details = `Patterns have similar templates`;
        break;
      case 'version':
        details = `Local version: ${local.version}, Remote version: ${remote.version}`;
        break;
    }

    return {
      type,
      localPattern: local,
      remotePattern: remote,
      details,
    };
  }

  /**
   * 名前でパターンを検索
   */
  private findByName(name: string): SharedPattern | undefined {
    const normalizedName = name.toLowerCase().trim();
    for (const pattern of this.localPatterns.values()) {
      if (pattern.name.toLowerCase().trim() === normalizedName) {
        return pattern;
      }
    }
    return undefined;
  }

  /**
   * 類似パターンを検索
   */
  private findSimilar(remote: SharedPattern): SharedPattern | undefined {
    if (!remote.template) {
      return undefined;
    }

    const remoteTemplate = this.normalizeTemplate(remote.template);

    for (const pattern of this.localPatterns.values()) {
      if (!pattern.template) continue;

      const localTemplate = this.normalizeTemplate(pattern.template);
      const similarity = this.calculateSimilarity(localTemplate, remoteTemplate);

      // 80%以上の類似度で類似と判定
      if (similarity >= 0.8) {
        return pattern;
      }
    }

    return undefined;
  }

  /**
   * テンプレートを正規化
   */
  private normalizeTemplate(template: string): string {
    return template
      .replace(/\s+/g, ' ') // 空白を正規化
      .replace(/\/\/.*$/gm, '') // 単行コメント除去
      .replace(/\/\*[\s\S]*?\*\//g, '') // 複数行コメント除去
      .trim();
  }

  /**
   * 文字列の類似度を計算（Jaccard係数）
   */
  private calculateSimilarity(str1: string, str2: string): number {
    const set1 = new Set(str1.split(/\s+/));
    const set2 = new Set(str2.split(/\s+/));

    const intersection = new Set([...set1].filter((x) => set2.has(x)));
    const union = new Set([...set1, ...set2]);

    return intersection.size / union.size;
  }

  /**
   * パターンが同一かチェック
   */
  private arePatternsSame(p1: SharedPattern, p2: SharedPattern): boolean {
    return (
      p1.name === p2.name &&
      p1.category === p2.category &&
      p1.confidence === p2.confidence &&
      p1.template === p2.template &&
      p1.version === p2.version
    );
  }

  /**
   * パターンをマージ
   */
  private mergePatterns(local: SharedPattern, remote: SharedPattern): SharedPattern {
    const now = new Date().toISOString();

    // 信頼度が高い方を基準に
    let base = local;
    let other = remote;

    if (this.options.preferHigherConfidence && remote.confidence > local.confidence) {
      base = remote;
      other = local;
    } else if (
      this.options.preferNewer &&
      new Date(remote.updatedAt) > new Date(local.updatedAt)
    ) {
      base = remote;
      other = local;
    }

    // マージ
    return {
      id: local.id, // ローカルIDを維持
      name: base.name,
      category: base.category,
      description: this.mergeDescriptions(local.description, remote.description),
      confidence: Math.max(local.confidence, remote.confidence),
      usageCount: local.usageCount + remote.usageCount,
      template: base.template ?? other.template,
      context: this.mergeContexts(local.context, remote.context),
      metadata: this.mergeMetadata(local.metadata, remote.metadata),
      createdAt: local.createdAt < remote.createdAt ? local.createdAt : remote.createdAt,
      updatedAt: now,
      version: Math.max(local.version, remote.version) + 1,
    };
  }

  /**
   * 説明をマージ
   */
  private mergeDescriptions(local: string, remote: string): string {
    if (local === remote) return local;
    if (!local) return remote;
    if (!remote) return local;

    // より長い方を採用
    return local.length >= remote.length ? local : remote;
  }

  /**
   * コンテキストをマージ
   */
  private mergeContexts(
    local?: SharedPattern['context'],
    remote?: SharedPattern['context']
  ): SharedPattern['context'] {
    if (!local && !remote) return {};
    if (!local) return remote;
    if (!remote) return local;

    return {
      language: local.language ?? remote.language,
      framework: local.framework ?? remote.framework,
      domain: local.domain ?? remote.domain,
      applicableWhen: [
        ...new Set([...(local.applicableWhen ?? []), ...(remote.applicableWhen ?? [])]),
      ],
      prerequisites: [
        ...new Set([...(local.prerequisites ?? []), ...(remote.prerequisites ?? [])]),
      ],
    };
  }

  /**
   * メタデータをマージ
   */
  private mergeMetadata(
    local: SharedPattern['metadata'],
    remote: SharedPattern['metadata']
  ): SharedPattern['metadata'] {
    return {
      source: local.source,
      importedFrom: remote.importedFrom ?? local.importedFrom,
      originalId: remote.originalId ?? local.originalId,
      tags: [...new Set([...(local.tags ?? []), ...(remote.tags ?? [])])],
      author: local.author ?? remote.author,
      license: local.license ?? remote.license,
    };
  }

  /**
   * プロンプトコールバックを設定
   */
  setPromptCallback(callback: ConflictPromptCallback): void {
    this.options.promptCallback = callback;
  }

  /**
   * ローカルパターン数を取得
   */
  getLocalPatternCount(): number {
    return this.localPatterns.size;
  }

  /**
   * ローカルパターンをクリア
   */
  clearLocalPatterns(): void {
    this.localPatterns.clear();
  }
}
