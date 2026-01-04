/**
 * BaseRepository - 標準Repository基底インターフェース
 * 
 * @description 一貫したRepositoryパターンの実装を提供
 * @requirement REQ-MUSUBIX-LEARN-002 (SDD Workflow Feedback)
 * @version 1.1.3
 * 
 * 学習フィードバック PAT-005 の改善:
 * - Repository メソッドシグネチャの標準化
 * - updateMany(ids[], data) 形式を標準として採用
 * - コード一貫性の向上
 */

/**
 * 基底Repositoryインターフェース
 * 
 * @template T - エンティティ型
 * @template ID - IDの型（デフォルト: string）
 */
export interface IRepository<T, ID = string> {
  /**
   * エンティティを保存
   */
  save(entity: T): Promise<T>;

  /**
   * 複数エンティティを保存
   */
  saveMany(entities: T[]): Promise<T[]>;

  /**
   * IDでエンティティを検索
   */
  findById(id: ID): Promise<T | null>;

  /**
   * 全エンティティを取得
   */
  findAll(): Promise<T[]>;

  /**
   * エンティティを更新
   */
  update(id: ID, data: Partial<T>): Promise<T>;

  /**
   * 複数エンティティを一括更新（標準シグネチャ）
   * @param ids - 更新対象のID配列
   * @param data - 更新データ
   */
  updateMany(ids: ID[], data: Partial<T>): Promise<T[]>;

  /**
   * エンティティを削除
   */
  delete(id: ID): Promise<boolean>;
}

/**
 * 検索可能なRepositoryインターフェース
 */
export interface ISearchableRepository<T, ID = string> extends IRepository<T, ID> {
  /**
   * 条件で検索
   */
  findBy(criteria: Partial<T>): Promise<T[]>;

  /**
   * 条件で1件検索
   */
  findOneBy(criteria: Partial<T>): Promise<T | null>;

  /**
   * 件数をカウント
   */
  count(criteria?: Partial<T>): Promise<number>;
}

/**
 * ページネーション付きRepositoryインターフェース
 */
export interface IPaginatedRepository<T, ID = string> extends ISearchableRepository<T, ID> {
  /**
   * ページネーション付き検索
   */
  findPaginated(
    criteria: Partial<T>,
    options: PaginationOptions
  ): Promise<PaginatedResult<T>>;
}

/**
 * ページネーションオプション
 */
export interface PaginationOptions {
  page: number;
  limit: number;
  sortBy?: string;
  sortOrder?: 'asc' | 'desc';
}

/**
 * ページネーション結果
 */
export interface PaginatedResult<T> {
  data: T[];
  total: number;
  page: number;
  limit: number;
  totalPages: number;
  hasNext: boolean;
  hasPrev: boolean;
}

/**
 * インメモリRepository実装（テスト用）
 */
export class InMemoryRepository<T extends { id: string }> implements IRepository<T> {
  protected storage = new Map<string, T>();

  async save(entity: T): Promise<T> {
    this.storage.set(entity.id, { ...entity });
    return entity;
  }

  async saveMany(entities: T[]): Promise<T[]> {
    entities.forEach((e) => this.storage.set(e.id, { ...e }));
    return entities;
  }

  async findById(id: string): Promise<T | null> {
    const entity = this.storage.get(id);
    return entity ? { ...entity } : null;
  }

  async findAll(): Promise<T[]> {
    return Array.from(this.storage.values());
  }

  async update(id: string, data: Partial<T>): Promise<T> {
    const entity = this.storage.get(id);
    if (!entity) throw new Error(`Entity not found: ${id}`);
    const updated = { ...entity, ...data } as T;
    this.storage.set(id, updated);
    return updated;
  }

  async updateMany(ids: string[], data: Partial<T>): Promise<T[]> {
    return ids.map((id) => {
      const entity = this.storage.get(id);
      if (!entity) throw new Error(`Entity not found: ${id}`);
      const updated = { ...entity, ...data } as T;
      this.storage.set(id, updated);
      return updated;
    });
  }

  async delete(id: string): Promise<boolean> {
    return this.storage.delete(id);
  }

  /**
   * テスト用: ストレージをクリア
   */
  clear(): void {
    this.storage.clear();
  }

  /**
   * テスト用: 現在の件数を取得
   */
  size(): number {
    return this.storage.size;
  }
}

/**
 * 検索可能なインメモリRepository実装
 */
export class SearchableInMemoryRepository<T extends { id: string }> 
  extends InMemoryRepository<T> 
  implements ISearchableRepository<T> {

  async findBy(criteria: Partial<T>): Promise<T[]> {
    return Array.from(this.storage.values()).filter((entity) => {
      return Object.entries(criteria).every(([key, value]) => {
        return (entity as Record<string, unknown>)[key] === value;
      });
    });
  }

  async findOneBy(criteria: Partial<T>): Promise<T | null> {
    const results = await this.findBy(criteria);
    return results[0] || null;
  }

  async count(criteria?: Partial<T>): Promise<number> {
    if (!criteria) return this.storage.size;
    const results = await this.findBy(criteria);
    return results.length;
  }
}

/**
 * Repository作成のファクトリー関数
 */
export function createInMemoryRepository<T extends { id: string }>(): InMemoryRepository<T> {
  return new InMemoryRepository<T>();
}

export function createSearchableRepository<T extends { id: string }>(): SearchableInMemoryRepository<T> {
  return new SearchableInMemoryRepository<T>();
}
