/**
 * Traceability Database
 * 
 * SQLiteベースのトレーサビリティデータベース
 */

import Database from 'better-sqlite3';
import type {
  TraceNode,
  TraceNodeInput,
  TraceLink,
  TraceLinkType,
  TraceNodeType,
  TraceQueryOptions,
  TraceQueryResult,
  TraceDbStats,
} from './types.js';

/**
 * トレーサビリティDB
 * 
 * 要件↔設計↔コード↔テストのトレーサビリティを管理するSQLiteベースのデータベース。
 * グラフ構造でノード間の関係を追跡し、影響分析やカバレッジ計算を支援します。
 * 
 * @example
 * ```typescript
 * const db = new TraceabilityDB('./trace.db');
 * 
 * // ノードを追加
 * await db.addNode({
 *   id: 'REQ-001',
 *   type: 'requirement',
 *   title: 'User Authentication',
 *   createdAt: new Date(),
 *   updatedAt: new Date(),
 * });
 * 
 * // リンクを追加
 * await db.addLink({
 *   source: 'REQ-001',
 *   target: 'DES-001',
 *   type: 'implements',
 * });
 * 
 * // クエリ
 * const related = await db.query('REQ-001', { direction: 'forward' });
 * ```
 */
export class TraceabilityDB {
  private db: Database.Database;
  private readonly _dbPath: string;

  constructor(dbPath: string = ':memory:') {
    this._dbPath = dbPath;
    this.db = new Database(dbPath);
    this.initializeSchema();
  }

  /**
   * データベーススキーマを初期化
   */
  private initializeSchema(): void {
    this.db.exec(`
      -- ノードテーブル
      CREATE TABLE IF NOT EXISTS nodes (
        id TEXT PRIMARY KEY,
        type TEXT NOT NULL,
        title TEXT NOT NULL,
        description TEXT,
        version TEXT,
        created_at TEXT NOT NULL,
        updated_at TEXT NOT NULL,
        metadata TEXT
      );

      -- リンクテーブル
      CREATE TABLE IF NOT EXISTS links (
        id TEXT PRIMARY KEY,
        source TEXT NOT NULL,
        target TEXT NOT NULL,
        type TEXT NOT NULL,
        description TEXT,
        confidence REAL DEFAULT 1.0,
        created_at TEXT NOT NULL,
        metadata TEXT,
        FOREIGN KEY (source) REFERENCES nodes(id),
        FOREIGN KEY (target) REFERENCES nodes(id)
      );

      -- インデックス
      CREATE INDEX IF NOT EXISTS idx_nodes_type ON nodes(type);
      CREATE INDEX IF NOT EXISTS idx_links_source ON links(source);
      CREATE INDEX IF NOT EXISTS idx_links_target ON links(target);
      CREATE INDEX IF NOT EXISTS idx_links_type ON links(type);
    `);
  }

  /**
   * ノードを追加
   * @throws Error 既に同じIDのノードが存在する場合
   */
  async addNode(input: TraceNodeInput): Promise<TraceNode> {
    // 重複チェック
    const existing = await this.getNode(input.id);
    if (existing) {
      throw new Error(`Node with ID '${input.id}' already exists`);
    }

    const now = new Date();
    const node: TraceNode = {
      ...input,
      createdAt: input.createdAt ?? now,
      updatedAt: input.updatedAt ?? now,
    };

    const stmt = this.db.prepare(`
      INSERT INTO nodes (id, type, title, description, version, created_at, updated_at, metadata)
      VALUES (?, ?, ?, ?, ?, ?, ?, ?)
    `);

    stmt.run(
      node.id,
      node.type,
      node.title,
      node.description ?? null,
      node.version ?? null,
      node.createdAt.toISOString(),
      node.updatedAt.toISOString(),
      node.metadata ? JSON.stringify(node.metadata) : null
    );

    return node;
  }

  /**
   * ノードを取得
   */
  async getNode(id: string): Promise<TraceNode | null> {
    const stmt = this.db.prepare('SELECT * FROM nodes WHERE id = ?');
    const row = stmt.get(id) as DbNodeRow | undefined;

    if (!row) return null;

    return this.rowToNode(row);
  }

  /**
   * ノードを更新
   */
  async updateNode(id: string, updates: Partial<TraceNode>): Promise<void> {
    const node = await this.getNode(id);
    if (!node) {
      throw new Error(`Node not found: ${id}`);
    }

    const updated: TraceNode = {
      ...node,
      ...updates,
      id, // IDは変更不可
      updatedAt: new Date(),
    };

    const stmt = this.db.prepare(`
      UPDATE nodes 
      SET type = ?, title = ?, description = ?, version = ?, updated_at = ?, metadata = ?
      WHERE id = ?
    `);

    stmt.run(
      updated.type,
      updated.title,
      updated.description ?? null,
      updated.version ?? null,
      updated.updatedAt.toISOString(),
      updated.metadata ? JSON.stringify(updated.metadata) : null,
      id
    );
  }

  /**
   * ノードを削除
   */
  async deleteNode(id: string): Promise<void> {
    // 関連リンクも削除
    this.db.prepare('DELETE FROM links WHERE source = ? OR target = ?').run(id, id);
    this.db.prepare('DELETE FROM nodes WHERE id = ?').run(id);
  }

  /**
   * ノードを削除（deleteNodeのエイリアス）
   */
  async removeNode(id: string): Promise<void> {
    return this.deleteNode(id);
  }

  /**
   * リンクを追加
   * @throws Error ソースまたはターゲットノードが存在しない場合
   */
  async addLink(link: Omit<TraceLink, 'id' | 'createdAt'> & { id?: string; createdAt?: Date }): Promise<TraceLink> {
    // ソースノードの存在チェック
    const sourceNode = await this.getNode(link.source);
    if (!sourceNode) {
      throw new Error(`Source node not found: ${link.source}`);
    }

    // ターゲットノードの存在チェック
    const targetNode = await this.getNode(link.target);
    if (!targetNode) {
      throw new Error(`Target node not found: ${link.target}`);
    }

    const linkId = link.id ?? this.generateLinkId(link as TraceLink);
    const createdAt = link.createdAt ?? new Date();
    
    const stmt = this.db.prepare(`
      INSERT OR REPLACE INTO links (id, source, target, type, description, confidence, created_at, metadata)
      VALUES (?, ?, ?, ?, ?, ?, ?, ?)
    `);

    stmt.run(
      linkId,
      link.source,
      link.target,
      link.type,
      link.description ?? null,
      link.confidence ?? 1.0,
      createdAt.toISOString(),
      link.metadata ? JSON.stringify(link.metadata) : null
    );

    return {
      id: linkId,
      source: link.source,
      target: link.target,
      type: link.type,
      description: link.description,
      confidence: link.confidence ?? 1.0,
      createdAt,
      metadata: link.metadata,
    };
  }

  /**
   * リンクを取得
   */
  async getLink(id: string): Promise<TraceLink | null> {
    const stmt = this.db.prepare('SELECT * FROM links WHERE id = ?');
    const row = stmt.get(id) as DbLinkRow | undefined;

    if (!row) return null;

    return this.rowToLink(row);
  }

  /**
   * ノード間のリンクを取得
   */
  async getLinksBetween(source: string, target: string): Promise<TraceLink[]> {
    const stmt = this.db.prepare(
      'SELECT * FROM links WHERE source = ? AND target = ?'
    );
    const rows = stmt.all(source, target) as DbLinkRow[];

    return rows.map(row => this.rowToLink(row));
  }

  /**
   * リンクを削除
   */
  async deleteLink(id: string): Promise<void> {
    this.db.prepare('DELETE FROM links WHERE id = ?').run(id);
  }

  /**
   * ノードをクエリ
   */
  async query(nodeId: string, options: TraceQueryOptions = {}): Promise<TraceQueryResult> {
    const source = await this.getNode(nodeId);
    const relatedNodes: TraceNode[] = [];
    const links: TraceLink[] = [];
    const paths: string[][] = [];

    const {
      linkTypes,
      nodeTypes,
      maxDepth = 10,
      direction = 'both',
      minConfidence = 0,
    } = options;

    const visited = new Set<string>();
    const queue: { id: string; depth: number; path: string[] }[] = [
      { id: nodeId, depth: 0, path: [nodeId] },
    ];

    while (queue.length > 0) {
      const current = queue.shift()!;
      
      if (visited.has(current.id) || current.depth > maxDepth) {
        continue;
      }
      visited.add(current.id);

      // 関連リンクを取得
      const relatedLinks = await this.getRelatedLinks(
        current.id,
        direction,
        linkTypes,
        minConfidence
      );

      for (const link of relatedLinks) {
        links.push(link);

        const nextId = link.source === current.id ? link.target : link.source;
        
        if (!visited.has(nextId)) {
          const nextNode = await this.getNode(nextId);
          
          if (nextNode && (!nodeTypes || nodeTypes.includes(nextNode.type))) {
            relatedNodes.push(nextNode);
            const newPath = [...current.path, nextId];
            paths.push(newPath);
            
            queue.push({
              id: nextId,
              depth: current.depth + 1,
              path: newPath,
            });
          }
        }
      }
    }

    return {
      source,
      relatedNodes,
      links,
      paths,
    };
  }

  /**
   * 関連リンクを取得
   */
  private async getRelatedLinks(
    nodeId: string,
    direction: 'forward' | 'backward' | 'both',
    linkTypes?: TraceLinkType[],
    minConfidence?: number
  ): Promise<TraceLink[]> {
    let sql = '';
    const params: unknown[] = [];

    if (direction === 'forward') {
      sql = 'SELECT * FROM links WHERE source = ?';
      params.push(nodeId);
    } else if (direction === 'backward') {
      sql = 'SELECT * FROM links WHERE target = ?';
      params.push(nodeId);
    } else {
      sql = 'SELECT * FROM links WHERE source = ? OR target = ?';
      params.push(nodeId, nodeId);
    }

    if (linkTypes && linkTypes.length > 0) {
      sql += ` AND type IN (${linkTypes.map(() => '?').join(', ')})`;
      params.push(...linkTypes);
    }

    if (minConfidence !== undefined && minConfidence > 0) {
      sql += ' AND confidence >= ?';
      params.push(minConfidence);
    }

    const stmt = this.db.prepare(sql);
    const rows = stmt.all(...params) as DbLinkRow[];

    return rows.map(row => this.rowToLink(row));
  }

  /**
   * タイプ別にノードを取得
   */
  async getNodesByType(type: TraceNodeType): Promise<TraceNode[]> {
    const stmt = this.db.prepare('SELECT * FROM nodes WHERE type = ?');
    const rows = stmt.all(type) as DbNodeRow[];

    return rows.map(row => this.rowToNode(row));
  }

  /**
   * 孤立ノードを取得
   */
  async getOrphanNodes(): Promise<TraceNode[]> {
    const stmt = this.db.prepare(`
      SELECT * FROM nodes
      WHERE id NOT IN (SELECT source FROM links)
      AND id NOT IN (SELECT target FROM links)
    `);
    const rows = stmt.all() as DbNodeRow[];

    return rows.map(row => this.rowToNode(row));
  }

  /**
   * 統計情報を取得
   */
  async getStats(): Promise<TraceDbStats> {
    const nodeCount = (this.db.prepare('SELECT COUNT(*) as count FROM nodes').get() as { count: number }).count;
    const linkCount = (this.db.prepare('SELECT COUNT(*) as count FROM links').get() as { count: number }).count;

    // ノードタイプ別カウント
    const nodesByTypeRows = this.db.prepare(
      'SELECT type, COUNT(*) as count FROM nodes GROUP BY type'
    ).all() as { type: TraceNodeType; count: number }[];
    
    const nodesByType = {} as Record<TraceNodeType, number>;
    for (const row of nodesByTypeRows) {
      nodesByType[row.type] = row.count;
    }

    // リンクタイプ別カウント
    const linksByTypeRows = this.db.prepare(
      'SELECT type, COUNT(*) as count FROM links GROUP BY type'
    ).all() as { type: TraceLinkType; count: number }[];
    
    const linksByType = {} as Record<TraceLinkType, number>;
    for (const row of linksByTypeRows) {
      linksByType[row.type] = row.count;
    }

    // 孤立ノード数
    const orphanNodes = (await this.getOrphanNodes()).length;

    // 最終更新日時
    const lastUpdatedRow = this.db.prepare(
      'SELECT MAX(updated_at) as last FROM nodes'
    ).get() as { last: string | null };
    
    const lastUpdated = lastUpdatedRow.last ? new Date(lastUpdatedRow.last) : null;

    return {
      nodeCount,
      linkCount,
      nodesByType,
      linksByType,
      orphanNodes,
      lastUpdated,
    };
  }

  /**
   * データベースを閉じる
   */
  close(): void {
    this.db.close();
  }

  /**
   * リンクIDを生成
   */
  private generateLinkId(link: TraceLink): string {
    return `${link.source}-${link.type}-${link.target}-${Date.now()}`;
  }

  /**
   * DBの行をノードに変換
   */
  private rowToNode(row: DbNodeRow): TraceNode {
    return {
      id: row.id,
      type: row.type as TraceNodeType,
      title: row.title,
      description: row.description ?? undefined,
      version: row.version ?? undefined,
      createdAt: new Date(row.created_at),
      updatedAt: new Date(row.updated_at),
      metadata: row.metadata ? JSON.parse(row.metadata) : undefined,
    };
  }

  /**
   * DBの行をリンクに変換
   */
  private rowToLink(row: DbLinkRow): TraceLink {
    return {
      id: row.id,
      source: row.source,
      target: row.target,
      type: row.type as TraceLinkType,
      description: row.description ?? undefined,
      confidence: row.confidence,
      createdAt: new Date(row.created_at),
      metadata: row.metadata ? JSON.parse(row.metadata) : undefined,
    };
  }
}

// DB行の型定義
interface DbNodeRow {
  id: string;
  type: string;
  title: string;
  description: string | null;
  version: string | null;
  created_at: string;
  updated_at: string;
  metadata: string | null;
}

interface DbLinkRow {
  id: string;
  source: string;
  target: string;
  type: string;
  description: string | null;
  confidence: number;
  created_at: string;
  metadata: string | null;
}
