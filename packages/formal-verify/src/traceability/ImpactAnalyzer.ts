/**
 * Impact Analyzer
 * 
 * 変更の影響範囲を分析するクラス
 */

import type { TraceabilityDB } from './TraceabilityDB.js';
import type {
  ImpactResult,
  ImpactedNode,
  TraceNodeType,
  TraceLinkType,
} from './types.js';

/**
 * 影響分析オプション
 */
export interface ImpactAnalysisOptions {
  /** 最大分析深度 */
  maxDepth?: number;
  /** 追跡するリンクタイプ */
  linkTypes?: TraceLinkType[];
  /** 分析対象のノードタイプ */
  nodeTypes?: TraceNodeType[];
  /** 影響度の減衰率（深さごと） */
  decayRate?: number;
  /** 最小影響度のしきい値 */
  minImpactScore?: number;
}

/**
 * 影響分析器
 * 
 * トレーサビリティDBを使用して、特定のノードが変更された場合の
 * 影響範囲を分析します。
 * 
 * @example
 * ```typescript
 * const db = new TraceabilityDB('./trace.db');
 * const analyzer = new ImpactAnalyzer(db);
 * 
 * // REQ-001が変更された場合の影響分析
 * const impact = await analyzer.analyze('REQ-001');
 * 
 * console.log(`影響を受けるノード: ${impact.totalImpacted}件`);
 * for (const node of impact.impactedNodes) {
 *   console.log(`- ${node.id}: 影響度 ${node.impactScore}`);
 * }
 * ```
 */
export class ImpactAnalyzer {
  private readonly db: TraceabilityDB;

  constructor(db: TraceabilityDB) {
    this.db = db;
  }

  /**
   * 影響分析を実行
   * 
   * @param sourceId - 変更の起点となるノードID
   * @param options - 分析オプション
   * @returns 影響分析結果
   */
  async analyze(
    sourceId: string,
    options: ImpactAnalysisOptions = {}
  ): Promise<ImpactResult> {
    const startTime = Date.now();

    const {
      maxDepth = 5,
      linkTypes,
      nodeTypes,
      decayRate = 0.7,
      minImpactScore = 0.1,
    } = options;

    const impactedNodes: ImpactedNode[] = [];
    const visited = new Set<string>();
    
    // BFSで影響範囲を探索
    const queue: {
      id: string;
      depth: number;
      path: string[];
      linkType: TraceLinkType;
      impactScore: number;
    }[] = [];

    // 初期ノードの隣接ノードをキューに追加
    const initialLinks = await this.getOutgoingLinks(sourceId, linkTypes);
    for (const link of initialLinks) {
      queue.push({
        id: link.target,
        depth: 1,
        path: [sourceId, link.target],
        linkType: link.type as TraceLinkType,
        impactScore: 1.0 * decayRate,
      });
    }

    visited.add(sourceId);

    while (queue.length > 0) {
      const current = queue.shift()!;

      if (visited.has(current.id)) {
        continue;
      }
      
      if (current.depth > maxDepth) {
        continue;
      }

      if (current.impactScore < minImpactScore) {
        continue;
      }

      visited.add(current.id);

      // ノード情報を取得
      const node = await this.db.getNode(current.id);
      if (!node) {
        continue;
      }

      // ノードタイプフィルタ
      if (nodeTypes && !nodeTypes.includes(node.type)) {
        continue;
      }

      // 影響ノードとして追加
      impactedNodes.push({
        id: node.id,
        type: node.type,
        title: node.title,
        distance: current.depth,
        path: current.path,
        linkType: current.linkType,
        impactScore: current.impactScore,
      });

      // 次の隣接ノードをキューに追加
      const nextLinks = await this.getOutgoingLinks(current.id, linkTypes);
      for (const link of nextLinks) {
        if (!visited.has(link.target)) {
          queue.push({
            id: link.target,
            depth: current.depth + 1,
            path: [...current.path, link.target],
            linkType: link.type as TraceLinkType,
            impactScore: current.impactScore * decayRate,
          });
        }
      }
    }

    // 影響度でソート
    impactedNodes.sort((a, b) => b.impactScore - a.impactScore);

    return {
      sourceId,
      impactedNodes,
      depth: Math.max(0, ...impactedNodes.map(n => n.distance)),
      totalImpacted: impactedNodes.length,
      duration: Date.now() - startTime,
    };
  }

  /**
   * 逆方向の影響分析（依存元を探す）
   * 
   * @param targetId - 調査対象のノードID
   * @param options - 分析オプション
   */
  async analyzeReverse(
    targetId: string,
    options: ImpactAnalysisOptions = {}
  ): Promise<ImpactResult> {
    const startTime = Date.now();

    const {
      maxDepth = 5,
      linkTypes,
      nodeTypes,
      decayRate = 0.7,
      minImpactScore = 0.1,
    } = options;

    const impactedNodes: ImpactedNode[] = [];
    const visited = new Set<string>();
    
    const queue: {
      id: string;
      depth: number;
      path: string[];
      linkType: TraceLinkType;
      impactScore: number;
    }[] = [];

    // 初期ノードの入力リンクをキューに追加
    const initialLinks = await this.getIncomingLinks(targetId, linkTypes);
    for (const link of initialLinks) {
      queue.push({
        id: link.source,
        depth: 1,
        path: [targetId, link.source],
        linkType: link.type as TraceLinkType,
        impactScore: 1.0 * decayRate,
      });
    }

    visited.add(targetId);

    while (queue.length > 0) {
      const current = queue.shift()!;

      if (visited.has(current.id) || current.depth > maxDepth || current.impactScore < minImpactScore) {
        continue;
      }

      visited.add(current.id);

      const node = await this.db.getNode(current.id);
      if (!node) continue;

      if (nodeTypes && !nodeTypes.includes(node.type)) continue;

      impactedNodes.push({
        id: node.id,
        type: node.type,
        title: node.title,
        distance: current.depth,
        path: current.path,
        linkType: current.linkType,
        impactScore: current.impactScore,
      });

      const nextLinks = await this.getIncomingLinks(current.id, linkTypes);
      for (const link of nextLinks) {
        if (!visited.has(link.source)) {
          queue.push({
            id: link.source,
            depth: current.depth + 1,
            path: [...current.path, link.source],
            linkType: link.type as TraceLinkType,
            impactScore: current.impactScore * decayRate,
          });
        }
      }
    }

    impactedNodes.sort((a, b) => b.impactScore - a.impactScore);

    return {
      sourceId: targetId,
      impactedNodes,
      depth: Math.max(0, ...impactedNodes.map(n => n.distance)),
      totalImpacted: impactedNodes.length,
      duration: Date.now() - startTime,
    };
  }

  /**
   * カバレッジ分析
   * 
   * 要件がどの程度テストでカバーされているかを分析
   */
  async analyzeCoverage(
    requirementType: TraceNodeType = 'requirement',
    testType: TraceNodeType = 'test'
  ): Promise<CoverageResult> {
    const requirements = await this.db.getNodesByType(requirementType);
    const tests = await this.db.getNodesByType(testType);

    const covered: string[] = [];
    const uncovered: string[] = [];

    for (const req of requirements) {
      const impact = await this.analyze(req.id, {
        maxDepth: 10,
        nodeTypes: [testType],
      });

      if (impact.totalImpacted > 0) {
        covered.push(req.id);
      } else {
        uncovered.push(req.id);
      }
    }

    const coveragePercentage = requirements.length > 0
      ? (covered.length / requirements.length) * 100
      : 0;

    return {
      totalRequirements: requirements.length,
      coveredRequirements: covered.length,
      uncoveredRequirements: uncovered.length,
      coveragePercentage,
      covered,
      uncovered,
      totalTests: tests.length,
    };
  }

  /**
   * 循環依存を検出
   */
  async detectCycles(): Promise<string[][]> {
    const cycles: string[][] = [];
    const visited = new Set<string>();
    const recursionStack = new Set<string>();

    const stats = await this.db.getStats();
    const allNodeTypes: TraceNodeType[] = Object.keys(stats.nodesByType) as TraceNodeType[];

    for (const nodeType of allNodeTypes) {
      const nodes = await this.db.getNodesByType(nodeType);
      
      for (const node of nodes) {
        if (!visited.has(node.id)) {
          await this.detectCyclesDFS(node.id, visited, recursionStack, [], cycles);
        }
      }
    }

    return cycles;
  }

  /**
   * DFSで循環を検出
   */
  private async detectCyclesDFS(
    nodeId: string,
    visited: Set<string>,
    recursionStack: Set<string>,
    path: string[],
    cycles: string[][]
  ): Promise<void> {
    visited.add(nodeId);
    recursionStack.add(nodeId);
    path.push(nodeId);

    const links = await this.getOutgoingLinks(nodeId);
    
    for (const link of links) {
      if (!visited.has(link.target)) {
        await this.detectCyclesDFS(link.target, visited, recursionStack, [...path], cycles);
      } else if (recursionStack.has(link.target)) {
        // 循環を検出
        const cycleStart = path.indexOf(link.target);
        const cycle = path.slice(cycleStart);
        cycle.push(link.target); // サイクルを閉じる
        cycles.push(cycle);
      }
    }

    recursionStack.delete(nodeId);
  }

  /**
   * 出力リンクを取得
   */
  private async getOutgoingLinks(
    nodeId: string,
    linkTypes?: TraceLinkType[]
  ): Promise<{ target: string; type: string }[]> {
    const result = await this.db.query(nodeId, {
      direction: 'forward',
      linkTypes,
      maxDepth: 1,
    });

    return result.links
      .filter(link => link.source === nodeId)
      .map(link => ({ target: link.target, type: link.type }));
  }

  /**
   * 入力リンクを取得
   */
  private async getIncomingLinks(
    nodeId: string,
    linkTypes?: TraceLinkType[]
  ): Promise<{ source: string; type: string }[]> {
    const result = await this.db.query(nodeId, {
      direction: 'backward',
      linkTypes,
      maxDepth: 1,
    });

    return result.links
      .filter(link => link.target === nodeId)
      .map(link => ({ source: link.source, type: link.type }));
  }
}

/**
 * カバレッジ分析結果
 */
export interface CoverageResult {
  /** 総要件数 */
  totalRequirements: number;
  /** カバーされた要件数 */
  coveredRequirements: number;
  /** カバーされていない要件数 */
  uncoveredRequirements: number;
  /** カバレッジ率 */
  coveragePercentage: number;
  /** カバーされた要件のID */
  covered: string[];
  /** カバーされていない要件のID */
  uncovered: string[];
  /** 総テスト数 */
  totalTests: number;
}
