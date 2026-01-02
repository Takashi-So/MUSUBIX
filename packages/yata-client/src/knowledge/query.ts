/**
 * Graph Query Interface
 * 
 * Interface for querying YATA knowledge graph
 * 
 * @packageDocumentation
 * @module knowledge/query
 * 
 * @see REQ-INT-101 - YATA Integration
 * @see REQ-NS-101 - Symbolic Reasoning
 */

import type { YataMCPClient } from '../mcp/client.js';
import type {
  KnowledgeNode,
  KnowledgeEdge,
  KnowledgeQueryResult,
} from '../types.js';

/**
 * Query options for knowledge graph
 */
export interface QueryOptions {
  /** Maximum depth for traversal */
  maxDepth?: number;
  /** Maximum number of results */
  limit?: number;
  /** Node types to include */
  nodeTypes?: string[];
  /** Edge types to include */
  edgeTypes?: string[];
  /** Include metadata in results */
  includeMetadata?: boolean;
}

/**
 * Default query options
 */
export const DEFAULT_QUERY_OPTIONS: Required<QueryOptions> = {
  maxDepth: 3,
  limit: 100,
  nodeTypes: [],
  edgeTypes: [],
  includeMetadata: true,
};

/**
 * Path in knowledge graph
 */
export interface GraphPath {
  /** Nodes in path */
  nodes: KnowledgeNode[];
  /** Edges connecting nodes */
  edges: KnowledgeEdge[];
  /** Path length */
  length: number;
  /** Path weight (if applicable) */
  weight?: number;
}

/**
 * Subgraph result
 */
export interface Subgraph {
  /** Nodes in subgraph */
  nodes: KnowledgeNode[];
  /** Edges in subgraph */
  edges: KnowledgeEdge[];
  /** Root node ID */
  rootId: string;
}

/**
 * Graph Query Interface
 * 
 * Provides high-level query operations on YATA knowledge graph
 */
export class GraphQueryInterface {
  private client: YataMCPClient;
  private defaultOptions: Required<QueryOptions>;

  constructor(client: YataMCPClient, options?: Partial<QueryOptions>) {
    this.client = client;
    this.defaultOptions = { ...DEFAULT_QUERY_OPTIONS, ...options };
  }

  /**
   * Query nodes by type
   */
  async queryNodesByType(
    type: string,
    options?: Partial<QueryOptions>
  ): Promise<KnowledgeQueryResult> {
    const opts = this.mergeOptions(options);
    
    const response = await this.client.callTool<KnowledgeQueryResult>({
      name: 'query_graph',
      arguments: {
        query: {
          type: 'nodes_by_type',
          nodeType: type,
          limit: opts.limit,
          includeMetadata: opts.includeMetadata,
        },
      },
    });

    if (!response.success) {
      throw new Error(`Query failed: ${response.error}`);
    }

    return response.result!;
  }

  /**
   * Query nodes by property
   */
  async queryNodesByProperty(
    property: string,
    value: unknown,
    options?: Partial<QueryOptions>
  ): Promise<KnowledgeQueryResult> {
    const opts = this.mergeOptions(options);
    
    const response = await this.client.callTool<KnowledgeQueryResult>({
      name: 'query_graph',
      arguments: {
        query: {
          type: 'nodes_by_property',
          property,
          value,
          limit: opts.limit,
          includeMetadata: opts.includeMetadata,
        },
      },
    });

    if (!response.success) {
      throw new Error(`Query failed: ${response.error}`);
    }

    return response.result!;
  }

  /**
   * Get node by ID
   */
  async getNode(id: string): Promise<KnowledgeNode | null> {
    const response = await this.client.callTool<KnowledgeNode | null>({
      name: 'get_node',
      arguments: { id },
    });

    if (!response.success) {
      throw new Error(`Failed to get node: ${response.error}`);
    }

    return response.result ?? null;
  }

  /**
   * Get node neighbors
   */
  async getNeighbors(
    nodeId: string,
    options?: Partial<QueryOptions>
  ): Promise<KnowledgeQueryResult> {
    const opts = this.mergeOptions(options);
    
    const response = await this.client.callTool<KnowledgeQueryResult>({
      name: 'get_neighbors',
      arguments: {
        nodeId,
        maxDepth: opts.maxDepth,
        edgeTypes: opts.edgeTypes,
        limit: opts.limit,
      },
    });

    if (!response.success) {
      throw new Error(`Failed to get neighbors: ${response.error}`);
    }

    return response.result!;
  }

  /**
   * Find shortest path between nodes
   */
  async findPath(
    sourceId: string,
    targetId: string,
    options?: Partial<QueryOptions>
  ): Promise<GraphPath | null> {
    const opts = this.mergeOptions(options);
    
    const response = await this.client.callTool<GraphPath | null>({
      name: 'find_path',
      arguments: {
        sourceId,
        targetId,
        maxDepth: opts.maxDepth,
        edgeTypes: opts.edgeTypes,
      },
    });

    if (!response.success) {
      throw new Error(`Path search failed: ${response.error}`);
    }

    return response.result ?? null;
  }

  /**
   * Get subgraph from root node
   */
  async getSubgraph(
    rootId: string,
    options?: Partial<QueryOptions>
  ): Promise<Subgraph> {
    const opts = this.mergeOptions(options);
    
    const response = await this.client.callTool<Subgraph>({
      name: 'get_subgraph',
      arguments: {
        rootId,
        maxDepth: opts.maxDepth,
        nodeTypes: opts.nodeTypes,
        edgeTypes: opts.edgeTypes,
        limit: opts.limit,
      },
    });

    if (!response.success) {
      throw new Error(`Failed to get subgraph: ${response.error}`);
    }

    return response.result!;
  }

  /**
   * Execute SPARQL-like query
   */
  async sparqlQuery(
    query: string,
    bindings?: Record<string, unknown>
  ): Promise<KnowledgeQueryResult> {
    const response = await this.client.callTool<KnowledgeQueryResult>({
      name: 'sparql_query',
      arguments: {
        query,
        bindings,
      },
    });

    if (!response.success) {
      throw new Error(`SPARQL query failed: ${response.error}`);
    }

    return response.result!;
  }

  /**
   * Count nodes by type
   */
  async countNodesByType(type?: string): Promise<number> {
    const response = await this.client.callTool<{ count: number }>({
      name: 'count_nodes',
      arguments: { type },
    });

    if (!response.success) {
      throw new Error(`Count failed: ${response.error}`);
    }

    return response.result!.count;
  }

  /**
   * Check if edge exists between nodes
   */
  async edgeExists(
    sourceId: string,
    targetId: string,
    edgeType?: string
  ): Promise<boolean> {
    const response = await this.client.callTool<{ exists: boolean }>({
      name: 'edge_exists',
      arguments: {
        sourceId,
        targetId,
        edgeType,
      },
    });

    if (!response.success) {
      throw new Error(`Edge check failed: ${response.error}`);
    }

    return response.result!.exists;
  }

  /**
   * Merge options with defaults
   */
  private mergeOptions(options?: Partial<QueryOptions>): Required<QueryOptions> {
    return { ...this.defaultOptions, ...options };
  }
}

/**
 * Create graph query interface
 */
export function createGraphQuery(
  client: YataMCPClient,
  options?: Partial<QueryOptions>
): GraphQueryInterface {
  return new GraphQueryInterface(client, options);
}
