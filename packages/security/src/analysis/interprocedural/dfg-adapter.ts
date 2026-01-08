/**
 * @fileoverview DFG Adapter - Integrate musubix-dfg with taint analysis
 * @module @nahisaho/musubix-security/analysis/interprocedural/dfg-adapter
 * @trace REQ-SEC-001 (EARS: THE system SHALL integrate with DFG for enhanced taint tracking)
 */

import type {
  DataFlowGraph,
  DFGNode,
  DFGEdge,
} from '@nahisaho/musubix-dfg';
import type { TaintLocation, TaintFlowEdge, TaintFlowType } from './taint-propagator.js';
import type { TaintSinkCategory } from '../../types/taint.js';
import type { SourceDefinition } from '../sources/types.js';
import type { SinkDefinition } from '../sinks/types.js';

/**
 * Options for DFG-based taint analysis
 */
export interface DFGTaintOptions {
  /** Include aliasing analysis */
  trackAliasing?: boolean;
  /** Include control flow dependencies */
  trackControlDependencies?: boolean;
  /** Maximum propagation depth */
  maxDepth?: number;
  /** Minimum confidence threshold */
  minConfidence?: number;
}

/**
 * DFG node with taint information
 */
export interface TaintedDFGNode extends DFGNode {
  /** Whether node is tainted */
  isTainted: boolean;
  /** Taint confidence */
  taintConfidence: number;
  /** Source of taint */
  taintSource?: TaintLocation;
  /** Sanitizers applied */
  sanitizers: string[];
  /** Remaining vulnerable categories */
  vulnerableCategories: TaintSinkCategory[];
}

/**
 * Result of DFG taint analysis
 */
export interface DFGTaintResult {
  /** Original DFG */
  dfg: DataFlowGraph;
  /** Tainted nodes */
  taintedNodes: Map<string, TaintedDFGNode>;
  /** Taint flow edges */
  taintFlowEdges: TaintFlowEdge[];
  /** Detected sources */
  sources: TaintLocation[];
  /** Detected sinks */
  sinks: TaintLocation[];
  /** Source to sink paths */
  vulnerablePaths: TaintPath[];
}

/**
 * Path from taint source to sink
 */
export interface TaintPath {
  /** Source location */
  source: TaintLocation;
  /** Sink location */
  sink: TaintLocation;
  /** Intermediate nodes */
  path: string[];
  /** Flow edges */
  edges: TaintFlowEdge[];
  /** Sanitizers in path */
  sanitizers: string[];
  /** Whether path is fully sanitized */
  isSanitized: boolean;
  /** Confidence */
  confidence: number;
}

/**
 * DFG Adapter for taint analysis
 * Converts DFG data flow information to taint tracking
 * @trace REQ-SEC-001
 */
export class DFGTaintAdapter {
  private sources: SourceDefinition[];
  private sinks: SinkDefinition[];
  private options: Required<DFGTaintOptions>;

  constructor(
    sources: SourceDefinition[],
    sinks: SinkDefinition[],
    options: DFGTaintOptions = {}
  ) {
    this.sources = sources;
    this.sinks = sinks;
    this.options = {
      trackAliasing: options.trackAliasing ?? true,
      trackControlDependencies: options.trackControlDependencies ?? false,
      maxDepth: options.maxDepth ?? 20,
      minConfidence: options.minConfidence ?? 0.5,
    };
  }

  /**
   * Analyze DFG for taint flows
   */
  analyzeTaint(dfg: DataFlowGraph): DFGTaintResult {
    const taintedNodes = new Map<string, TaintedDFGNode>();
    const taintFlowEdges: TaintFlowEdge[] = [];
    const sources: TaintLocation[] = [];
    const sinks: TaintLocation[] = [];
    const vulnerablePaths: TaintPath[] = [];

    // Step 1: Identify taint sources in DFG
    for (const [nodeId, node] of dfg.nodes) {
      if (this.isSource(node)) {
        const location = this.dfgLocationToTaintLocation(node);
        sources.push(location);
        
        // Mark node as tainted
        taintedNodes.set(nodeId, {
          ...node,
          isTainted: true,
          taintConfidence: 1.0,
          taintSource: location,
          sanitizers: [],
          vulnerableCategories: this.getAllSinkCategories(),
        });
      }
    }

    // Step 2: Propagate taint through DFG edges
    this.propagateTaint(dfg, taintedNodes, taintFlowEdges);

    // Step 3: Identify sinks that receive tainted data
    for (const [nodeId, node] of dfg.nodes) {
      if (this.isSink(node)) {
        const location = this.dfgLocationToTaintLocation(node);
        sinks.push(location);
        
        // Check if sink receives tainted data
        const incomingEdges = this.getEdgesWithTarget(dfg, nodeId);
        for (const edge of incomingEdges) {
          const sourceNode = taintedNodes.get(edge.source);
          if (sourceNode?.isTainted) {
            // Found vulnerable path
            const path = this.buildTaintPath(
              dfg,
              taintedNodes,
              sourceNode.taintSource!,
              location
            );
            if (path && path.confidence >= this.options.minConfidence) {
              vulnerablePaths.push(path);
            }
          }
        }
      }
    }

    return {
      dfg,
      taintedNodes,
      taintFlowEdges,
      sources,
      sinks,
      vulnerablePaths,
    };
  }

  /**
   * Propagate taint through DFG
   */
  private propagateTaint(
    dfg: DataFlowGraph,
    taintedNodes: Map<string, TaintedDFGNode>,
    taintFlowEdges: TaintFlowEdge[]
  ): void {
    const worklist: string[] = Array.from(taintedNodes.keys());
    const visited = new Set<string>();
    const maxIterations = this.options.maxDepth * dfg.nodes.size;
    let iteration = 0;

    while (worklist.length > 0 && iteration < maxIterations) {
      const nodeId = worklist.shift()!;
      if (visited.has(nodeId)) continue;
      visited.add(nodeId);
      iteration++;

      const taintedNode = taintedNodes.get(nodeId);
      if (!taintedNode) continue;

      // Find outgoing edges
      const outgoing = this.getEdgesWithSource(dfg, nodeId);

      for (const edge of outgoing) {
        // Check if this edge type propagates taint
        if (!this.propagatesTaint(edge)) continue;

        const targetNode = dfg.nodes.get(edge.target);
        if (!targetNode) continue;

        // Check for sanitizer
        const sanitizer = this.checkSanitizer(targetNode);
        const newSanitizers = sanitizer
          ? [...taintedNode.sanitizers, sanitizer]
          : [...taintedNode.sanitizers];

        // Update vulnerable categories after sanitization
        const newVulnerableCategories = this.updateVulnerableCategories(
          taintedNode.vulnerableCategories,
          sanitizer
        );

        // Calculate new confidence
        const newConfidence = this.calculateConfidence(
          taintedNode.taintConfidence,
          edge.type as string
        );

        // Create or update target node
        const existingTarget = taintedNodes.get(edge.target);
        if (!existingTarget || existingTarget.taintConfidence < newConfidence) {
          taintedNodes.set(edge.target, {
            ...targetNode,
            isTainted: true,
            taintConfidence: newConfidence,
            taintSource: taintedNode.taintSource,
            sanitizers: newSanitizers,
            vulnerableCategories: newVulnerableCategories,
          });

          // Add to worklist for further propagation
          if (!visited.has(edge.target)) {
            worklist.push(edge.target);
          }
        }

        // Record flow edge
        const flowEdge = this.createFlowEdge(
          taintedNode,
          targetNode,
          edge,
          newConfidence,
          newSanitizers
        );
        taintFlowEdges.push(flowEdge);
      }

      // Handle aliasing
      if (this.options.trackAliasing) {
        const aliasEdges = this.getEdgesWithSourceAndType(dfg, nodeId, 'alias');
        for (const aliasEdge of aliasEdges) {
          const aliasTarget = dfg.nodes.get(aliasEdge.target);
          if (aliasTarget && !taintedNodes.has(aliasEdge.target)) {
            taintedNodes.set(aliasEdge.target, {
              ...aliasTarget,
              isTainted: true,
              taintConfidence: taintedNode.taintConfidence * 0.95,
              taintSource: taintedNode.taintSource,
              sanitizers: [...taintedNode.sanitizers],
              vulnerableCategories: [...taintedNode.vulnerableCategories],
            });
            worklist.push(aliasEdge.target);
          }
        }
      }
    }
  }

  /**
   * Check if DFG node is a taint source
   */
  private isSource(node: DFGNode): boolean {
    for (const source of this.sources) {
      for (const pattern of source.patterns) {
        // Check method match
        if (pattern.method) {
          const methods = Array.isArray(pattern.method) ? pattern.method : [pattern.method];
          if (methods.some((m) => node.name?.includes(m))) {
            return true;
          }
        }
        // Check property match
        if (pattern.property) {
          const props = Array.isArray(pattern.property) ? pattern.property : [pattern.property];
          if (props.some((p) => node.name?.includes(p))) {
            return true;
          }
        }
      }
    }
    return false;
  }

  /**
   * Check if DFG node is a taint sink
   */
  private isSink(node: DFGNode): boolean {
    for (const sink of this.sinks) {
      for (const pattern of sink.patterns) {
        // Check method match
        if (pattern.method) {
          const methods = Array.isArray(pattern.method) ? pattern.method : [pattern.method];
          if (methods.some((m) => node.name?.includes(m))) {
            return true;
          }
        }
        // Check property match
        if (pattern.property) {
          const props = Array.isArray(pattern.property) ? pattern.property : [pattern.property];
          if (props.some((p) => node.name?.includes(p))) {
            return true;
          }
        }
      }
    }
    return false;
  }

  /**
   * Check if DFG node is a sanitizer
   */
  private checkSanitizer(node: DFGNode): string | null {
    const sanitizerPatterns = [
      'escape',
      'sanitize',
      'encode',
      'parameterize',
      'validate',
      'filter',
      'parseInt',
      'parseFloat',
    ];

    for (const pattern of sanitizerPatterns) {
      if (node.name?.toLowerCase().includes(pattern)) {
        return node.name;
      }
    }
    return null;
  }

  /**
   * Check if edge type propagates taint
   */
  private propagatesTaint(edge: DFGEdge): boolean {
    const propagatingTypes = [
      'def-use',
      'data-dep',
      'call-arg',
      'call-return',
      'property',
      'alias',
    ];

    if (this.options.trackControlDependencies) {
      propagatingTypes.push('control-dep');
    }

    return propagatingTypes.includes(edge.type as string);
  }

  /**
   * Get all sink categories
   */
  private getAllSinkCategories(): TaintSinkCategory[] {
    return [
      'sql-query',
      'nosql-query',
      'command-exec',
      'file-write',
      'file-read',
      'html-output',
      'redirect',
      'eval',
      'deserialization',
      'ldap-query',
      'xpath-query',
      'http-request',
    ];
  }

  /**
   * Update vulnerable categories after sanitization
   */
  private updateVulnerableCategories(
    current: TaintSinkCategory[],
    sanitizer: string | null
  ): TaintSinkCategory[] {
    if (!sanitizer) return current;

    const sanitizerMappings: Record<string, TaintSinkCategory[]> = {
      escape: ['sql-query', 'html-output'],
      escapeHtml: ['html-output'],
      encodeURIComponent: ['redirect', 'http-request'],
      parameterize: ['sql-query'],
      parseInt: ['sql-query', 'command-exec'],
      sanitize: ['html-output', 'sql-query'],
    };

    const protectedCategories: TaintSinkCategory[] = [];
    for (const [pattern, categories] of Object.entries(sanitizerMappings)) {
      if (sanitizer.toLowerCase().includes(pattern.toLowerCase())) {
        protectedCategories.push(...categories);
      }
    }

    return current.filter((c) => !protectedCategories.includes(c));
  }

  /**
   * Calculate taint confidence after propagation
   */
  private calculateConfidence(baseConfidence: number, edgeType: string): number {
    const confidenceFactors: Record<string, number> = {
      'def-use': 1.0,
      'data-dep': 0.95,
      'call-arg': 0.9,
      'call-return': 0.85,
      'property': 0.9,
      'alias': 0.95,
      'control-dep': 0.6,
      'phi': 0.8,
    };

    const factor = confidenceFactors[edgeType] ?? 0.7;
    return baseConfidence * factor;
  }

  /**
   * Convert DFG location to taint location
   */
  private dfgLocationToTaintLocation(node: DFGNode): TaintLocation {
    return {
      nodeId: node.id,
      identifier: node.name ?? node.id,
      line: node.location?.startLine ?? 0,
      column: node.location?.startColumn ?? 0,
      filePath: node.location?.filePath ?? 'unknown',
    };
  }

  /**
   * Create taint flow edge from DFG edge
   */
  private createFlowEdge(
    sourceNode: TaintedDFGNode,
    targetNode: DFGNode,
    edge: DFGEdge,
    confidence: number,
    sanitizers: string[]
  ): TaintFlowEdge {
    const flowTypeMapping: Record<string, TaintFlowType> = {
      'def-use': 'assignment',
      'data-dep': 'assignment',
      'call-arg': 'parameter',
      'call-return': 'return',
      'property': 'property-access',
      'alias': 'assignment',
      'control-dep': 'implicit',
    };

    return {
      id: `flow_${edge.id}`,
      from: this.dfgLocationToTaintLocation(sourceNode),
      to: this.dfgLocationToTaintLocation(targetNode),
      flowType: flowTypeMapping[edge.type as string] ?? 'assignment',
      sanitizersApplied: sanitizers,
      confidence,
    };
  }

  /**
   * Build complete taint path from source to sink
   */
  private buildTaintPath(
    dfg: DataFlowGraph,
    taintedNodes: Map<string, TaintedDFGNode>,
    source: TaintLocation,
    sink: TaintLocation
  ): TaintPath | null {
    // BFS to find shortest path
    const visited = new Set<string>();
    const queue: Array<{ nodeId: string; path: string[]; edges: TaintFlowEdge[] }> = [];
    
    // Find source node
    const sourceNodeId = Array.from(taintedNodes.entries())
      .find(([, node]) => node.taintSource?.nodeId === source.nodeId)?.[0];
    
    if (!sourceNodeId) return null;
    
    queue.push({ nodeId: sourceNodeId, path: [sourceNodeId], edges: [] });
    visited.add(sourceNodeId);

    while (queue.length > 0) {
      const { nodeId, path, edges } = queue.shift()!;
      
      // Check if we reached sink
      if (nodeId === sink.nodeId) {
        const taintedNode = taintedNodes.get(nodeId);
        return {
          source,
          sink,
          path,
          edges,
          sanitizers: taintedNode?.sanitizers ?? [],
          isSanitized: (taintedNode?.vulnerableCategories.length ?? 0) === 0,
          confidence: taintedNode?.taintConfidence ?? 0,
        };
      }

      // Explore neighbors
      const outgoing = this.getEdgesWithSource(dfg, nodeId);
      for (const edge of outgoing) {
        if (!visited.has(edge.target) && taintedNodes.has(edge.target)) {
          visited.add(edge.target);
          const targetNode = dfg.nodes.get(edge.target);
          if (targetNode) {
            const sourceNode = taintedNodes.get(nodeId)!;
            const flowEdge = this.createFlowEdge(
              sourceNode,
              targetNode,
              edge,
              sourceNode.taintConfidence,
              sourceNode.sanitizers
            );
            queue.push({
              nodeId: edge.target,
              path: [...path, edge.target],
              edges: [...edges, flowEdge],
            });
          }
        }
      }
    }

    return null;
  }

  /**
   * Get sink category for a node
   */
  getSinkCategory(node: DFGNode): TaintSinkCategory | null {
    for (const sink of this.sinks) {
      for (const pattern of sink.patterns) {
        if (pattern.method) {
          const methods = Array.isArray(pattern.method) ? pattern.method : [pattern.method];
          if (methods.some((m) => node.name?.includes(m))) {
            return sink.category;
          }
        }
      }
    }
    return null;
  }

  /**
   * Get statistics about taint analysis
   */
  getStatistics(result: DFGTaintResult): DFGTaintStatistics {
    return {
      totalNodes: result.dfg.nodes.size,
      taintedNodes: result.taintedNodes.size,
      sources: result.sources.length,
      sinks: result.sinks.length,
      vulnerablePaths: result.vulnerablePaths.length,
      sanitizedPaths: result.vulnerablePaths.filter((p) => p.isSanitized).length,
      avgConfidence:
        result.vulnerablePaths.length > 0
          ? result.vulnerablePaths.reduce((sum, p) => sum + p.confidence, 0) /
            result.vulnerablePaths.length
          : 0,
    };
  }

  // ========================================================================
  // Helper methods for Map-based DFG traversal
  // ========================================================================

  /**
   * Get all edges with a specific source node
   */
  private getEdgesWithSource(dfg: DataFlowGraph, sourceId: string): DFGEdge[] {
    const result: DFGEdge[] = [];
    for (const edge of dfg.edges.values()) {
      if (edge.source === sourceId) {
        result.push(edge);
      }
    }
    return result;
  }

  /**
   * Get all edges with a specific target node
   */
  private getEdgesWithTarget(dfg: DataFlowGraph, targetId: string): DFGEdge[] {
    const result: DFGEdge[] = [];
    for (const edge of dfg.edges.values()) {
      if (edge.target === targetId) {
        result.push(edge);
      }
    }
    return result;
  }

  /**
   * Get all edges with a specific source and type
   */
  private getEdgesWithSourceAndType(dfg: DataFlowGraph, sourceId: string, edgeType: string): DFGEdge[] {
    const result: DFGEdge[] = [];
    for (const edge of dfg.edges.values()) {
      if (edge.source === sourceId && edge.type === edgeType) {
        result.push(edge);
      }
    }
    return result;
  }
}

/**
 * Statistics from DFG taint analysis
 */
export interface DFGTaintStatistics {
  totalNodes: number;
  taintedNodes: number;
  sources: number;
  sinks: number;
  vulnerablePaths: number;
  sanitizedPaths: number;
  avgConfidence: number;
}
