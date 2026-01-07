/**
 * YATA Knowledge Graph integration for DFG/CFG
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-dfg/yata
 */

import type {
  DataFlowGraph,
  ControlFlowGraph,
  DFGNode,
  DFGEdge,
  CFGBlock,
  CFGEdge,
} from '../types/index.js';

// ============================================================================
// YATA Triple Types
// ============================================================================

/**
 * RDF Triple for YATA knowledge graph
 */
export interface Triple {
  subject: string;
  predicate: string;
  object: string;
  graph?: string;
}

/**
 * Namespace prefixes for DFG/CFG triples
 */
export const DFG_NAMESPACES = {
  dfg: 'https://musubix.dev/ontology/dfg#',
  cfg: 'https://musubix.dev/ontology/cfg#',
  code: 'https://musubix.dev/ontology/code#',
  rdf: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
  rdfs: 'http://www.w3.org/2000/01/rdf-schema#',
  xsd: 'http://www.w3.org/2001/XMLSchema#',
} as const;

// ============================================================================
// DFG to YATA Converter
// ============================================================================

/**
 * Options for YATA export
 */
export interface YATAExportOptions {
  /** Include source location information */
  includeLocation: boolean;
  /** Include type information */
  includeTypes: boolean;
  /** Include metadata */
  includeMetadata: boolean;
  /** Graph namespace */
  graphNamespace: string;
}

/**
 * Default export options
 */
export const DEFAULT_EXPORT_OPTIONS: YATAExportOptions = {
  includeLocation: true,
  includeTypes: true,
  includeMetadata: true,
  graphNamespace: 'code:dfg',
};

/**
 * Convert Data Flow Graph to YATA triples
 *
 * @example
 * ```typescript
 * const converter = new DFGToYATAConverter();
 * const triples = converter.convert(dfg);
 *
 * // Import to YATA
 * await yataLocal.importTriples(triples);
 * ```
 *
 * @traces REQ-DFG-003
 */
export class DFGToYATAConverter {
  private options: YATAExportOptions;

  constructor(options: Partial<YATAExportOptions> = {}) {
    this.options = { ...DEFAULT_EXPORT_OPTIONS, ...options };
  }

  /**
   * Convert DFG to triples
   */
  convert(dfg: DataFlowGraph): Triple[] {
    const triples: Triple[] = [];
    const graphUri = `${DFG_NAMESPACES.dfg}graph/${dfg.id}`;

    // Graph metadata
    triples.push({
      subject: graphUri,
      predicate: `${DFG_NAMESPACES.rdf}type`,
      object: `${DFG_NAMESPACES.dfg}DataFlowGraph`,
      graph: this.options.graphNamespace,
    });

    triples.push({
      subject: graphUri,
      predicate: `${DFG_NAMESPACES.dfg}filePath`,
      object: `"${dfg.filePath}"`,
      graph: this.options.graphNamespace,
    });

    triples.push({
      subject: graphUri,
      predicate: `${DFG_NAMESPACES.dfg}nodeCount`,
      object: `"${dfg.metadata.nodeCount}"^^${DFG_NAMESPACES.xsd}integer`,
      graph: this.options.graphNamespace,
    });

    triples.push({
      subject: graphUri,
      predicate: `${DFG_NAMESPACES.dfg}edgeCount`,
      object: `"${dfg.metadata.edgeCount}"^^${DFG_NAMESPACES.xsd}integer`,
      graph: this.options.graphNamespace,
    });

    // Convert nodes
    for (const node of dfg.nodes.values()) {
      triples.push(...this.convertDFGNode(node, graphUri));
    }

    // Convert edges
    for (const edge of dfg.edges.values()) {
      triples.push(...this.convertDFGEdge(edge, graphUri));
    }

    // Entry/exit points
    for (const entryId of dfg.entryPoints) {
      triples.push({
        subject: graphUri,
        predicate: `${DFG_NAMESPACES.dfg}hasEntryPoint`,
        object: `${DFG_NAMESPACES.dfg}node/${entryId}`,
        graph: this.options.graphNamespace,
      });
    }

    for (const exitId of dfg.exitPoints) {
      triples.push({
        subject: graphUri,
        predicate: `${DFG_NAMESPACES.dfg}hasExitPoint`,
        object: `${DFG_NAMESPACES.dfg}node/${exitId}`,
        graph: this.options.graphNamespace,
      });
    }

    return triples;
  }

  private convertDFGNode(node: DFGNode, graphUri: string): Triple[] {
    const triples: Triple[] = [];
    const nodeUri = `${DFG_NAMESPACES.dfg}node/${node.id}`;

    // Node type
    triples.push({
      subject: nodeUri,
      predicate: `${DFG_NAMESPACES.rdf}type`,
      object: `${DFG_NAMESPACES.dfg}${this.capitalize(node.type)}Node`,
      graph: this.options.graphNamespace,
    });

    // Node belongs to graph
    triples.push({
      subject: graphUri,
      predicate: `${DFG_NAMESPACES.dfg}hasNode`,
      object: nodeUri,
      graph: this.options.graphNamespace,
    });

    // Node properties
    triples.push({
      subject: nodeUri,
      predicate: `${DFG_NAMESPACES.dfg}name`,
      object: `"${this.escapeString(node.name)}"`,
      graph: this.options.graphNamespace,
    });

    triples.push({
      subject: nodeUri,
      predicate: `${DFG_NAMESPACES.dfg}scope`,
      object: `"${node.scope}"`,
      graph: this.options.graphNamespace,
    });

    // Location
    if (this.options.includeLocation) {
      triples.push({
        subject: nodeUri,
        predicate: `${DFG_NAMESPACES.code}startLine`,
        object: `"${node.location.startLine}"^^${DFG_NAMESPACES.xsd}integer`,
        graph: this.options.graphNamespace,
      });

      triples.push({
        subject: nodeUri,
        predicate: `${DFG_NAMESPACES.code}endLine`,
        object: `"${node.location.endLine}"^^${DFG_NAMESPACES.xsd}integer`,
        graph: this.options.graphNamespace,
      });
    }

    // Type information
    if (this.options.includeTypes && node.typeInfo) {
      triples.push({
        subject: nodeUri,
        predicate: `${DFG_NAMESPACES.code}hasType`,
        object: `"${this.escapeString(node.typeInfo.fullType)}"`,
        graph: this.options.graphNamespace,
      });

      if (node.typeInfo.nullable) {
        triples.push({
          subject: nodeUri,
          predicate: `${DFG_NAMESPACES.code}isNullable`,
          object: `"true"^^${DFG_NAMESPACES.xsd}boolean`,
          graph: this.options.graphNamespace,
        });
      }
    }

    return triples;
  }

  private convertDFGEdge(edge: DFGEdge, graphUri: string): Triple[] {
    const triples: Triple[] = [];
    const edgeUri = `${DFG_NAMESPACES.dfg}edge/${edge.id}`;
    const sourceUri = `${DFG_NAMESPACES.dfg}node/${edge.source}`;
    const targetUri = `${DFG_NAMESPACES.dfg}node/${edge.target}`;

    // Edge type
    triples.push({
      subject: edgeUri,
      predicate: `${DFG_NAMESPACES.rdf}type`,
      object: `${DFG_NAMESPACES.dfg}${this.edgeTypeToClass(edge.type)}`,
      graph: this.options.graphNamespace,
    });

    // Edge belongs to graph
    triples.push({
      subject: graphUri,
      predicate: `${DFG_NAMESPACES.dfg}hasEdge`,
      object: edgeUri,
      graph: this.options.graphNamespace,
    });

    // Source and target
    triples.push({
      subject: edgeUri,
      predicate: `${DFG_NAMESPACES.dfg}source`,
      object: sourceUri,
      graph: this.options.graphNamespace,
    });

    triples.push({
      subject: edgeUri,
      predicate: `${DFG_NAMESPACES.dfg}target`,
      object: targetUri,
      graph: this.options.graphNamespace,
    });

    // Direct relationship triple
    triples.push({
      subject: sourceUri,
      predicate: `${DFG_NAMESPACES.dfg}${edge.type.replace(/-/g, '')}`,
      object: targetUri,
      graph: this.options.graphNamespace,
    });

    // Label
    if (edge.label) {
      triples.push({
        subject: edgeUri,
        predicate: `${DFG_NAMESPACES.rdfs}label`,
        object: `"${this.escapeString(edge.label)}"`,
        graph: this.options.graphNamespace,
      });
    }

    return triples;
  }

  private capitalize(str: string): string {
    return str
      .split('-')
      .map((part) => part.charAt(0).toUpperCase() + part.slice(1))
      .join('');
  }

  private edgeTypeToClass(type: string): string {
    const mapping: Record<string, string> = {
      'def-use': 'DefinitionUseEdge',
      'use-def': 'UseDefinitionEdge',
      'data-dep': 'DataDependencyEdge',
      'call-arg': 'CallArgumentEdge',
      'call-return': 'CallReturnEdge',
      property: 'PropertyAccessEdge',
      alias: 'AliasEdge',
      phi: 'PhiEdge',
      'control-dep': 'ControlDependencyEdge',
    };
    return mapping[type] || 'Edge';
  }

  private escapeString(str: string): string {
    return str.replace(/"/g, '\\"').replace(/\n/g, '\\n');
  }
}

/**
 * Convert Control Flow Graph to YATA triples
 *
 * @traces REQ-DFG-003
 */
export class CFGToYATAConverter {
  private options: YATAExportOptions;

  constructor(options: Partial<YATAExportOptions> = {}) {
    this.options = { ...DEFAULT_EXPORT_OPTIONS, ...options };
  }

  /**
   * Convert CFG to triples
   */
  convert(cfg: ControlFlowGraph): Triple[] {
    const triples: Triple[] = [];
    const graphUri = `${DFG_NAMESPACES.cfg}graph/${cfg.id}`;

    // Graph metadata
    triples.push({
      subject: graphUri,
      predicate: `${DFG_NAMESPACES.rdf}type`,
      object: `${DFG_NAMESPACES.cfg}ControlFlowGraph`,
      graph: this.options.graphNamespace,
    });

    triples.push({
      subject: graphUri,
      predicate: `${DFG_NAMESPACES.cfg}functionName`,
      object: `"${cfg.functionName}"`,
      graph: this.options.graphNamespace,
    });

    triples.push({
      subject: graphUri,
      predicate: `${DFG_NAMESPACES.cfg}filePath`,
      object: `"${cfg.filePath}"`,
      graph: this.options.graphNamespace,
    });

    triples.push({
      subject: graphUri,
      predicate: `${DFG_NAMESPACES.cfg}cyclomaticComplexity`,
      object: `"${cfg.metadata.cyclomaticComplexity}"^^${DFG_NAMESPACES.xsd}integer`,
      graph: this.options.graphNamespace,
    });

    triples.push({
      subject: graphUri,
      predicate: `${DFG_NAMESPACES.cfg}maxLoopDepth`,
      object: `"${cfg.metadata.maxLoopDepth}"^^${DFG_NAMESPACES.xsd}integer`,
      graph: this.options.graphNamespace,
    });

    // Convert blocks
    for (const block of cfg.blocks.values()) {
      triples.push(...this.convertCFGBlock(block, graphUri));
    }

    // Convert edges
    for (const edge of cfg.edges.values()) {
      triples.push(...this.convertCFGEdge(edge, graphUri));
    }

    // Entry block
    triples.push({
      subject: graphUri,
      predicate: `${DFG_NAMESPACES.cfg}hasEntryBlock`,
      object: `${DFG_NAMESPACES.cfg}block/${cfg.entryBlock}`,
      graph: this.options.graphNamespace,
    });

    // Exit blocks
    for (const exitId of cfg.exitBlocks) {
      triples.push({
        subject: graphUri,
        predicate: `${DFG_NAMESPACES.cfg}hasExitBlock`,
        object: `${DFG_NAMESPACES.cfg}block/${exitId}`,
        graph: this.options.graphNamespace,
      });
    }

    return triples;
  }

  private convertCFGBlock(block: CFGBlock, graphUri: string): Triple[] {
    const triples: Triple[] = [];
    const blockUri = `${DFG_NAMESPACES.cfg}block/${block.id}`;

    // Block type
    triples.push({
      subject: blockUri,
      predicate: `${DFG_NAMESPACES.rdf}type`,
      object: `${DFG_NAMESPACES.cfg}${this.capitalize(block.type)}Block`,
      graph: this.options.graphNamespace,
    });

    // Block belongs to graph
    triples.push({
      subject: graphUri,
      predicate: `${DFG_NAMESPACES.cfg}hasBlock`,
      object: blockUri,
      graph: this.options.graphNamespace,
    });

    // Block properties
    triples.push({
      subject: blockUri,
      predicate: `${DFG_NAMESPACES.rdfs}label`,
      object: `"${this.escapeString(block.label)}"`,
      graph: this.options.graphNamespace,
    });

    triples.push({
      subject: blockUri,
      predicate: `${DFG_NAMESPACES.cfg}loopDepth`,
      object: `"${block.loopDepth}"^^${DFG_NAMESPACES.xsd}integer`,
      graph: this.options.graphNamespace,
    });

    // Statements
    for (let i = 0; i < block.statements.length; i++) {
      const stmt = block.statements[i];
      const stmtUri = `${blockUri}/stmt/${i}`;

      triples.push({
        subject: blockUri,
        predicate: `${DFG_NAMESPACES.cfg}hasStatement`,
        object: stmtUri,
        graph: this.options.graphNamespace,
      });

      triples.push({
        subject: stmtUri,
        predicate: `${DFG_NAMESPACES.cfg}statementText`,
        object: `"${this.escapeString(stmt.text)}"`,
        graph: this.options.graphNamespace,
      });

      triples.push({
        subject: stmtUri,
        predicate: `${DFG_NAMESPACES.cfg}statementIndex`,
        object: `"${i}"^^${DFG_NAMESPACES.xsd}integer`,
        graph: this.options.graphNamespace,
      });
    }

    // Location
    if (this.options.includeLocation) {
      triples.push({
        subject: blockUri,
        predicate: `${DFG_NAMESPACES.code}startLine`,
        object: `"${block.location.startLine}"^^${DFG_NAMESPACES.xsd}integer`,
        graph: this.options.graphNamespace,
      });
    }

    return triples;
  }

  private convertCFGEdge(edge: CFGEdge, graphUri: string): Triple[] {
    const triples: Triple[] = [];
    const edgeUri = `${DFG_NAMESPACES.cfg}edge/${edge.id}`;
    const sourceUri = `${DFG_NAMESPACES.cfg}block/${edge.source}`;
    const targetUri = `${DFG_NAMESPACES.cfg}block/${edge.target}`;

    // Edge type
    triples.push({
      subject: edgeUri,
      predicate: `${DFG_NAMESPACES.rdf}type`,
      object: `${DFG_NAMESPACES.cfg}${this.edgeTypeToClass(edge.type)}`,
      graph: this.options.graphNamespace,
    });

    // Edge belongs to graph
    triples.push({
      subject: graphUri,
      predicate: `${DFG_NAMESPACES.cfg}hasEdge`,
      object: edgeUri,
      graph: this.options.graphNamespace,
    });

    // Source and target
    triples.push({
      subject: edgeUri,
      predicate: `${DFG_NAMESPACES.cfg}source`,
      object: sourceUri,
      graph: this.options.graphNamespace,
    });

    triples.push({
      subject: edgeUri,
      predicate: `${DFG_NAMESPACES.cfg}target`,
      object: targetUri,
      graph: this.options.graphNamespace,
    });

    // Direct successor relationship
    triples.push({
      subject: sourceUri,
      predicate: `${DFG_NAMESPACES.cfg}successor`,
      object: targetUri,
      graph: this.options.graphNamespace,
    });

    // Condition
    if (edge.condition) {
      triples.push({
        subject: edgeUri,
        predicate: `${DFG_NAMESPACES.cfg}condition`,
        object: `"${this.escapeString(edge.condition)}"`,
        graph: this.options.graphNamespace,
      });
    }

    // Back edge marker
    if (edge.isBackEdge) {
      triples.push({
        subject: edgeUri,
        predicate: `${DFG_NAMESPACES.cfg}isBackEdge`,
        object: `"true"^^${DFG_NAMESPACES.xsd}boolean`,
        graph: this.options.graphNamespace,
      });
    }

    return triples;
  }

  private capitalize(str: string): string {
    return str
      .split('-')
      .map((part) => part.charAt(0).toUpperCase() + part.slice(1))
      .join('');
  }

  private edgeTypeToClass(type: string): string {
    const mapping: Record<string, string> = {
      sequential: 'SequentialEdge',
      'conditional-true': 'ConditionalTrueEdge',
      'conditional-false': 'ConditionalFalseEdge',
      'loop-back': 'LoopBackEdge',
      'loop-exit': 'LoopExitEdge',
      'switch-case': 'SwitchCaseEdge',
      'switch-default': 'SwitchDefaultEdge',
      exception: 'ExceptionEdge',
      return: 'ReturnEdge',
      break: 'BreakEdge',
      continue: 'ContinueEdge',
    };
    return mapping[type] || 'Edge';
  }

  private escapeString(str: string): string {
    return str.replace(/"/g, '\\"').replace(/\n/g, '\\n');
  }
}

/**
 * YATA integration helper for DFG/CFG
 *
 * @example
 * ```typescript
 * import { YATALocal } from '@nahisaho/yata-local';
 *
 * const yata = new YATALocal('myproject.db');
 * const integrator = new YATAIntegrator(yata);
 *
 * // Import DFG
 * await integrator.importDFG(dfg);
 *
 * // Query related code
 * const results = await integrator.queryRelatedCode('userId');
 * ```
 */
export class YATAIntegrator {
  private dfgConverter: DFGToYATAConverter;
  private cfgConverter: CFGToYATAConverter;

  constructor(
    private readonly yataClient?: unknown, // YATALocal type when available
    options: Partial<YATAExportOptions> = {}
  ) {
    this.dfgConverter = new DFGToYATAConverter(options);
    this.cfgConverter = new CFGToYATAConverter({
      ...options,
      graphNamespace: options.graphNamespace || 'code:cfg',
    });
  }

  /**
   * Import DFG to YATA knowledge graph
   */
  async importDFG(dfg: DataFlowGraph): Promise<void> {
    const triples = this.dfgConverter.convert(dfg);
    await this.importTriples(triples);
  }

  /**
   * Import CFG to YATA knowledge graph
   */
  async importCFG(cfg: ControlFlowGraph): Promise<void> {
    const triples = this.cfgConverter.convert(cfg);
    await this.importTriples(triples);
  }

  /**
   * Import multiple graphs
   */
  async importAll(
    dfgs: DataFlowGraph[],
    cfgs: ControlFlowGraph[]
  ): Promise<void> {
    const allTriples: Triple[] = [];

    for (const dfg of dfgs) {
      allTriples.push(...this.dfgConverter.convert(dfg));
    }

    for (const cfg of cfgs) {
      allTriples.push(...this.cfgConverter.convert(cfg));
    }

    await this.importTriples(allTriples);
  }

  /**
   * Export triples without importing
   */
  exportToTriples(dfg: DataFlowGraph): Triple[] {
    return this.dfgConverter.convert(dfg);
  }

  /**
   * Export to N-Triples format
   */
  exportToNTriples(dfg: DataFlowGraph): string {
    const triples = this.dfgConverter.convert(dfg);
    return triples
      .map((t) => {
        const subject = t.subject.startsWith('"')
          ? t.subject
          : `<${t.subject}>`;
        const predicate = `<${t.predicate}>`;
        const object = t.object.startsWith('"')
          ? t.object
          : t.object.startsWith('_:')
          ? t.object
          : `<${t.object}>`;
        return `${subject} ${predicate} ${object} .`;
      })
      .join('\n');
  }

  private async importTriples(triples: Triple[]): Promise<void> {
    if (this.yataClient && typeof (this.yataClient as any).addTriples === 'function') {
      await (this.yataClient as any).addTriples(triples);
    } else {
      // Log triples when no client available
      console.log(`[YATAIntegrator] ${triples.length} triples generated (no client connected)`);
    }
  }
}
