/**
 * @fileoverview Pattern-Ontology Integration MCP Tools
 * @traceability TSK-INT-002
 */

import type { Tool, CallToolResult, TextContent } from '@modelcontextprotocol/sdk/types.js';
import {
  N3Store,
  PatternOntologyBridge,
  type PatternRelation,
} from '@nahisaho/musubix-ontology-mcp';
import {
  WakeSleepCycle,
  type ASTNode,
} from '@nahisaho/musubix-pattern-mcp';

// Singleton instances
let storeInstance: N3Store | null = null;
let bridgeInstance: PatternOntologyBridge | null = null;
let wakeSleepInstance: WakeSleepCycle | null = null;

/**
 * Get or create N3Store instance
 */
function getStore(): N3Store {
  if (!storeInstance) {
    storeInstance = new N3Store({
      enableInference: true,
      maxTriples: 100000,
    });
  }
  return storeInstance;
}

/**
 * Get or create Bridge instance
 */
function getBridge(): PatternOntologyBridge {
  if (!bridgeInstance) {
    bridgeInstance = new PatternOntologyBridge(getStore(), {
      enableInference: true,
      minConfidence: 0.5,
    });
  }
  return bridgeInstance;
}

/**
 * Get or create WakeSleep instance
 */
function getWakeSleep(): WakeSleepCycle {
  if (!wakeSleepInstance) {
    wakeSleepInstance = new WakeSleepCycle({
      autoSleep: false,
      minQualityThreshold: 0.3,
      maxLibrarySize: 1000,
    });
  }
  return wakeSleepInstance;
}

/**
 * Tool: Learn from code observation
 */
export const learnPatternTool: Tool = {
  name: 'pattern_learn',
  description: 'Learn patterns from observed code. Part of the Wake phase of Wake-Sleep learning.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      code: {
        type: 'string',
        description: 'The source code to learn from',
      },
      language: {
        type: 'string',
        description: 'Programming language (e.g., typescript, python)',
        default: 'typescript',
      },
      filename: {
        type: 'string',
        description: 'Optional filename for context',
      },
      domain: {
        type: 'string',
        description: 'Optional domain context (e.g., web, api, database)',
      },
    },
    required: ['code'],
  },
};

/**
 * Tool: Consolidate learned patterns
 */
export const consolidatePatternsTool: Tool = {
  name: 'pattern_consolidate',
  description: 'Consolidate and optimize the pattern library. Part of the Sleep phase of Wake-Sleep learning.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      qualityThreshold: {
        type: 'number',
        description: 'Minimum quality score to keep patterns (0-1)',
        default: 0.3,
      },
    },
    required: [],
  },
};

/**
 * Tool: Query pattern relationships
 */
export const queryPatternRelationsTool: Tool = {
  name: 'pattern_query_relations',
  description: 'Query relationships between patterns in the knowledge graph.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      patternId: {
        type: 'string',
        description: 'Pattern ID to find relationships for',
      },
      relation: {
        type: 'string',
        enum: ['subsumes', 'specializes', 'similarTo', 'composedOf', 'usedWith', 'derivedFrom'],
        description: 'Optional: filter by relationship type',
      },
    },
    required: ['patternId'],
  },
};

/**
 * Tool: Search patterns
 */
export const searchPatternsTool: Tool = {
  name: 'pattern_search',
  description: 'Search for patterns by various criteria.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      language: {
        type: 'string',
        description: 'Filter by programming language',
      },
      astType: {
        type: 'string',
        description: 'Filter by AST node type (e.g., FunctionDeclaration)',
      },
      minFrequency: {
        type: 'number',
        description: 'Minimum usage frequency',
      },
    },
    required: [],
  },
};

/**
 * Tool: Get learning statistics
 */
export const getLearningStatsTool: Tool = {
  name: 'pattern_stats',
  description: 'Get statistics about the pattern learning system.',
  inputSchema: {
    type: 'object' as const,
    properties: {},
    required: [],
  },
};

/**
 * Tool: Import patterns to knowledge graph
 */
export const importToKnowledgeGraphTool: Tool = {
  name: 'pattern_import_kg',
  description: 'Import learned patterns into the ontology knowledge graph for semantic reasoning.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      discoverRelationships: {
        type: 'boolean',
        description: 'Whether to discover relationships between patterns',
        default: true,
      },
    },
    required: [],
  },
};

/**
 * Tool: Export knowledge graph
 */
export const exportKnowledgeGraphTool: Tool = {
  name: 'pattern_export_kg',
  description: 'Export the pattern knowledge graph as Turtle RDF.',
  inputSchema: {
    type: 'object' as const,
    properties: {},
    required: [],
  },
};

/**
 * Handle pattern_learn tool call
 */
async function handleLearnPattern(args: Record<string, unknown>): Promise<CallToolResult> {
  const code = args.code as string;
  const language = (args.language as string) || 'typescript';
  const filename = args.filename as string | undefined;
  const domain = args.domain as string | undefined;

  // Create a simple AST representation (in real implementation, use actual parser)
  const ast = createSimpleAST(code, language);

  const wakeSleep = getWakeSleep();
  const patterns = wakeSleep.wake({
    ast,
    source: code,
    context: { language, filename, domain },
    timestamp: new Date().toISOString(),
  });

  const stats = wakeSleep.getStats();

  return {
    content: [{
      type: 'text',
      text: JSON.stringify({
        success: true,
        patternsExtracted: patterns.length,
        totalObservations: stats.totalWakeObservations,
        librarySize: stats.currentLibrarySize,
        patterns: patterns.slice(0, 5).map(p => ({
          id: p.id,
          name: p.name,
          astType: p.ast.type,
        })),
      }, null, 2),
    } as TextContent],
  };
}

/**
 * Handle pattern_consolidate tool call
 */
async function handleConsolidatePatterns(_args: Record<string, unknown>): Promise<CallToolResult> {
  const wakeSleep = getWakeSleep();
  const result = wakeSleep.sleep();

  return {
    content: [{
      type: 'text',
      text: JSON.stringify({
        success: true,
        patternsConsolidated: result.patternsConsolidated,
        patternsRemoved: result.patternsRemoved,
        compressionRatio: result.compressionRatio.toFixed(3),
        mdlImprovement: (result.mdlImprovement * 100).toFixed(1) + '%',
        cycleTimeMs: result.cycleTimeMs,
      }, null, 2),
    } as TextContent],
  };
}

/**
 * Handle pattern_query_relations tool call
 */
async function handleQueryRelations(args: Record<string, unknown>): Promise<CallToolResult> {
  const patternId = args.patternId as string;
  const relation = args.relation as PatternRelation | undefined;

  const bridge = getBridge();
  const relationships = bridge.findRelatedPatterns(patternId, relation);

  return {
    content: [{
      type: 'text',
      text: JSON.stringify({
        success: true,
        patternId,
        relationshipCount: relationships.length,
        relationships: relationships.map(r => ({
          source: r.source,
          target: r.target,
          relation: r.relation,
          confidence: r.confidence.toFixed(3),
        })),
      }, null, 2),
    } as TextContent],
  };
}

/**
 * Handle pattern_search tool call
 */
async function handleSearchPatterns(args: Record<string, unknown>): Promise<CallToolResult> {
  const bridge = getBridge();
  const result = bridge.queryPatterns({
    language: args.language as string | undefined,
    astType: args.astType as string | undefined,
    minFrequency: args.minFrequency as number | undefined,
  });

  return {
    content: [{
      type: 'text',
      text: JSON.stringify({
        success: true,
        patternCount: result.patterns.length,
        patterns: result.patterns.slice(0, 20).map(p => ({
          id: p.id,
          name: p.name,
          language: p.language,
          astType: p.ast.type,
          frequency: p.frequency,
          holes: p.holes.length,
        })),
      }, null, 2),
    } as TextContent],
  };
}

/**
 * Handle pattern_stats tool call
 */
async function handleGetStats(): Promise<CallToolResult> {
  const wakeSleep = getWakeSleep();
  const bridge = getBridge();

  const wsStats = wakeSleep.getStats();
  const bridgeStats = bridge.getStats();

  return {
    content: [{
      type: 'text',
      text: JSON.stringify({
        wakeSleep: {
          totalObservations: wsStats.totalWakeObservations,
          totalSleepCycles: wsStats.totalSleepCycles,
          librarySize: wsStats.currentLibrarySize,
          averageQuality: wsStats.averagePatternQuality.toFixed(3),
          patternsExtracted: wsStats.totalPatternsExtracted,
          patternsRemoved: wsStats.totalPatternsRemoved,
        },
        knowledgeGraph: {
          patternCount: bridgeStats.patternCount,
          tripleCount: bridgeStats.tripleCount,
          relationshipCount: bridgeStats.relationshipCount,
        },
      }, null, 2),
    } as TextContent],
  };
}

/**
 * Handle pattern_import_kg tool call
 */
async function handleImportToKG(args: Record<string, unknown>): Promise<CallToolResult> {
  const discoverRelationships = args.discoverRelationships !== false;

  const wakeSleep = getWakeSleep();
  const bridge = getBridge();

  const patterns = wakeSleep.getLibrary();
  const imported = bridge.importPatterns(patterns);

  let relationships: unknown[] = [];
  if (discoverRelationships && patterns.length > 1) {
    relationships = bridge.discoverRelationships(patterns);
  }

  const stats = bridge.getStats();

  return {
    content: [{
      type: 'text',
      text: JSON.stringify({
        success: true,
        patternsImported: imported,
        relationshipsDiscovered: relationships.length,
        knowledgeGraph: {
          patternCount: stats.patternCount,
          tripleCount: stats.tripleCount,
          relationshipCount: stats.relationshipCount,
        },
      }, null, 2),
    } as TextContent],
  };
}

/**
 * Handle pattern_export_kg tool call
 */
async function handleExportKG(): Promise<CallToolResult> {
  const bridge = getBridge();
  const turtle = await bridge.exportAsTurtle();

  return {
    content: [{
      type: 'text',
      text: turtle,
    } as TextContent],
  };
}

/**
 * Create simple AST from code (placeholder - real implementation would use parser)
 */
function createSimpleAST(code: string, _language: string): ASTNode {
  const defaultPos = { row: 0, column: 0 };

  // Simple heuristic-based AST creation
  const lines = code.split('\n');
  const children: ASTNode[] = [];

  for (const line of lines) {
    const trimmed = line.trim();
    if (trimmed.startsWith('function') || trimmed.startsWith('async function')) {
      children.push({
        type: 'FunctionDeclaration',
        children: [],
        startPosition: defaultPos,
        endPosition: defaultPos,
      });
    } else if (trimmed.startsWith('class')) {
      children.push({
        type: 'ClassDeclaration',
        children: [],
        startPosition: defaultPos,
        endPosition: defaultPos,
      });
    } else if (trimmed.startsWith('const') || trimmed.startsWith('let') || trimmed.startsWith('var')) {
      children.push({
        type: 'VariableDeclaration',
        children: [],
        startPosition: defaultPos,
        endPosition: defaultPos,
      });
    } else if (trimmed.startsWith('if')) {
      children.push({
        type: 'IfStatement',
        children: [],
        startPosition: defaultPos,
        endPosition: defaultPos,
      });
    } else if (trimmed.startsWith('for') || trimmed.startsWith('while')) {
      children.push({
        type: 'LoopStatement',
        children: [],
        startPosition: defaultPos,
        endPosition: defaultPos,
      });
    }
  }

  return {
    type: 'Program',
    children,
    startPosition: defaultPos,
    endPosition: defaultPos,
  };
}

/**
 * All pattern integration tools
 */
export const patternIntegrationTools: Tool[] = [
  learnPatternTool,
  consolidatePatternsTool,
  queryPatternRelationsTool,
  searchPatternsTool,
  getLearningStatsTool,
  importToKnowledgeGraphTool,
  exportKnowledgeGraphTool,
];

/**
 * Get all pattern integration tools
 */
export function getPatternIntegrationTools(): Tool[] {
  return patternIntegrationTools;
}

/**
 * Handle pattern integration tool calls
 */
export async function handlePatternIntegrationTool(
  name: string,
  args: Record<string, unknown>
): Promise<CallToolResult> {
  switch (name) {
    case 'pattern_learn':
      return handleLearnPattern(args);
    case 'pattern_consolidate':
      return handleConsolidatePatterns(args);
    case 'pattern_query_relations':
      return handleQueryRelations(args);
    case 'pattern_search':
      return handleSearchPatterns(args);
    case 'pattern_stats':
      return handleGetStats();
    case 'pattern_import_kg':
      return handleImportToKG(args);
    case 'pattern_export_kg':
      return handleExportKG();
    default:
      return {
        content: [{
          type: 'text',
          text: JSON.stringify({ error: `Unknown tool: ${name}` }),
        } as TextContent],
        isError: true,
      };
  }
}

/**
 * Reset instances (for testing)
 */
export function resetPatternIntegration(): void {
  storeInstance = null;
  bridgeInstance = null;
  wakeSleepInstance = null;
}
