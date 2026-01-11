/**
 * Natural Language Query Module for YATA
 *
 * Provides natural language query capabilities for knowledge graphs
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/nlq
 *
 * @see REQ-YL-NLQ-001 - Natural Language Query Support
 */

import type { Entity, EntityType, RelationType } from '../types.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Query intent extracted from natural language
 */
export type QueryIntent =
  | 'find_entity'           // Find specific entity
  | 'find_related'          // Find related entities
  | 'find_callers'          // Find callers of a function/method
  | 'find_callees'          // Find callees of a function/method
  | 'find_dependencies'     // Find dependencies
  | 'find_dependents'       // Find dependents
  | 'find_implementations'  // Find implementations of interface
  | 'find_by_type'          // Find by entity type
  | 'find_by_namespace'     // Find by namespace
  | 'explain_relationship'  // Explain relationship between entities
  | 'general_search';       // General text search

/**
 * Parsed natural language query
 */
export interface ParsedQuery {
  /** Original query text */
  originalQuery: string;
  /** Detected intent */
  intent: QueryIntent;
  /** Main subject/target of the query */
  subject?: string;
  /** Additional target (for relationships) */
  target?: string;
  /** Entity type filter */
  entityTypes?: EntityType[];
  /** Relationship type filter */
  relationshipTypes?: RelationType[];
  /** Namespace filter */
  namespace?: string;
  /** Search keywords */
  keywords: string[];
  /** Confidence score (0-1) */
  confidence: number;
}

/**
 * Natural language query result
 */
export interface NLQueryResult {
  /** Parsed query information */
  parsedQuery: ParsedQuery;
  /** Matching entities */
  entities: Entity[];
  /** Related entities (for relationship queries) */
  relatedEntities?: Entity[];
  /** Explanation of results */
  explanation: string;
  /** Execution time in ms */
  executionTimeMs: number;
  /** Total matches found */
  totalMatches: number;
}

/**
 * Query parser configuration
 */
export interface QueryParserConfig {
  /** Language for parsing (default: 'auto') */
  language?: 'en' | 'ja' | 'auto';
  /** Enable fuzzy matching */
  fuzzyMatching?: boolean;
  /** Minimum confidence threshold */
  minConfidence?: number;
}

// ============================================================================
// Intent Patterns
// ============================================================================

/**
 * English intent patterns
 */
const EN_PATTERNS: Array<{ pattern: RegExp; intent: QueryIntent; extract?: (match: RegExpMatchArray) => Partial<ParsedQuery> }> = [
  // Find callers
  {
    pattern: /(?:what|which|find|show|list)\s+(?:methods?|functions?|classes?)?\s*(?:call|invoke|use)s?\s+['"]?(\w+)['"]?/i,
    intent: 'find_callers',
    extract: (m) => ({ subject: m[1] }),
  },
  {
    pattern: /(?:who|what)\s+(?:is\s+)?calling\s+['"]?(\w+)['"]?/i,
    intent: 'find_callers',
    extract: (m) => ({ subject: m[1] }),
  },
  // Find callees
  {
    pattern: /(?:what|which)\s+(?:does|do)\s+['"]?(\w+)['"]?\s+(?:call|invoke|use)/i,
    intent: 'find_callees',
    extract: (m) => ({ subject: m[1] }),
  },
  {
    pattern: /(?:methods?|functions?)\s+called\s+(?:by|from)\s+['"]?(\w+)['"]?/i,
    intent: 'find_callees',
    extract: (m) => ({ subject: m[1] }),
  },
  // Find implementations
  {
    pattern: /(?:what|which|find|show|list)\s+(?:classes?)?\s*implement(?:s|ing)?\s+['"]?(\w+)['"]?/i,
    intent: 'find_implementations',
    extract: (m) => ({ subject: m[1] }),
  },
  {
    pattern: /implementations?\s+(?:of|for)\s+['"]?(\w+)['"]?/i,
    intent: 'find_implementations',
    extract: (m) => ({ subject: m[1] }),
  },
  // Find dependencies
  {
    pattern: /(?:what|which)\s+(?:does|do)\s+['"]?(\w+)['"]?\s+depend\s+on/i,
    intent: 'find_dependencies',
    extract: (m) => ({ subject: m[1] }),
  },
  {
    pattern: /dependencies\s+(?:of|for)\s+['"]?(\w+)['"]?/i,
    intent: 'find_dependencies',
    extract: (m) => ({ subject: m[1] }),
  },
  // Find dependents
  {
    pattern: /(?:what|which)\s+depend(?:s)?\s+on\s+['"]?(\w+)['"]?/i,
    intent: 'find_dependents',
    extract: (m) => ({ subject: m[1] }),
  },
  // Find related
  {
    pattern: /(?:related|associated)\s+(?:to|with)\s+['"]?(\w+)['"]?/i,
    intent: 'find_related',
    extract: (m) => ({ subject: m[1] }),
  },
  // Find by type
  {
    pattern: /(?:all|list|show|find)\s+(class(?:es)?|interface(?:s)?|function(?:s)?|method(?:s)?|type(?:s)?|enum(?:s)?)/i,
    intent: 'find_by_type',
    extract: (m) => ({ entityTypes: [normalizeEntityType(m[1])] }),
  },
  // Find by namespace
  {
    pattern: /(?:in|from|under)\s+(?:namespace|module|package)\s+['"]?([.\w]+)['"]?/i,
    intent: 'find_by_namespace',
    extract: (m) => ({ namespace: m[1] }),
  },
  // Find specific entity
  {
    pattern: /(?:find|show|where\s+is|locate)\s+['"]?(\w+)['"]?/i,
    intent: 'find_entity',
    extract: (m) => ({ subject: m[1] }),
  },
  // Explain relationship
  {
    pattern: /(?:relationship|connection)\s+between\s+['"]?(\w+)['"]?\s+and\s+['"]?(\w+)['"]?/i,
    intent: 'explain_relationship',
    extract: (m) => ({ subject: m[1], target: m[2] }),
  },
  {
    pattern: /how\s+(?:is|are)\s+['"]?(\w+)['"]?\s+(?:related|connected)\s+to\s+['"]?(\w+)['"]?/i,
    intent: 'explain_relationship',
    extract: (m) => ({ subject: m[1], target: m[2] }),
  },
];

/**
 * Japanese intent patterns
 */
const JA_PATTERNS: Array<{ pattern: RegExp; intent: QueryIntent; extract?: (match: RegExpMatchArray) => Partial<ParsedQuery> }> = [
  // Find callers (呼び出し元)
  {
    pattern: /['"]?(\w+)['"]?\s*を\s*呼び出し(?:ている|てる)(?:関数|メソッド|クラス)?/i,
    intent: 'find_callers',
    extract: (m) => ({ subject: m[1] }),
  },
  {
    pattern: /['"]?(\w+)['"]?\s*の\s*呼び出し元/i,
    intent: 'find_callers',
    extract: (m) => ({ subject: m[1] }),
  },
  // Find callees (呼び出し先)
  {
    pattern: /['"]?(\w+)['"]?\s*(?:が|は)\s*呼び出し(?:ている|てる)/i,
    intent: 'find_callees',
    extract: (m) => ({ subject: m[1] }),
  },
  {
    pattern: /['"]?(\w+)['"]?\s*の\s*呼び出し先/i,
    intent: 'find_callees',
    extract: (m) => ({ subject: m[1] }),
  },
  // Find implementations (実装)
  {
    pattern: /['"]?(\w+)['"]?\s*を\s*実装(?:している|してる)(?:クラス)?/i,
    intent: 'find_implementations',
    extract: (m) => ({ subject: m[1] }),
  },
  {
    pattern: /['"]?(\w+)['"]?\s*の\s*実装/i,
    intent: 'find_implementations',
    extract: (m) => ({ subject: m[1] }),
  },
  // Find dependencies (依存関係)
  {
    pattern: /['"]?(\w+)['"]?\s*(?:が|は)\s*(?:何に)?依存(?:している|してる)/i,
    intent: 'find_dependencies',
    extract: (m) => ({ subject: m[1] }),
  },
  {
    pattern: /['"]?(\w+)['"]?\s*の\s*依存(?:関係|先)?/i,
    intent: 'find_dependencies',
    extract: (m) => ({ subject: m[1] }),
  },
  // Find dependents (被依存)
  {
    pattern: /['"]?(\w+)['"]?\s*に\s*依存(?:している|してる)/i,
    intent: 'find_dependents',
    extract: (m) => ({ subject: m[1] }),
  },
  // Find related (関連)
  {
    pattern: /['"]?(\w+)['"]?\s*に?\s*関連(?:する|している|してる)/i,
    intent: 'find_related',
    extract: (m) => ({ subject: m[1] }),
  },
  // Find by type
  {
    pattern: /(?:すべて|全て)?の?\s*(クラス|インターフェース|関数|メソッド|型|列挙型)/i,
    intent: 'find_by_type',
    extract: (m) => ({ entityTypes: [normalizeJaEntityType(m[1])] }),
  },
  // Find by namespace
  {
    pattern: /(?:名前空間|モジュール|パッケージ)\s*['"]?([.\w]+)['"]?\s*(?:の|内の|にある)/i,
    intent: 'find_by_namespace',
    extract: (m) => ({ namespace: m[1] }),
  },
  // Find specific entity
  {
    pattern: /['"]?(\w+)['"]?\s*(?:を|は)\s*(?:探し|見つけ|検索)/i,
    intent: 'find_entity',
    extract: (m) => ({ subject: m[1] }),
  },
  {
    pattern: /['"]?(\w+)['"]?\s*(?:はどこ|について)/i,
    intent: 'find_entity',
    extract: (m) => ({ subject: m[1] }),
  },
  // Explain relationship
  {
    pattern: /['"]?(\w+)['"]?\s*と\s*['"]?(\w+)['"]?\s*の\s*(?:関係|つながり)/i,
    intent: 'explain_relationship',
    extract: (m) => ({ subject: m[1], target: m[2] }),
  },
];

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Normalize English entity type
 */
function normalizeEntityType(type: string): EntityType {
  const normalized = type.toLowerCase().replace(/s$/, '');
  const mapping: Record<string, EntityType> = {
    'class': 'class',
    'interface': 'interface',
    'function': 'function',
    'method': 'method',
    'type': 'type',
    'enum': 'enum',
    'variable': 'variable',
    'constant': 'constant',
    'module': 'module',
    'package': 'package',
  };
  return mapping[normalized] || 'unknown';
}

/**
 * Normalize Japanese entity type
 */
function normalizeJaEntityType(type: string): EntityType {
  const mapping: Record<string, EntityType> = {
    'クラス': 'class',
    'インターフェース': 'interface',
    '関数': 'function',
    'メソッド': 'method',
    '型': 'type',
    '列挙型': 'enum',
    '変数': 'variable',
    '定数': 'constant',
    'モジュール': 'module',
    'パッケージ': 'package',
  };
  return mapping[type] || 'unknown';
}

/**
 * Detect language of query
 */
function detectLanguage(query: string): 'en' | 'ja' {
  // Check for Japanese characters
  const hasJapanese = /[\u3040-\u309F\u30A0-\u30FF\u4E00-\u9FAF]/.test(query);
  return hasJapanese ? 'ja' : 'en';
}

/**
 * Extract keywords from query
 */
function extractKeywords(query: string): string[] {
  // Remove common stop words and extract meaningful words
  const stopWords = new Set([
    // English
    'the', 'a', 'an', 'is', 'are', 'was', 'were', 'be', 'been', 'being',
    'have', 'has', 'had', 'do', 'does', 'did', 'will', 'would', 'could',
    'should', 'may', 'might', 'must', 'shall', 'can', 'need', 'dare',
    'ought', 'used', 'to', 'of', 'in', 'for', 'on', 'with', 'at', 'by',
    'from', 'as', 'into', 'through', 'during', 'before', 'after', 'above',
    'below', 'between', 'under', 'again', 'further', 'then', 'once',
    'what', 'which', 'who', 'whom', 'this', 'that', 'these', 'those',
    'am', 'all', 'each', 'every', 'both', 'few', 'more', 'most', 'other',
    'some', 'such', 'no', 'nor', 'not', 'only', 'same', 'so', 'than',
    'too', 'very', 'just', 'and', 'but', 'if', 'or', 'because', 'until',
    'while', 'where', 'when', 'how', 'find', 'show', 'list', 'get',
    // Japanese particles
    'の', 'を', 'が', 'に', 'は', 'で', 'と', 'から', 'まで', 'より',
    'へ', 'や', 'か', 'も', 'など', 'て', 'た', 'だ', 'です', 'ます',
    'する', 'している', 'してる', 'ある', 'いる', 'なる', 'できる',
    'すべて', '全て', 'どこ', '何', 'どれ',
  ]);

  const words = query
    .toLowerCase()
    .replace(/['"]/g, '')
    .split(/[\s,.\-_]+/)
    .filter(w => w.length > 1 && !stopWords.has(w));

  return [...new Set(words)];
}

// ============================================================================
// Query Parser
// ============================================================================

/**
 * Natural Language Query Parser
 */
export class NLQueryParser {
  private config: QueryParserConfig;

  constructor(config: QueryParserConfig = {}) {
    this.config = {
      language: 'auto',
      fuzzyMatching: true,
      minConfidence: 0.3,
      ...config,
    };
  }

  /**
   * Parse natural language query
   */
  parse(query: string): ParsedQuery {
    const trimmedQuery = query.trim();
    const language = this.config.language === 'auto'
      ? detectLanguage(trimmedQuery)
      : this.config.language;

    const patterns = language === 'ja' ? JA_PATTERNS : EN_PATTERNS;

    // Try to match patterns
    for (const { pattern, intent, extract } of patterns) {
      const match = trimmedQuery.match(pattern);
      if (match) {
        const extracted = extract ? extract(match) : {};
        return {
          originalQuery: trimmedQuery,
          intent,
          keywords: extractKeywords(trimmedQuery),
          confidence: 0.9,
          ...extracted,
        };
      }
    }

    // Fall back to general search
    return {
      originalQuery: trimmedQuery,
      intent: 'general_search',
      keywords: extractKeywords(trimmedQuery),
      confidence: 0.5,
    };
  }

  /**
   * Get intent relationship types
   */
  getRelationshipTypes(intent: QueryIntent): RelationType[] {
    const mapping: Record<QueryIntent, RelationType[]> = {
      'find_callers': ['calls'],
      'find_callees': ['calls'],
      'find_dependencies': ['depends-on', 'imports', 'uses'],
      'find_dependents': ['depends-on', 'imports', 'uses'],
      'find_implementations': ['implements'],
      'find_related': ['calls', 'uses', 'depends-on', 'implements', 'extends'],
      'find_entity': [],
      'find_by_type': [],
      'find_by_namespace': [],
      'explain_relationship': [],
      'general_search': [],
    };
    return mapping[intent] || [];
  }
}

// ============================================================================
// Exports
// ============================================================================

/**
 * Create a new NL Query Parser
 */
export function createNLQueryParser(config?: QueryParserConfig): NLQueryParser {
  return new NLQueryParser(config);
}
