/**
 * Natural Language Query Engine for YATA
 *
 * Executes natural language queries against the knowledge graph
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/nlq
 *
 * @see REQ-YL-NLQ-001 - Natural Language Query Support
 */

import type { Entity, RelationType } from '../types.js';
import type { YataDatabase } from '../database.js';
import type { QueryEngine } from '../query-engine.js';
import {
  NLQueryParser,
  createNLQueryParser,
  type ParsedQuery,
  type NLQueryResult,
  type QueryParserConfig,
  type QueryIntent,
} from './parser.js';

// ============================================================================
// Types
// ============================================================================

/**
 * NL Query Engine configuration
 */
export interface NLQueryEngineConfig extends QueryParserConfig {
  /** Maximum results to return (default: 20) */
  maxResults?: number;
  /** Include related entities in results (default: true) */
  includeRelated?: boolean;
  /** Maximum depth for relationship traversal (default: 2) */
  maxTraversalDepth?: number;
}

/**
 * Internal query context
 */
interface QueryContext {
  parsedQuery: ParsedQuery;
  startTime: number;
  results: Entity[];
  relatedEntities: Entity[];
}

// ============================================================================
// Engine Implementation
// ============================================================================

/**
 * Natural Language Query Engine
 *
 * @example
 * ```typescript
 * const engine = createNLQueryEngine(db, queryEngine);
 *
 * // English queries
 * const result1 = await engine.query("What calls UserService?");
 * const result2 = await engine.query("Find all classes in app.services");
 *
 * // Japanese queries
 * const result3 = await engine.query("UserServiceを呼び出しているメソッドは?");
 * const result4 = await engine.query("app.servicesの全てのクラス");
 * ```
 */
export class NLQueryEngine {
  private db: YataDatabase;
  private parser: NLQueryParser;
  private config: Required<NLQueryEngineConfig>;

  constructor(
    db: YataDatabase,
    _queryEngine: QueryEngine,  // Reserved for future use
    config: NLQueryEngineConfig = {}
  ) {
    this.db = db;
    this.parser = createNLQueryParser({
      language: config.language,
      fuzzyMatching: config.fuzzyMatching,
      minConfidence: config.minConfidence,
    });
    this.config = {
      language: config.language ?? 'auto',
      fuzzyMatching: config.fuzzyMatching ?? true,
      minConfidence: config.minConfidence ?? 0.3,
      maxResults: config.maxResults ?? 20,
      includeRelated: config.includeRelated ?? true,
      maxTraversalDepth: config.maxTraversalDepth ?? 2,
    };
  }

  /**
   * Execute natural language query
   */
  async query(naturalLanguageQuery: string): Promise<NLQueryResult> {
    const startTime = Date.now();
    const parsedQuery = this.parser.parse(naturalLanguageQuery);

    const context: QueryContext = {
      parsedQuery,
      startTime,
      results: [],
      relatedEntities: [],
    };

    // Execute query based on intent
    await this.executeIntent(context);

    // Generate explanation
    const explanation = this.generateExplanation(context);

    return {
      parsedQuery,
      entities: context.results.slice(0, this.config.maxResults),
      relatedEntities: this.config.includeRelated
        ? context.relatedEntities.slice(0, this.config.maxResults)
        : undefined,
      explanation,
      executionTimeMs: Date.now() - startTime,
      totalMatches: context.results.length,
    };
  }

  /**
   * Alias for query - more conversational
   */
  async ask(question: string): Promise<NLQueryResult> {
    return this.query(question);
  }

  /**
   * Execute query based on detected intent
   */
  private async executeIntent(context: QueryContext): Promise<void> {
    const { parsedQuery } = context;

    switch (parsedQuery.intent) {
      case 'find_entity':
        await this.executeFindEntity(context);
        break;
      case 'find_callers':
        await this.executeFindCallers(context);
        break;
      case 'find_callees':
        await this.executeFindCallees(context);
        break;
      case 'find_implementations':
        await this.executeFindImplementations(context);
        break;
      case 'find_dependencies':
        await this.executeFindDependencies(context);
        break;
      case 'find_dependents':
        await this.executeFindDependents(context);
        break;
      case 'find_related':
        await this.executeFindRelated(context);
        break;
      case 'find_by_type':
        await this.executeFindByType(context);
        break;
      case 'find_by_namespace':
        await this.executeFindByNamespace(context);
        break;
      case 'explain_relationship':
        await this.executeExplainRelationship(context);
        break;
      case 'general_search':
      default:
        await this.executeGeneralSearch(context);
        break;
    }
  }

  /**
   * Find specific entity by name
   */
  private async executeFindEntity(context: QueryContext): Promise<void> {
    const { parsedQuery } = context;
    const name = parsedQuery.subject || parsedQuery.keywords[0];

    if (!name) {
      return;
    }

    // Try exact match first
    const result = this.db.queryEntities({ name }, this.config.maxResults, 0);
    context.results = result.entities;

    // If no exact match, try fuzzy search
    if (context.results.length === 0 && this.config.fuzzyMatching) {
      context.results = this.db.searchEntities(name, this.config.maxResults);
    }
  }

  /**
   * Find callers of a function/method/class
   */
  private async executeFindCallers(context: QueryContext): Promise<void> {
    const { parsedQuery } = context;
    const targetName = parsedQuery.subject;

    if (!targetName) {
      return;
    }

    // Find the target entity
    const targetResult = this.db.queryEntities({ name: targetName }, 1, 0);
    const target = targetResult.entities[0];

    if (!target) {
      // Try fuzzy search
      const fuzzyResults = this.db.searchEntities(targetName, 1);
      if (fuzzyResults.length === 0) {
        return;
      }
      context.relatedEntities = [fuzzyResults[0]];
    } else {
      context.relatedEntities = [target];
    }

    const targetId = context.relatedEntities[0]?.id;
    if (!targetId) return;

    // Find entities that call this target (incoming 'calls' relationships)
    const relationships = this.db.getRelationships(targetId, 'in');
    const callerRelationships = relationships.filter(r => r.type === 'calls');

    // Get caller entities
    const callerIds = callerRelationships.map(r => r.sourceId);
    for (const callerId of callerIds) {
      const caller = this.db.getEntity(callerId);
      if (caller) {
        context.results.push(caller);
      }
    }
  }

  /**
   * Find callees of a function/method/class
   */
  private async executeFindCallees(context: QueryContext): Promise<void> {
    const { parsedQuery } = context;
    const sourceName = parsedQuery.subject;

    if (!sourceName) {
      return;
    }

    // Find the source entity
    const sourceResult = this.db.queryEntities({ name: sourceName }, 1, 0);
    const source = sourceResult.entities[0];

    if (!source) {
      const fuzzyResults = this.db.searchEntities(sourceName, 1);
      if (fuzzyResults.length === 0) {
        return;
      }
      context.relatedEntities = [fuzzyResults[0]];
    } else {
      context.relatedEntities = [source];
    }

    const sourceId = context.relatedEntities[0]?.id;
    if (!sourceId) return;

    // Find entities this source calls (outgoing 'calls' relationships)
    const relationships = this.db.getRelationships(sourceId, 'out');
    const calleeRelationships = relationships.filter(r => r.type === 'calls');

    // Get callee entities
    const calleeIds = calleeRelationships.map(r => r.targetId);
    for (const calleeId of calleeIds) {
      const callee = this.db.getEntity(calleeId);
      if (callee) {
        context.results.push(callee);
      }
    }
  }

  /**
   * Find implementations of an interface
   */
  private async executeFindImplementations(context: QueryContext): Promise<void> {
    const { parsedQuery } = context;
    const interfaceName = parsedQuery.subject;

    if (!interfaceName) {
      return;
    }

    // Find the interface entity
    const interfaceResult = this.db.queryEntities(
      { name: interfaceName, type: 'interface' },
      1,
      0
    );
    let interfaceEntity = interfaceResult.entities[0];

    if (!interfaceEntity) {
      // Try without type filter
      const anyResult = this.db.queryEntities({ name: interfaceName }, 1, 0);
      interfaceEntity = anyResult.entities[0];
    }

    if (!interfaceEntity) {
      return;
    }

    context.relatedEntities = [interfaceEntity];

    // Find entities that implement this interface
    const relationships = this.db.getRelationships(interfaceEntity.id, 'in');
    const implementsRelationships = relationships.filter(r => r.type === 'implements');

    for (const rel of implementsRelationships) {
      const implementor = this.db.getEntity(rel.sourceId);
      if (implementor) {
        context.results.push(implementor);
      }
    }
  }

  /**
   * Find dependencies of an entity
   */
  private async executeFindDependencies(context: QueryContext): Promise<void> {
    const { parsedQuery } = context;
    const entityName = parsedQuery.subject;

    if (!entityName) {
      return;
    }

    const entityResult = this.db.queryEntities({ name: entityName }, 1, 0);
    const entity = entityResult.entities[0];

    if (!entity) {
      return;
    }

    context.relatedEntities = [entity];

    // Find outgoing dependency relationships
    const relationships = this.db.getRelationships(entity.id, 'out');
    const depTypes: RelationType[] = ['depends-on', 'imports', 'uses'];
    const depRelationships = relationships.filter(r => depTypes.includes(r.type));

    for (const rel of depRelationships) {
      const dep = this.db.getEntity(rel.targetId);
      if (dep) {
        context.results.push(dep);
      }
    }
  }

  /**
   * Find dependents of an entity
   */
  private async executeFindDependents(context: QueryContext): Promise<void> {
    const { parsedQuery } = context;
    const entityName = parsedQuery.subject;

    if (!entityName) {
      return;
    }

    const entityResult = this.db.queryEntities({ name: entityName }, 1, 0);
    const entity = entityResult.entities[0];

    if (!entity) {
      return;
    }

    context.relatedEntities = [entity];

    // Find incoming dependency relationships
    const relationships = this.db.getRelationships(entity.id, 'in');
    const depTypes: RelationType[] = ['depends-on', 'imports', 'uses'];
    const depRelationships = relationships.filter(r => depTypes.includes(r.type));

    for (const rel of depRelationships) {
      const dependent = this.db.getEntity(rel.sourceId);
      if (dependent) {
        context.results.push(dependent);
      }
    }
  }

  /**
   * Find related entities
   */
  private async executeFindRelated(context: QueryContext): Promise<void> {
    const { parsedQuery } = context;
    const entityName = parsedQuery.subject;

    if (!entityName) {
      return;
    }

    const entityResult = this.db.queryEntities({ name: entityName }, 1, 0);
    const entity = entityResult.entities[0];

    if (!entity) {
      return;
    }

    context.relatedEntities = [entity];

    // Get all relationships
    const relationships = this.db.getRelationships(entity.id, 'both');
    const relatedIds = new Set<string>();

    for (const rel of relationships) {
      if (rel.sourceId !== entity.id) {
        relatedIds.add(rel.sourceId);
      }
      if (rel.targetId !== entity.id) {
        relatedIds.add(rel.targetId);
      }
    }

    for (const relatedId of relatedIds) {
      const related = this.db.getEntity(relatedId);
      if (related) {
        context.results.push(related);
      }
    }
  }

  /**
   * Find entities by type
   */
  private async executeFindByType(context: QueryContext): Promise<void> {
    const { parsedQuery } = context;
    const entityTypes = parsedQuery.entityTypes;

    if (!entityTypes || entityTypes.length === 0) {
      return;
    }

    for (const type of entityTypes) {
      const result = this.db.queryEntities({ type }, this.config.maxResults, 0);
      context.results.push(...result.entities);
    }
  }

  /**
   * Find entities by namespace
   */
  private async executeFindByNamespace(context: QueryContext): Promise<void> {
    const { parsedQuery } = context;
    const namespace = parsedQuery.namespace;

    if (!namespace) {
      return;
    }

    const result = this.db.queryEntities(
      { namespace },
      this.config.maxResults,
      0
    );
    context.results = result.entities;
  }

  /**
   * Explain relationship between two entities
   */
  private async executeExplainRelationship(context: QueryContext): Promise<void> {
    const { parsedQuery } = context;
    const { subject, target } = parsedQuery;

    if (!subject || !target) {
      return;
    }

    // Find both entities
    const subjectResult = this.db.queryEntities({ name: subject }, 1, 0);
    const targetResult = this.db.queryEntities({ name: target }, 1, 0);

    const subjectEntity = subjectResult.entities[0];
    const targetEntity = targetResult.entities[0];

    if (subjectEntity) {
      context.results.push(subjectEntity);
    }
    if (targetEntity) {
      context.relatedEntities.push(targetEntity);
    }

    // Find path between them would require QueryEngine
    // For now, just return the entities
  }

  /**
   * General text search
   */
  private async executeGeneralSearch(context: QueryContext): Promise<void> {
    const { parsedQuery } = context;
    const keywords = parsedQuery.keywords;

    if (keywords.length === 0) {
      return;
    }

    // Search for each keyword and combine results
    const seenIds = new Set<string>();
    for (const keyword of keywords) {
      const results = this.db.searchEntities(keyword, this.config.maxResults);
      for (const entity of results) {
        if (!seenIds.has(entity.id)) {
          seenIds.add(entity.id);
          context.results.push(entity);
        }
      }
    }
  }

  /**
   * Generate human-readable explanation
   */
  private generateExplanation(context: QueryContext): string {
    const { parsedQuery, results, relatedEntities: _relatedEntities } = context;
    const lang = /[\u3040-\u309F\u30A0-\u30FF\u4E00-\u9FAF]/.test(parsedQuery.originalQuery) ? 'ja' : 'en';

    if (results.length === 0) {
      return lang === 'ja'
        ? `「${parsedQuery.originalQuery}」に一致する結果が見つかりませんでした。`
        : `No results found for "${parsedQuery.originalQuery}".`;
    }

    const intentDescriptions: Record<QueryIntent, { en: string; ja: string }> = {
      find_entity: {
        en: `Found ${results.length} entity(ies) matching "${parsedQuery.subject}"`,
        ja: `「${parsedQuery.subject}」に一致する${results.length}件のエンティティが見つかりました`,
      },
      find_callers: {
        en: `Found ${results.length} caller(s) of "${parsedQuery.subject}"`,
        ja: `「${parsedQuery.subject}」を呼び出している${results.length}件が見つかりました`,
      },
      find_callees: {
        en: `Found ${results.length} method(s)/function(s) called by "${parsedQuery.subject}"`,
        ja: `「${parsedQuery.subject}」が呼び出している${results.length}件が見つかりました`,
      },
      find_implementations: {
        en: `Found ${results.length} implementation(s) of "${parsedQuery.subject}"`,
        ja: `「${parsedQuery.subject}」を実装している${results.length}件が見つかりました`,
      },
      find_dependencies: {
        en: `Found ${results.length} dependenc(ies) of "${parsedQuery.subject}"`,
        ja: `「${parsedQuery.subject}」の依存先${results.length}件が見つかりました`,
      },
      find_dependents: {
        en: `Found ${results.length} dependent(s) on "${parsedQuery.subject}"`,
        ja: `「${parsedQuery.subject}」に依存している${results.length}件が見つかりました`,
      },
      find_related: {
        en: `Found ${results.length} entit(ies) related to "${parsedQuery.subject}"`,
        ja: `「${parsedQuery.subject}」に関連する${results.length}件が見つかりました`,
      },
      find_by_type: {
        en: `Found ${results.length} ${parsedQuery.entityTypes?.[0] || 'entity'}(ies)`,
        ja: `${parsedQuery.entityTypes?.[0] || 'エンティティ'}が${results.length}件見つかりました`,
      },
      find_by_namespace: {
        en: `Found ${results.length} entit(ies) in namespace "${parsedQuery.namespace}"`,
        ja: `名前空間「${parsedQuery.namespace}」に${results.length}件見つかりました`,
      },
      explain_relationship: {
        en: `Showing relationship between "${parsedQuery.subject}" and "${parsedQuery.target}"`,
        ja: `「${parsedQuery.subject}」と「${parsedQuery.target}」の関係を表示`,
      },
      general_search: {
        en: `Found ${results.length} result(s) for your search`,
        ja: `検索結果: ${results.length}件`,
      },
    };

    const desc = intentDescriptions[parsedQuery.intent];
    return lang === 'ja' ? desc.ja : desc.en;
  }
}

// ============================================================================
// Factory Function
// ============================================================================

/**
 * Create a new NL Query Engine
 */
export function createNLQueryEngine(
  db: YataDatabase,
  queryEngine: QueryEngine,
  config?: NLQueryEngineConfig
): NLQueryEngine {
  return new NLQueryEngine(db, queryEngine, config);
}
