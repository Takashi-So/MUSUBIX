/**
 * @nahisaho/musubix-codegraph - CodeGraph Facade
 *
 * Main entry point for code graph analysis
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-codegraph
 *
 * @see REQ-CG-API-001
 * @see REQ-CG-API-002
 * @see REQ-CG-API-003
 * @see DES-CG-001
 */

import type {
  CodeGraphOptions,
  Entity,
  QueryResult,
  IndexResult,
  GraphStatistics,
  CallPath,
  ModuleAnalysis,
  CodeSnippet,
  FileStructure,
  SearchResult,
  GraphQuery,
  DependencyOptions,
  LocalSearchOptions,
  GlobalSearchOptions,
  StorageAdapter,
} from './types.js';
import { DEFAULT_CODEGRAPH_OPTIONS } from './types.js';
import { CodeGraphEventEmitter } from './events/index.js';

/**
 * CodeGraph - Main facade for code graph analysis
 *
 * Provides a unified API for:
 * - AST parsing and entity extraction
 * - Graph construction and querying
 * - Dependency and call graph analysis
 * - GraphRAG-based semantic search
 *
 * @example
 * ```typescript
 * // Basic usage
 * const codeGraph = new CodeGraph({ storage: 'memory' });
 * await codeGraph.index('/path/to/repo');
 *
 * const deps = await codeGraph.findDependencies('UserService');
 * const callers = await codeGraph.findCallers('authenticate');
 * const results = await codeGraph.globalSearch('authentication');
 * ```
 *
 * @see REQ-CG-API-001 - Library as standalone
 * @see REQ-CG-API-002 - Programmatic API
 */
export class CodeGraph extends CodeGraphEventEmitter {
  private options: CodeGraphOptions;
  private storage: StorageAdapter | null = null;
  private initialized = false;

  /**
   * Create a new CodeGraph instance
   *
   * @param options - Configuration options
   */
  constructor(options: CodeGraphOptions = {}) {
    super();
    this.options = {
      ...options,
      parser: { ...DEFAULT_CODEGRAPH_OPTIONS.parser, ...options.parser },
      graph: { ...DEFAULT_CODEGRAPH_OPTIONS.graph, ...options.graph },
      indexer: { ...DEFAULT_CODEGRAPH_OPTIONS.indexer, ...options.indexer },
      graphrag: { ...DEFAULT_CODEGRAPH_OPTIONS.graphrag, ...options.graphrag },
    };
  }

  // =========================================================================
  // Event handler shortcuts
  // =========================================================================

  /**
   * Register a handler for indexing start events
   */
  onIndexingStart(handler: (path: string) => void): this {
    this.on('indexing:start', (data) => handler(data.path));
    return this;
  }

  /**
   * Register a handler for indexing complete events
   */
  onIndexingComplete(handler: (result: { entitiesIndexed: number; relationsIndexed: number; errors: unknown[] }) => void): this {
    this.on('indexing:complete', handler);
    return this;
  }

  /**
   * Register a handler for indexing progress events
   */
  onIndexingProgress(handler: (processed: number, total: number, currentFile: string) => void): this {
    this.on('indexing:progress', (data) => handler(data.processed, data.total, data.currentFile));
    return this;
  }

  /**
   * Register a handler for indexing error events
   */
  onIndexingError(handler: (error: Error, file?: string) => void): this {
    this.on('indexing:error', (data) => handler(data.error, data.file));
    return this;
  }

  /**
   * Register a handler for query start events
   */
  onQueryStart(handler: (query: GraphQuery) => void): this {
    this.on('query:start', (data) => handler(data.query));
    return this;
  }

  /**
   * Register a handler for query complete events
   */
  onQueryComplete(handler: (result: QueryResult, durationMs: number) => void): this {
    this.on('query:complete', (data) => handler(data.result, data.durationMs));
    return this;
  }

  /**
   * Initialize the CodeGraph instance
   *
   * @internal
   */
  private async ensureInitialized(): Promise<void> {
    if (this.initialized) return;

    // Initialize storage
    this.storage = await this.createStorage();
    await this.storage.initialize();

    this.initialized = true;
  }

  /**
   * Create storage adapter based on options
   *
   * @internal
   */
  private async createStorage(): Promise<StorageAdapter> {
    const storageOption = this.options.storage ?? 'memory';

    if (typeof storageOption === 'object') {
      // Custom storage adapter provided
      return storageOption;
    }

    // Lazy import storage implementations
    switch (storageOption) {
      case 'memory': {
        const { MemoryStorage } = await import('./storage/memory-storage.js');
        return new MemoryStorage();
      }
      case 'sqlite': {
        const { SQLiteStorage } = await import('./storage/sqlite-storage.js');
        return new SQLiteStorage(this.options.sqlitePath ?? '.codegraph/index.db');
      }
      default:
        throw new Error(`Unknown storage type: ${storageOption}`);
    }
  }

  // =========================================================================
  // Indexing Methods
  // =========================================================================

  /**
   * Index a repository or directory
   *
   * @param path - Path to repository or directory
   * @returns Index result with statistics
   *
   * @see REQ-CG-IDX-001
   *
   * @example
   * ```typescript
   * const result = await codeGraph.index('/path/to/repo');
   * console.log(`Indexed ${result.entitiesIndexed} entities`);
   * ```
   */
  async index(path: string): Promise<IndexResult> {
    await this.ensureInitialized();

    this.emitIndexingStart(path);

    try {
      const { Indexer } = await import('./indexer/index.js');
      const { ASTParser } = await import('./parser/index.js');
      const { GraphEngine } = await import('./graph/index.js');

      const parser = new ASTParser(this.options.parser);
      const graph = new GraphEngine(this.storage!, this.options.graph);
      const indexer = new Indexer(parser, graph, this.options.indexer);

      // Set up progress tracking
      indexer.onProgress((progress) => {
        this.emitIndexingProgress(progress.processed, progress.total, progress.currentFile);
      });

      const result = await indexer.indexRepository(path);

      this.emitIndexingComplete(result);
      return result;
    } catch (error) {
      const err = error instanceof Error ? error : new Error(String(error));
      this.emitIndexingError(err);
      throw err;
    }
  }

  /**
   * Reindex a repository (clear and index fresh)
   *
   * @param path - Path to repository or directory
   * @returns Index result with statistics
   */
  async reindex(path: string): Promise<IndexResult> {
    await this.ensureInitialized();
    await this.storage!.clear();
    return this.index(path);
  }

  // =========================================================================
  // Query Methods
  // =========================================================================

  /**
   * Query the code graph
   *
   * @param query - Search query string or query object
   * @returns Query result with matching entities
   *
   * @see REQ-CG-GRF-003
   */
  async query(query: string | GraphQuery): Promise<QueryResult> {
    await this.ensureInitialized();

    const graphQuery: GraphQuery = typeof query === 'string'
      ? { textSearch: query }
      : query;

    this.emitQueryStart(graphQuery);
    const startTime = Date.now();

    const { GraphEngine } = await import('./graph/index.js');
    const graph = new GraphEngine(this.storage!, this.options.graph);

    const result = await graph.query(graphQuery);
    const durationMs = Date.now() - startTime;

    this.emitQueryComplete(result, durationMs);
    return result;
  }

  /**
   * Find dependencies of an entity
   *
   * @param entityName - Name or ID of the entity
   * @param options - Dependency analysis options
   * @returns List of dependent entities
   *
   * @see REQ-CG-GRF-004
   */
  async findDependencies(entityName: string, options?: DependencyOptions): Promise<Entity[]> {
    await this.ensureInitialized();

    const { GraphEngine } = await import('./graph/index.js');
    const graph = new GraphEngine(this.storage!, this.options.graph);

    return graph.findDependencies(entityName, options?.depth ?? 3);
  }

  /**
   * Find callers of a function or method
   *
   * @param entityName - Name or ID of the function/method
   * @returns List of call paths
   *
   * @see REQ-CG-GRF-005
   */
  async findCallers(entityName: string): Promise<CallPath[]> {
    await this.ensureInitialized();

    const { GraphEngine } = await import('./graph/index.js');
    const graph = new GraphEngine(this.storage!, this.options.graph);

    return graph.findCallers(entityName);
  }

  /**
   * Find callees of a function or method
   *
   * @param entityName - Name or ID of the function/method
   * @returns List of call paths
   *
   * @see REQ-CG-GRF-005
   */
  async findCallees(entityName: string): Promise<CallPath[]> {
    await this.ensureInitialized();

    const { GraphEngine } = await import('./graph/index.js');
    const graph = new GraphEngine(this.storage!, this.options.graph);

    return graph.findCallees(entityName);
  }

  /**
   * Find implementations of an interface
   *
   * @param interfaceName - Name or ID of the interface
   * @returns List of implementing entities
   */
  async findImplementations(interfaceName: string): Promise<Entity[]> {
    await this.ensureInitialized();

    const { GraphEngine } = await import('./graph/index.js');
    const graph = new GraphEngine(this.storage!, this.options.graph);

    return graph.findImplementations(interfaceName);
  }

  /**
   * Analyze module structure
   *
   * @param path - Path to module/file
   * @returns Module analysis result
   */
  async analyzeModule(path: string): Promise<ModuleAnalysis> {
    await this.ensureInitialized();

    const { GraphEngine } = await import('./graph/index.js');
    const graph = new GraphEngine(this.storage!, this.options.graph);

    return graph.analyzeModule(path);
  }

  // =========================================================================
  // Code Retrieval Methods
  // =========================================================================

  /**
   * Get source code snippet for an entity
   *
   * @param entityId - Entity ID
   * @returns Code snippet with context
   */
  async getSnippet(entityId: string): Promise<CodeSnippet> {
    await this.ensureInitialized();

    const entity = await this.storage!.getEntity(entityId);
    if (!entity) {
      throw new Error(`Entity not found: ${entityId}`);
    }

    return {
      entityId,
      code: entity.sourceCode ?? '',
      language: entity.language ?? 'typescript',
      filePath: entity.filePath ?? '',
      startLine: entity.startLine ?? 0,
      endLine: entity.endLine ?? 0,
    };
  }

  /**
   * Get file structure overview
   *
   * @param path - File path
   * @returns File structure with entities
   */
  async getFileStructure(path: string): Promise<FileStructure> {
    await this.ensureInitialized();

    const entities = await this.storage!.queryEntities({
      filePath: path,
    });

    const imports = entities.filter(e => e.type === 'import');
    const exports = entities.filter(e => e.type === 'export');

    return {
      filePath: path,
      language: entities[0]?.language ?? 'typescript',
      entities,
      linesOfCode: Math.max(...entities.map(e => e.endLine ?? 0), 0),
      importCount: imports.length,
      exportCount: exports.length,
    };
  }

  // =========================================================================
  // GraphRAG Methods
  // =========================================================================

  /**
   * Global search across all code communities
   *
   * @param query - Search query
   * @param options - Search options
   * @returns Search results with relevance scores
   *
   * @see REQ-CG-RAG-002
   */
  async globalSearch(query: string, options?: GlobalSearchOptions): Promise<SearchResult[]> {
    await this.ensureInitialized();

    const { GraphRAGSearch } = await import('./graphrag/index.js');
    const { GraphEngine } = await import('./graph/index.js');

    const graph = new GraphEngine(this.storage!, this.options.graph);
    const search = new GraphRAGSearch(graph, this.options.graphrag);

    return search.globalSearch(query, options);
  }

  /**
   * Local search in entity neighborhood
   *
   * @param entityName - Entity name or ID
   * @param options - Search options
   * @returns Search results from entity neighborhood
   *
   * @see REQ-CG-RAG-003
   */
  async localSearch(entityName: string, options?: LocalSearchOptions): Promise<SearchResult[]> {
    await this.ensureInitialized();

    const { GraphRAGSearch } = await import('./graphrag/index.js');
    const { GraphEngine } = await import('./graph/index.js');

    const graph = new GraphEngine(this.storage!, this.options.graph);
    const search = new GraphRAGSearch(graph, this.options.graphrag);

    return search.localSearch(entityName, options);
  }

  // =========================================================================
  // Statistics Methods
  // =========================================================================

  /**
   * Get graph statistics
   *
   * @returns Graph statistics
   */
  async getStats(): Promise<GraphStatistics> {
    await this.ensureInitialized();

    const storageStats = await this.storage!.getStats();

    // Get entity type distribution
    const entities = await this.storage!.queryEntities({});
    const entitiesByType: Partial<Record<string, number>> = {};
    const languages = new Set<string>();

    for (const entity of entities) {
      entitiesByType[entity.type] = (entitiesByType[entity.type] ?? 0) + 1;
      if (entity.language) {
        languages.add(entity.language);
      }
    }

    return {
      entityCount: storageStats.entityCount,
      relationCount: storageStats.relationCount,
      fileCount: storageStats.fileCount,
      communityCount: 0, // Will be populated by GraphRAG
      entitiesByType: entitiesByType as Partial<Record<import('./types.js').EntityType, number>>,
      relationsByType: {},
      languages: Array.from(languages) as import('./types.js').Language[],
    };
  }

  // =========================================================================
  // Lifecycle Methods
  // =========================================================================

  /**
   * Close the CodeGraph instance and release resources
   */
  async close(): Promise<void> {
    if (this.storage) {
      await this.storage.close();
      this.storage = null;
    }
    this.initialized = false;
    this.removeAllListeners();
  }

  /**
   * Check if instance is initialized
   */
  isInitialized(): boolean {
    return this.initialized;
  }
}

/**
 * Create a new CodeGraph instance
 *
 * @param options - Configuration options
 * @returns CodeGraph instance
 */
export function createCodeGraph(options?: CodeGraphOptions): CodeGraph {
  return new CodeGraph(options);
}
