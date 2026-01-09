/**
 * CodeGraph Command
 *
 * CLI commands for code knowledge graph operations
 *
 * @packageDocumentation
 * @module cli/commands/codegraph
 *
 * @see TSK-CG-070 - CLI Integration
 * @see REQ-CG-001 - CodeGraph Requirements
 */

import type { Command } from 'commander';
import { resolve } from 'path';
import { ExitCode, outputResult } from '../base.js';

// Lazy loading for CodeGraph
type CodeGraphInstance = Awaited<
  ReturnType<typeof import('@nahisaho/musubix-codegraph').createCodeGraph>
>;

let codeGraphInstance: CodeGraphInstance | null = null;

async function getCodeGraph(): Promise<CodeGraphInstance> {
  if (!codeGraphInstance) {
    const { createCodeGraph } = await import('@nahisaho/musubix-codegraph');
    codeGraphInstance = await createCodeGraph();
  }
  return codeGraphInstance;
}

/**
 * Index command options
 */
export interface IndexOptions {
  verbose?: boolean;
  exclude?: string[];
  maxDepth?: number;
  json?: boolean;
  quiet?: boolean;
}

/**
 * Query command options
 */
export interface QueryOptions {
  type?: string;
  scope?: string;
  limit?: number;
  verbose?: boolean;
  json?: boolean;
  quiet?: boolean;
}

/**
 * Search command options
 */
export interface SearchOptions {
  local?: boolean;
  context?: string;
  radius?: number;
  limit?: number;
  verbose?: boolean;
  json?: boolean;
  quiet?: boolean;
}

/**
 * Index a directory for code analysis
 */
async function indexDirectory(
  path: string,
  options: IndexOptions
): Promise<void> {
  if (options.verbose) {
    console.log(`Indexing: ${path}`);
  }

  try {
    const absolutePath = resolve(path);
    const codeGraph = await getCodeGraph();

    await codeGraph.index(absolutePath);
    const stats = await codeGraph.getStats();

    outputResult(
      {
        success: true,
        message: 'Indexing complete',
        stats: {
          totalEntities: stats.entityCount,
          totalRelations: stats.relationCount,
          files: stats.fileCount,
        },
      },
      { json: options.json, quiet: options.quiet }
    );
  } catch (err) {
    outputResult(
      {
        success: false,
        error: err instanceof Error ? err.message : 'Unknown error',
      },
      { json: options.json, quiet: options.quiet }
    );
    process.exit(ExitCode.GENERAL_ERROR);
  }
}

/**
 * Query entities in the code graph
 */
async function queryEntities(
  name: string | undefined,
  options: QueryOptions
): Promise<void> {
  try {
    const codeGraph = await getCodeGraph();
    
    // Build query
    const query: Record<string, unknown> = {};
    if (name) {
      query.textSearch = name;
    }
    if (options.type) {
      query.entityTypes = [options.type];
    }
    if (options.limit) {
      query.limit = options.limit;
    }

    const result = await codeGraph.query(query);
    const entities = result.entities || [];

    outputResult(
      {
        success: true,
        count: entities.length,
        entities: entities.map((e) => ({
          id: e.id,
          name: e.name,
          type: e.type,
          namespace: e.namespace,
          filePath: e.filePath,
          docstring: e.docstring?.substring(0, 100),
        })),
      },
      { json: options.json, quiet: options.quiet }
    );
  } catch (err) {
    outputResult(
      {
        success: false,
        error: err instanceof Error ? err.message : 'Unknown error',
      },
      { json: options.json, quiet: options.quiet }
    );
    process.exit(ExitCode.GENERAL_ERROR);
  }
}

/**
 * Find dependencies of an entity
 */
async function findDependencies(name: string, options: { json?: boolean; quiet?: boolean }): Promise<void> {
  try {
    const codeGraph = await getCodeGraph();
    const deps = await codeGraph.findDependencies(name);

    outputResult(
      {
        success: true,
        entity: name,
        dependencies: deps.map((d) => ({
          id: d.id,
          name: d.name,
          type: d.type,
          filePath: d.filePath,
        })),
        count: deps.length,
      },
      { json: options.json, quiet: options.quiet }
    );
  } catch (err) {
    outputResult(
      {
        success: false,
        error: err instanceof Error ? err.message : 'Unknown error',
      },
      { json: options.json, quiet: options.quiet }
    );
    process.exit(ExitCode.GENERAL_ERROR);
  }
}

/**
 * Find callers of a function
 */
async function findCallers(name: string, options: { json?: boolean; quiet?: boolean }): Promise<void> {
  try {
    const codeGraph = await getCodeGraph();
    const callers = await codeGraph.findCallers(name);

    outputResult(
      {
        success: true,
        function: name,
        callers: callers.map((c) => ({
          from: c.from?.name,
          to: c.to?.name,
          path: c.path?.map((e) => e.name),
        })),
        count: callers.length,
      },
      { json: options.json, quiet: options.quiet }
    );
  } catch (err) {
    outputResult(
      {
        success: false,
        error: err instanceof Error ? err.message : 'Unknown error',
      },
      { json: options.json, quiet: options.quiet }
    );
    process.exit(ExitCode.GENERAL_ERROR);
  }
}

/**
 * Find callees of a function
 */
async function findCallees(name: string, options: { json?: boolean; quiet?: boolean }): Promise<void> {
  try {
    const codeGraph = await getCodeGraph();
    const callees = await codeGraph.findCallees(name);

    outputResult(
      {
        success: true,
        function: name,
        callees: callees.map((c) => ({
          from: c.from?.name,
          to: c.to?.name,
          path: c.path?.map((e) => e.name),
        })),
        count: callees.length,
      },
      { json: options.json, quiet: options.quiet }
    );
  } catch (err) {
    outputResult(
      {
        success: false,
        error: err instanceof Error ? err.message : 'Unknown error',
      },
      { json: options.json, quiet: options.quiet }
    );
    process.exit(ExitCode.GENERAL_ERROR);
  }
}

/**
 * Semantic search across the codebase
 */
async function search(
  query: string,
  options: SearchOptions
): Promise<void> {
  try {
    const codeGraph = await getCodeGraph();
    
    let results: Array<{
      entity: { id: string; name: string; type: string; filePath?: string };
      score: number;
    }>;

    if (options.local && options.context) {
      const localResults = await codeGraph.localSearch(query, {
        radius: options.radius || 2,
      });
      results = localResults;
    } else {
      results = await codeGraph.globalSearch(query);
    }

    const limited = options.limit ? results.slice(0, options.limit) : results;

    outputResult(
      {
        success: true,
        query,
        mode: options.local ? 'local' : 'global',
        results: limited.map((r) => ({
          name: r.entity.name,
          type: r.entity.type,
          filePath: r.entity.filePath,
          score: r.score,
        })),
        count: limited.length,
      },
      { json: options.json, quiet: options.quiet }
    );
  } catch (err) {
    outputResult(
      {
        success: false,
        error: err instanceof Error ? err.message : 'Unknown error',
      },
      { json: options.json, quiet: options.quiet }
    );
    process.exit(ExitCode.GENERAL_ERROR);
  }
}

/**
 * Show graph statistics
 */
async function showStats(options: { json?: boolean; quiet?: boolean }): Promise<void> {
  try {
    const codeGraph = await getCodeGraph();
    const stats = await codeGraph.getStats();

    outputResult(
      {
        success: true,
        stats: {
          totalEntities: stats.entityCount,
          totalRelations: stats.relationCount,
          fileCount: stats.fileCount,
          communityCount: stats.communityCount,
          entitiesByType: stats.entitiesByType,
          relationsByType: stats.relationsByType,
          languages: stats.languages,
        },
      },
      { json: options.json, quiet: options.quiet }
    );
  } catch (err) {
    outputResult(
      {
        success: false,
        error: err instanceof Error ? err.message : 'Unknown error',
      },
      { json: options.json, quiet: options.quiet }
    );
    process.exit(ExitCode.GENERAL_ERROR);
  }
}

/**
 * Register codegraph commands
 */
export function registerCodeGraphCommand(program: Command): void {
  const cg = program.command('cg').description('Code graph operations');

  // Alias: codegraph
  program
    .command('codegraph')
    .description('Code graph operations (alias for cg)')
    .action(() => {
      cg.help();
    });

  // cg index
  cg.command('index <path>')
    .description('Index a directory or repository for code analysis')
    .option('-v, --verbose', 'Verbose output')
    .option('-e, --exclude <patterns...>', 'Exclude patterns')
    .option('-d, --max-depth <n>', 'Maximum directory depth', parseInt)
    .option('--json', 'Output in JSON format')
    .option('-q, --quiet', 'Suppress non-essential output')
    .action(async (path: string, options: IndexOptions) => {
      await indexDirectory(path, options);
    });

  // cg query
  cg.command('query [name]')
    .description('Query entities in the code graph')
    .option('-t, --type <type>', 'Filter by entity type (function, class, etc.)')
    .option('-s, --scope <scope>', 'Filter by scope (public, private, etc.)')
    .option('-l, --limit <n>', 'Limit results', parseInt)
    .option('-v, --verbose', 'Verbose output')
    .option('--json', 'Output in JSON format')
    .option('-q, --quiet', 'Suppress non-essential output')
    .action(async (name: string | undefined, options: QueryOptions) => {
      await queryEntities(name, options);
    });

  // cg deps
  cg.command('deps <name>')
    .description('Find dependencies of an entity')
    .option('--json', 'Output in JSON format')
    .option('-q, --quiet', 'Suppress non-essential output')
    .action(async (name: string, options: { json?: boolean; quiet?: boolean }) => {
      await findDependencies(name, options);
    });

  // cg callers
  cg.command('callers <name>')
    .description('Find all callers of a function')
    .option('--json', 'Output in JSON format')
    .option('-q, --quiet', 'Suppress non-essential output')
    .action(async (name: string, options: { json?: boolean; quiet?: boolean }) => {
      await findCallers(name, options);
    });

  // cg callees
  cg.command('callees <name>')
    .description('Find all functions called by a function')
    .option('--json', 'Output in JSON format')
    .option('-q, --quiet', 'Suppress non-essential output')
    .action(async (name: string, options: { json?: boolean; quiet?: boolean }) => {
      await findCallees(name, options);
    });

  // cg search
  cg.command('search <query>')
    .description('Semantic search across the codebase')
    .option('-L, --local', 'Use local context search')
    .option('-c, --context <entityId>', 'Start entity for local search')
    .option('-r, --radius <n>', 'Search radius for local search', parseInt)
    .option('-l, --limit <n>', 'Limit results', parseInt)
    .option('-v, --verbose', 'Verbose output')
    .option('--json', 'Output in JSON format')
    .option('-q, --quiet', 'Suppress non-essential output')
    .action(async (query: string, options: SearchOptions) => {
      await search(query, options);
    });

  // cg stats
  cg.command('stats')
    .description('Show code graph statistics')
    .option('--json', 'Output in JSON format')
    .option('-q, --quiet', 'Suppress non-essential output')
    .action(async (options: { json?: boolean; quiet?: boolean }) => {
      await showStats(options);
    });
}
