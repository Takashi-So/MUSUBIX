/**
 * Dependency Analyzer
 * 
 * Analyzes code dependencies and generates dependency graphs
 * 
 * @packageDocumentation
 * @module codegen/dependency-analyzer
 * 
 * @see REQ-COD-004 - Dependency Analysis
 * @see Article VI - Implementation Standards
 */

/**
 * Dependency type
 */
export type DependencyType =
  | 'import'
  | 'require'
  | 'extends'
  | 'implements'
  | 'composes'
  | 'aggregates'
  | 'uses'
  | 'type-reference'
  | 'dynamic';

/**
 * Dependency strength
 */
export type DependencyStrength = 'strong' | 'medium' | 'weak';

/**
 * Module type
 */
export type ModuleType = 'internal' | 'external' | 'builtin' | 'relative';

/**
 * Dependency info
 */
export interface DependencyInfo {
  /** Source module */
  source: string;
  /** Target module */
  target: string;
  /** Dependency type */
  type: DependencyType;
  /** Strength */
  strength: DependencyStrength;
  /** Module type */
  moduleType: ModuleType;
  /** Import specifiers */
  specifiers?: string[];
  /** Is default import */
  isDefault?: boolean;
  /** Is namespace import */
  isNamespace?: boolean;
  /** Is type-only import */
  isTypeOnly?: boolean;
  /** Location in source */
  location?: {
    line: number;
    column: number;
  };
}

/**
 * Module info
 */
export interface ModuleInfo {
  /** Module path */
  path: string;
  /** Module name */
  name: string;
  /** Module type */
  type: ModuleType;
  /** Exports */
  exports: ExportInfo[];
  /** Dependencies */
  dependencies: DependencyInfo[];
  /** Dependents */
  dependents: string[];
}

/**
 * Export info
 */
export interface ExportInfo {
  /** Export name */
  name: string;
  /** Is default export */
  isDefault: boolean;
  /** Export type */
  type: 'function' | 'class' | 'variable' | 'type' | 'interface' | 'enum';
  /** Line number */
  line?: number;
}

/**
 * Dependency graph
 */
export interface DependencyGraph {
  /** All modules */
  modules: Map<string, ModuleInfo>;
  /** All dependencies */
  dependencies: DependencyInfo[];
  /** Root modules */
  roots: string[];
  /** Leaf modules */
  leaves: string[];
  /** Cycles */
  cycles: string[][];
}

/**
 * Dependency analysis result
 */
export interface DependencyAnalysisResult {
  /** Dependency graph */
  graph: DependencyGraph;
  /** Metrics */
  metrics: DependencyMetrics;
  /** Issues */
  issues: DependencyIssue[];
  /** Recommendations */
  recommendations: string[];
}

/**
 * Dependency metrics
 */
export interface DependencyMetrics {
  /** Total modules */
  totalModules: number;
  /** Total dependencies */
  totalDependencies: number;
  /** Internal dependencies */
  internalDependencies: number;
  /** External dependencies */
  externalDependencies: number;
  /** Average dependencies per module */
  avgDependenciesPerModule: number;
  /** Maximum dependencies */
  maxDependencies: number;
  /** Module with max dependencies */
  maxDependenciesModule?: string;
  /** Coupling factor (0-1) */
  couplingFactor: number;
  /** Cyclomatic complexity of graph */
  graphComplexity: number;
  /** Number of cycles */
  cycleCount: number;
}

/**
 * Dependency issue
 */
export interface DependencyIssue {
  /** Issue ID */
  id: string;
  /** Severity */
  severity: 'error' | 'warning' | 'info';
  /** Issue type */
  type: 'cycle' | 'unused' | 'missing' | 'version' | 'security' | 'deprecated' | 'coupling';
  /** Message */
  message: string;
  /** Affected modules */
  modules: string[];
  /** Suggestion */
  suggestion?: string;
}

/**
 * Dependency analyzer configuration
 */
export interface DependencyAnalyzerConfig {
  /** Include dev dependencies */
  includeDevDependencies: boolean;
  /** Include type-only imports */
  includeTypeOnly: boolean;
  /** Maximum allowed dependencies per module */
  maxDependenciesPerModule: number;
  /** Maximum allowed coupling factor */
  maxCouplingFactor: number;
  /** Detect cycles */
  detectCycles: boolean;
  /** Detect unused */
  detectUnused: boolean;
  /** Known external packages */
  knownExternals?: string[];
  /** Alias mappings */
  aliases?: Record<string, string>;
}

/**
 * Default configuration
 */
export const DEFAULT_ANALYZER_CONFIG: DependencyAnalyzerConfig = {
  includeDevDependencies: false,
  includeTypeOnly: true,
  maxDependenciesPerModule: 20,
  maxCouplingFactor: 0.5,
  detectCycles: true,
  detectUnused: true,
};

/**
 * Built-in Node.js modules
 */
const BUILTIN_MODULES = new Set([
  'assert', 'buffer', 'child_process', 'cluster', 'console', 'constants',
  'crypto', 'dgram', 'dns', 'domain', 'events', 'fs', 'http', 'https',
  'module', 'net', 'os', 'path', 'perf_hooks', 'process', 'punycode',
  'querystring', 'readline', 'repl', 'stream', 'string_decoder', 'sys',
  'timers', 'tls', 'tty', 'url', 'util', 'v8', 'vm', 'wasi', 'worker_threads', 'zlib',
  'node:assert', 'node:buffer', 'node:child_process', 'node:cluster',
  'node:console', 'node:constants', 'node:crypto', 'node:dgram', 'node:dns',
  'node:domain', 'node:events', 'node:fs', 'node:http', 'node:https',
  'node:module', 'node:net', 'node:os', 'node:path', 'node:perf_hooks',
  'node:process', 'node:punycode', 'node:querystring', 'node:readline',
  'node:repl', 'node:stream', 'node:string_decoder', 'node:sys',
  'node:timers', 'node:tls', 'node:tty', 'node:url', 'node:util', 'node:v8',
  'node:vm', 'node:wasi', 'node:worker_threads', 'node:zlib',
]);

/**
 * Dependency Analyzer
 */
export class DependencyAnalyzer {
  private config: DependencyAnalyzerConfig;

  constructor(config?: Partial<DependencyAnalyzerConfig>) {
    this.config = { ...DEFAULT_ANALYZER_CONFIG, ...config };
  }

  /**
   * Analyze dependencies in code
   */
  analyze(
    code: string,
    filePath: string
  ): DependencyInfo[] {
    const dependencies: DependencyInfo[] = [];

    // Parse import statements
    dependencies.push(...this.parseImports(code, filePath));

    // Parse require statements
    dependencies.push(...this.parseRequires(code, filePath));

    // Parse class relationships
    dependencies.push(...this.parseClassRelationships(code, filePath));

    // Parse type references
    if (this.config.includeTypeOnly) {
      dependencies.push(...this.parseTypeReferences(code, filePath));
    }

    return dependencies;
  }

  /**
   * Analyze multiple files and build graph
   */
  analyzeProject(
    files: Array<{ path: string; content: string }>
  ): DependencyAnalysisResult {
    const graph = this.buildGraph(files);
    const metrics = this.calculateMetrics(graph);
    const issues = this.detectIssues(graph, metrics);
    const recommendations = this.generateRecommendations(graph, metrics, issues);

    return {
      graph,
      metrics,
      issues,
      recommendations,
    };
  }

  /**
   * Parse ES6 import statements
   */
  private parseImports(code: string, source: string): DependencyInfo[] {
    const dependencies: DependencyInfo[] = [];
    
    // Standard imports: import { x } from 'module'
    const importRegex = /import\s+(?:(type)\s+)?(?:(\*\s+as\s+\w+)|(\w+)(?:\s*,\s*\{([^}]*)\})?|\{([^}]*)\})\s+from\s+['"]([^'"]+)['"]/g;
    let match;

    while ((match = importRegex.exec(code)) !== null) {
      const isTypeOnly = match[1] === 'type';
      const isNamespace = !!match[2];
      const defaultImport = match[3];
      const namedWithDefault = match[4];
      const namedImports = match[5];
      const target = match[6];
      
      const line = code.substring(0, match.index).split('\n').length;

      const specifiers: string[] = [];
      if (defaultImport) specifiers.push(defaultImport);
      if (namedWithDefault) {
        specifiers.push(...namedWithDefault.split(',').map((s) => s.trim()));
      }
      if (namedImports) {
        specifiers.push(...namedImports.split(',').map((s) => s.trim().split(' as ')[0]));
      }

      dependencies.push({
        source,
        target,
        type: 'import',
        strength: this.calculateStrength(target),
        moduleType: this.getModuleType(target),
        specifiers: specifiers.length > 0 ? specifiers : undefined,
        isDefault: !!defaultImport,
        isNamespace,
        isTypeOnly,
        location: { line, column: 0 },
      });
    }

    // Side-effect imports: import 'module'
    const sideEffectRegex = /import\s+['"]([^'"]+)['"]/g;
    while ((match = sideEffectRegex.exec(code)) !== null) {
      const target = match[1];
      const line = code.substring(0, match.index).split('\n').length;

      // Skip if already captured
      if (dependencies.some((d) => d.target === target)) continue;

      dependencies.push({
        source,
        target,
        type: 'import',
        strength: 'weak',
        moduleType: this.getModuleType(target),
        location: { line, column: 0 },
      });
    }

    return dependencies;
  }

  /**
   * Parse CommonJS require statements
   */
  private parseRequires(code: string, source: string): DependencyInfo[] {
    const dependencies: DependencyInfo[] = [];
    const requireRegex = /(?:const|let|var)\s+(?:(\w+)|{([^}]+)})\s*=\s*require\s*\(\s*['"]([^'"]+)['"]\s*\)/g;
    let match;

    while ((match = requireRegex.exec(code)) !== null) {
      const defaultRequire = match[1];
      const destructured = match[2];
      const target = match[3];
      const line = code.substring(0, match.index).split('\n').length;

      const specifiers: string[] = [];
      if (defaultRequire) specifiers.push(defaultRequire);
      if (destructured) {
        specifiers.push(...destructured.split(',').map((s) => s.trim().split(':')[0]));
      }

      dependencies.push({
        source,
        target,
        type: 'require',
        strength: this.calculateStrength(target),
        moduleType: this.getModuleType(target),
        specifiers: specifiers.length > 0 ? specifiers : undefined,
        isDefault: !!defaultRequire,
        location: { line, column: 0 },
      });
    }

    // Dynamic require
    const dynamicRegex = /require\s*\(\s*(['"`])([^'"]+)\1\s*\)/g;
    while ((match = dynamicRegex.exec(code)) !== null) {
      const target = match[2];
      if (dependencies.some((d) => d.target === target)) continue;

      const line = code.substring(0, match.index).split('\n').length;
      dependencies.push({
        source,
        target,
        type: 'dynamic',
        strength: 'weak',
        moduleType: this.getModuleType(target),
        location: { line, column: 0 },
      });
    }

    return dependencies;
  }

  /**
   * Parse class relationships (extends, implements)
   */
  private parseClassRelationships(code: string, source: string): DependencyInfo[] {
    const dependencies: DependencyInfo[] = [];
    const classRegex = /class\s+\w+(?:\s+extends\s+(\w+))?(?:\s+implements\s+([^{]+))?\s*\{/g;
    let match;

    while ((match = classRegex.exec(code)) !== null) {
      const extendsClass = match[1];
      const implementsList = match[2];
      const line = code.substring(0, match.index).split('\n').length;

      if (extendsClass) {
        dependencies.push({
          source,
          target: extendsClass,
          type: 'extends',
          strength: 'strong',
          moduleType: 'internal',
          location: { line, column: 0 },
        });
      }

      if (implementsList) {
        for (const impl of implementsList.split(',')) {
          dependencies.push({
            source,
            target: impl.trim(),
            type: 'implements',
            strength: 'strong',
            moduleType: 'internal',
            location: { line, column: 0 },
          });
        }
      }
    }

    return dependencies;
  }

  /**
   * Parse type references
   */
  private parseTypeReferences(code: string, source: string): DependencyInfo[] {
    const dependencies: DependencyInfo[] = [];
    
    // Type annotations: : TypeName
    const typeRegex = /:\s*(\w+)(?:<[^>]+>)?(?:\[\])?/g;
    let match;
    const foundTypes = new Set<string>();

    while ((match = typeRegex.exec(code)) !== null) {
      const typeName = match[1];
      
      // Skip primitives and common types
      if (this.isPrimitive(typeName)) continue;
      if (foundTypes.has(typeName)) continue;

      foundTypes.add(typeName);
      const line = code.substring(0, match.index).split('\n').length;

      dependencies.push({
        source,
        target: typeName,
        type: 'type-reference',
        strength: 'weak',
        moduleType: 'internal',
        isTypeOnly: true,
        location: { line, column: 0 },
      });
    }

    return dependencies;
  }

  /**
   * Build dependency graph
   */
  private buildGraph(
    files: Array<{ path: string; content: string }>
  ): DependencyGraph {
    const modules = new Map<string, ModuleInfo>();
    const allDependencies: DependencyInfo[] = [];

    // First pass: analyze all files
    for (const file of files) {
      const deps = this.analyze(file.content, file.path);
      const exports = this.parseExports(file.content);

      modules.set(file.path, {
        path: file.path,
        name: this.getModuleName(file.path),
        type: 'internal',
        exports,
        dependencies: deps,
        dependents: [],
      });

      allDependencies.push(...deps);
    }

    // Second pass: build dependents
    for (const [path, module] of modules) {
      for (const dep of module.dependencies) {
        const resolvedTarget = this.resolveModule(dep.target, path);
        const targetModule = modules.get(resolvedTarget);
        if (targetModule) {
          targetModule.dependents.push(path);
        }
      }
    }

    // Find roots and leaves
    const roots = [...modules.entries()]
      .filter(([_, m]) => m.dependents.length === 0)
      .map(([p]) => p);

    const leaves = [...modules.entries()]
      .filter(([_, m]) => m.dependencies.filter((d) => d.moduleType === 'internal').length === 0)
      .map(([p]) => p);

    // Detect cycles
    const cycles = this.config.detectCycles ? this.detectCycles(modules) : [];

    return {
      modules,
      dependencies: allDependencies,
      roots,
      leaves,
      cycles,
    };
  }

  /**
   * Parse exports
   */
  private parseExports(code: string): ExportInfo[] {
    const exports: ExportInfo[] = [];
    
    // Named exports
    const namedExportRegex = /export\s+(?:(async\s+)?function|class|const|let|var|interface|type|enum)\s+(\w+)/g;
    let match;

    while ((match = namedExportRegex.exec(code)) !== null) {
      const name = match[2];
      const line = code.substring(0, match.index).split('\n').length;
      const isFunction = match[0].includes('function');
      const isClass = match[0].includes('class');
      const isInterface = match[0].includes('interface');
      const isType = match[0].includes('type');
      const isEnum = match[0].includes('enum');

      exports.push({
        name,
        isDefault: false,
        type: isFunction ? 'function' :
              isClass ? 'class' :
              isInterface ? 'interface' :
              isType ? 'type' :
              isEnum ? 'enum' : 'variable',
        line,
      });
    }

    // Default export
    const defaultExportRegex = /export\s+default\s+(?:(async\s+)?function|class)?\s*(\w+)?/g;
    while ((match = defaultExportRegex.exec(code)) !== null) {
      const name = match[2] || 'default';
      const line = code.substring(0, match.index).split('\n').length;

      exports.push({
        name,
        isDefault: true,
        type: match[0].includes('class') ? 'class' :
              match[0].includes('function') ? 'function' : 'variable',
        line,
      });
    }

    return exports;
  }

  /**
   * Calculate metrics
   */
  private calculateMetrics(graph: DependencyGraph): DependencyMetrics {
    const totalModules = graph.modules.size;
    const internalDeps = graph.dependencies.filter((d) => d.moduleType === 'internal');
    const externalDeps = graph.dependencies.filter((d) => d.moduleType === 'external');

    let maxDeps = 0;
    let maxDepsModule: string | undefined;

    for (const [path, module] of graph.modules) {
      const depCount = module.dependencies.length;
      if (depCount > maxDeps) {
        maxDeps = depCount;
        maxDepsModule = path;
      }
    }

    const avgDeps = totalModules > 0
      ? graph.dependencies.length / totalModules
      : 0;

    // Coupling factor: actual dependencies / maximum possible dependencies
    const maxPossibleDeps = totalModules * (totalModules - 1);
    const couplingFactor = maxPossibleDeps > 0
      ? internalDeps.length / maxPossibleDeps
      : 0;

    // Graph complexity: edges - nodes + 2 * connected components
    const edges = internalDeps.length;
    const nodes = totalModules;
    const connectedComponents = this.countConnectedComponents(graph);
    const graphComplexity = Math.max(0, edges - nodes + 2 * connectedComponents);

    return {
      totalModules,
      totalDependencies: graph.dependencies.length,
      internalDependencies: internalDeps.length,
      externalDependencies: externalDeps.length,
      avgDependenciesPerModule: Math.round(avgDeps * 100) / 100,
      maxDependencies: maxDeps,
      maxDependenciesModule: maxDepsModule,
      couplingFactor: Math.round(couplingFactor * 1000) / 1000,
      graphComplexity,
      cycleCount: graph.cycles.length,
    };
  }

  /**
   * Count connected components
   */
  private countConnectedComponents(graph: DependencyGraph): number {
    const visited = new Set<string>();
    let components = 0;

    for (const path of graph.modules.keys()) {
      if (!visited.has(path)) {
        this.dfs(path, graph, visited);
        components++;
      }
    }

    return components;
  }

  /**
   * DFS for connected components
   */
  private dfs(
    start: string,
    graph: DependencyGraph,
    visited: Set<string>
  ): void {
    const stack = [start];

    while (stack.length > 0) {
      const current = stack.pop()!;
      if (visited.has(current)) continue;
      visited.add(current);

      const module = graph.modules.get(current);
      if (module) {
        for (const dep of module.dependencies) {
          const resolved = this.resolveModule(dep.target, current);
          if (graph.modules.has(resolved) && !visited.has(resolved)) {
            stack.push(resolved);
          }
        }
        for (const dependent of module.dependents) {
          if (!visited.has(dependent)) {
            stack.push(dependent);
          }
        }
      }
    }
  }

  /**
   * Detect cycles using DFS
   */
  private detectCycles(modules: Map<string, ModuleInfo>): string[][] {
    const cycles: string[][] = [];
    const visited = new Set<string>();
    const recursionStack = new Set<string>();
    const path: string[] = [];

    const dfs = (node: string): void => {
      if (recursionStack.has(node)) {
        // Found cycle
        const cycleStart = path.indexOf(node);
        const cycle = path.slice(cycleStart);
        cycle.push(node);
        cycles.push(cycle);
        return;
      }

      if (visited.has(node)) return;

      visited.add(node);
      recursionStack.add(node);
      path.push(node);

      const module = modules.get(node);
      if (module) {
        for (const dep of module.dependencies) {
          if (dep.moduleType === 'internal') {
            const resolved = this.resolveModule(dep.target, node);
            if (modules.has(resolved)) {
              dfs(resolved);
            }
          }
        }
      }

      path.pop();
      recursionStack.delete(node);
    };

    for (const path of modules.keys()) {
      visited.clear();
      recursionStack.clear();
      dfs(path);
    }

    return cycles;
  }

  /**
   * Detect issues
   */
  private detectIssues(
    graph: DependencyGraph,
    metrics: DependencyMetrics
  ): DependencyIssue[] {
    const issues: DependencyIssue[] = [];

    // Circular dependencies
    for (const cycle of graph.cycles) {
      issues.push({
        id: `cycle-${cycle.join('-')}`,
        severity: 'error',
        type: 'cycle',
        message: `Circular dependency detected: ${cycle.join(' → ')}`,
        modules: cycle,
        suggestion: 'Consider extracting shared code into a separate module',
      });
    }

    // High coupling modules
    for (const [path, module] of graph.modules) {
      if (module.dependencies.length > this.config.maxDependenciesPerModule) {
        issues.push({
          id: `high-coupling-${path}`,
          severity: 'warning',
          type: 'coupling',
          message: `Module ${path} has too many dependencies (${module.dependencies.length} > ${this.config.maxDependenciesPerModule})`,
          modules: [path],
          suggestion: 'Consider splitting this module or using dependency injection',
        });
      }
    }

    // High overall coupling
    if (metrics.couplingFactor > this.config.maxCouplingFactor) {
      issues.push({
        id: 'high-overall-coupling',
        severity: 'warning',
        type: 'coupling',
        message: `Overall coupling factor is too high (${metrics.couplingFactor} > ${this.config.maxCouplingFactor})`,
        modules: [],
        suggestion: 'Consider refactoring to reduce inter-module dependencies',
      });
    }

    // Unused exports (if detectUnused is enabled)
    if (this.config.detectUnused) {
      for (const [path, module] of graph.modules) {
        for (const exp of module.exports) {
          const isUsed = [...graph.modules.values()].some((m) =>
            m.dependencies.some((d) =>
              d.specifiers?.includes(exp.name)
            )
          );

          if (!isUsed && !exp.isDefault && module.dependents.length === 0) {
            issues.push({
              id: `unused-export-${path}-${exp.name}`,
              severity: 'info',
              type: 'unused',
              message: `Export '${exp.name}' in ${path} appears to be unused`,
              modules: [path],
            });
          }
        }
      }
    }

    return issues;
  }

  /**
   * Generate recommendations
   */
  private generateRecommendations(
    graph: DependencyGraph,
    metrics: DependencyMetrics,
    issues: DependencyIssue[]
  ): string[] {
    const recommendations: string[] = [];

    // Based on issues
    if (issues.some((i) => i.type === 'cycle')) {
      recommendations.push('Break circular dependencies by extracting shared interfaces');
    }

    if (issues.some((i) => i.type === 'coupling')) {
      recommendations.push('Use dependency injection to reduce coupling');
      recommendations.push('Consider applying the SOLID principles');
    }

    // Based on metrics
    if (metrics.avgDependenciesPerModule > 10) {
      recommendations.push('Average dependencies per module is high - consider splitting modules');
    }

    if (graph.roots.length === 0 && graph.modules.size > 0) {
      recommendations.push('No root modules found - all modules have dependents');
    }

    if (metrics.graphComplexity > metrics.totalModules) {
      recommendations.push('Graph complexity is high - simplify module relationships');
    }

    return recommendations;
  }

  /**
   * Get module type
   */
  private getModuleType(target: string): ModuleType {
    if (BUILTIN_MODULES.has(target)) return 'builtin';
    if (target.startsWith('.') || target.startsWith('/')) return 'relative';
    if (target.startsWith('@') || /^[a-z]/i.test(target)) return 'external';
    return 'internal';
  }

  /**
   * Calculate dependency strength
   */
  private calculateStrength(target: string): DependencyStrength {
    const type = this.getModuleType(target);
    if (type === 'external') return 'strong';
    if (type === 'relative') return 'medium';
    return 'weak';
  }

  /**
   * Check if type is primitive
   */
  private isPrimitive(type: string): boolean {
    return ['string', 'number', 'boolean', 'void', 'null', 'undefined',
            'any', 'unknown', 'never', 'object', 'symbol', 'bigint',
            'Array', 'Object', 'Function', 'Promise', 'Map', 'Set',
            'Record', 'Partial', 'Required', 'Readonly', 'Pick', 'Omit'].includes(type);
  }

  /**
   * Get module name from path
   */
  private getModuleName(path: string): string {
    const parts = path.split('/');
    const filename = parts[parts.length - 1];
    return filename.replace(/\.(ts|js|tsx|jsx)$/, '');
  }

  /**
   * Resolve module path
   */
  private resolveModule(target: string, source: string): string {
    // Handle aliases
    if (this.config.aliases) {
      for (const [alias, path] of Object.entries(this.config.aliases)) {
        if (target.startsWith(alias)) {
          return target.replace(alias, path);
        }
      }
    }

    // Handle relative paths
    if (target.startsWith('.')) {
      const sourceParts = source.split('/');
      sourceParts.pop();
      const targetParts = target.split('/');

      for (const part of targetParts) {
        if (part === '..') {
          sourceParts.pop();
        } else if (part !== '.') {
          sourceParts.push(part);
        }
      }

      return sourceParts.join('/');
    }

    return target;
  }

  /**
   * Generate dependency report
   */
  generateReport(result: DependencyAnalysisResult): string {
    const lines: string[] = [];

    lines.push('# Dependency Analysis Report');
    lines.push('');
    lines.push('## Metrics');
    lines.push(`- Total Modules: ${result.metrics.totalModules}`);
    lines.push(`- Total Dependencies: ${result.metrics.totalDependencies}`);
    lines.push(`- Internal Dependencies: ${result.metrics.internalDependencies}`);
    lines.push(`- External Dependencies: ${result.metrics.externalDependencies}`);
    lines.push(`- Avg Dependencies/Module: ${result.metrics.avgDependenciesPerModule}`);
    lines.push(`- Coupling Factor: ${result.metrics.couplingFactor}`);
    lines.push(`- Cycles: ${result.metrics.cycleCount}`);
    lines.push('');

    if (result.issues.length > 0) {
      lines.push('## Issues');
      for (const issue of result.issues) {
        const icon = issue.severity === 'error' ? '❌' :
                     issue.severity === 'warning' ? '⚠️' : 'ℹ️';
        lines.push(`${icon} [${issue.type}] ${issue.message}`);
        if (issue.suggestion) {
          lines.push(`   → ${issue.suggestion}`);
        }
      }
      lines.push('');
    }

    if (result.recommendations.length > 0) {
      lines.push('## Recommendations');
      for (const rec of result.recommendations) {
        lines.push(`- ${rec}`);
      }
    }

    return lines.join('\n');
  }
}

/**
 * Create dependency analyzer instance
 */
export function createDependencyAnalyzer(
  config?: Partial<DependencyAnalyzerConfig>
): DependencyAnalyzer {
  return new DependencyAnalyzer(config);
}
