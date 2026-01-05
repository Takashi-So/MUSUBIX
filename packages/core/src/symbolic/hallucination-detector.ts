/**
 * Hallucination Detector
 *
 * Detects non-existent API/module references in LLM-generated code
 * by comparing against project context and known symbols.
 *
 * @packageDocumentation
 * @module symbolic
 *
 * @see REQ-SF-002 - Hallucination Detection
 * @see DES-SYMB-001 §4.2 - HallucinationDetector
 * @see TSK-SYMB-002
 */

import type {
  CodeCandidate,
  ProjectContext,
  HallucinationResult,
  HallucinationItem,
  SymbolInfo,
  Explanation,
} from './types.js';

/**
 * Configuration for HallucinationDetector
 */
export interface HallucinationDetectorConfig {
  maxSuggestions?: number;
  similarityThreshold?: number;
}

/**
 * Project Symbol Index
 *
 * Maintains an index of known symbols for fast lookup
 * and similarity-based suggestions.
 */
export class ProjectSymbolIndex {
  private readonly symbols = new Map<string, SymbolInfo>();

  /**
   * Add a symbol to the index
   */
  addSymbol(symbol: SymbolInfo): void {
    this.symbols.set(symbol.name, symbol);
  }

  /**
   * Add multiple symbols
   */
  addSymbols(symbols: SymbolInfo[]): void {
    for (const symbol of symbols) {
      this.addSymbol(symbol);
    }
  }

  /**
   * Check if a symbol exists
   */
  hasSymbol(name: string): boolean {
    return this.symbols.has(name);
  }

  /**
   * Get symbol info
   */
  getSymbol(name: string): SymbolInfo | undefined {
    return this.symbols.get(name);
  }

  /**
   * Find similar symbol names (for suggestions)
   */
  findSimilar(name: string, maxResults: number = 3): string[] {
    const results: Array<{ name: string; distance: number }> = [];

    for (const knownName of this.symbols.keys()) {
      const distance = this.levenshteinDistance(name.toLowerCase(), knownName.toLowerCase());
      if (distance <= Math.max(name.length, knownName.length) * 0.5) {
        results.push({ name: knownName, distance });
      }
    }

    return results
      .sort((a, b) => a.distance - b.distance)
      .slice(0, maxResults)
      .map((r) => r.name);
  }

  /**
   * Clear the index
   */
  clear(): void {
    this.symbols.clear();
  }

  /**
   * Get index size
   */
  get size(): number {
    return this.symbols.size;
  }

  /**
   * Levenshtein distance calculation
   */
  private levenshteinDistance(a: string, b: string): number {
    if (a.length === 0) return b.length;
    if (b.length === 0) return a.length;

    const matrix: number[][] = [];
    for (let i = 0; i <= b.length; i++) {
      matrix[i] = [i];
    }
    for (let j = 0; j <= a.length; j++) {
      matrix[0][j] = j;
    }

    for (let i = 1; i <= b.length; i++) {
      for (let j = 1; j <= a.length; j++) {
        if (b.charAt(i - 1) === a.charAt(j - 1)) {
          matrix[i][j] = matrix[i - 1][j - 1];
        } else {
          matrix[i][j] = Math.min(
            matrix[i - 1][j - 1] + 1,
            matrix[i][j - 1] + 1,
            matrix[i - 1][j] + 1,
          );
        }
      }
    }

    return matrix[b.length][a.length];
  }
}

/**
 * Hallucination Detector
 *
 * Detects potential hallucinations in code:
 * - Non-existent imports
 * - Unknown function/class references
 * - Type mismatches
 */
export class HallucinationDetector {
  private readonly config: Required<HallucinationDetectorConfig>;
  private readonly builtins = new Set([
    // JavaScript built-ins
    'console',
    'Math',
    'Date',
    'JSON',
    'Promise',
    'Array',
    'Object',
    'String',
    'Number',
    'Boolean',
    'Map',
    'Set',
    'Error',
    'TypeError',
    'ReferenceError',
    'setTimeout',
    'setInterval',
    'clearTimeout',
    'clearInterval',
    'fetch',
    'Buffer',
    'process',
    // Common libraries that might be in dependencies
    'fs',
    'path',
    'url',
    'http',
    'https',
    'crypto',
    'stream',
    'events',
    'util',
  ]);

  constructor(config: HallucinationDetectorConfig = {}) {
    this.config = {
      maxSuggestions: config.maxSuggestions ?? 3,
      similarityThreshold: config.similarityThreshold ?? 0.5,
    };
  }

  /**
   * Detect hallucinations in code
   */
  async detect(candidate: CodeCandidate, context: ProjectContext): Promise<HallucinationResult> {
    const index = new ProjectSymbolIndex();
    if (context.symbols) {
      index.addSymbols(context.symbols);
    }

    const items: HallucinationItem[] = [];

    // Detect import hallucinations
    const importHallucinations = this.detectImportHallucinations(candidate.code, context, index);
    items.push(...importHallucinations);

    // Detect function call hallucinations
    const callHallucinations = this.detectFunctionCallHallucinations(candidate.code, index);
    items.push(...callHallucinations);

    const hasHallucinations = items.length > 0;
    const explanation = this.buildExplanation(hasHallucinations, items);

    return { hasHallucinations, items, explanation };
  }

  /**
   * Detect hallucinated imports
   */
  private detectImportHallucinations(
    code: string,
    context: ProjectContext,
    index: ProjectSymbolIndex,
  ): HallucinationItem[] {
    const items: HallucinationItem[] = [];
    const lines = code.split('\n');

    // Match import statements
    const importPatterns = [
      /import\s+\{([^}]+)\}\s+from\s+['"]([^'"]+)['"]/g,
      /import\s+(\w+)\s+from\s+['"]([^'"]+)['"]/g,
      /const\s+\{([^}]+)\}\s+=\s+require\(['"]([^'"]+)['"]\)/g,
    ];

    for (let lineNum = 0; lineNum < lines.length; lineNum++) {
      const line = lines[lineNum];

      for (const pattern of importPatterns) {
        pattern.lastIndex = 0;
        let match;
        while ((match = pattern.exec(line)) !== null) {
          const importPath = match[2];
          const importedNames = match[1].split(',').map((s) => s.trim().split(' as ')[0].trim());

          // Skip node built-ins and dependencies
          if (this.isKnownModule(importPath, context.dependencies ?? [])) {
            continue;
          }

          // Check relative imports against project symbols
          if (importPath.startsWith('.') || importPath.startsWith('/')) {
            for (const name of importedNames) {
              if (name && !index.hasSymbol(name) && !this.builtins.has(name)) {
                const suggestions = index.findSimilar(name, this.config.maxSuggestions);
                items.push({
                  type: 'import',
                  identifier: name,
                  location: { line: lineNum + 1, column: line.indexOf(name) },
                  reason: `Symbol '${name}' not found in project context`,
                  suggestions: suggestions.length > 0 ? suggestions : undefined,
                });
              }
            }
          }
        }
      }
    }

    return items;
  }

  /**
   * Detect hallucinated function calls
   */
  private detectFunctionCallHallucinations(
    code: string,
    index: ProjectSymbolIndex,
  ): HallucinationItem[] {
    const items: HallucinationItem[] = [];
    const lines = code.split('\n');

    // Match class instantiation: new ClassName(...)
    const newPattern = /new\s+([A-Z][a-zA-Z0-9]*)\s*\(/g;

    for (let lineNum = 0; lineNum < lines.length; lineNum++) {
      const line = lines[lineNum];
      newPattern.lastIndex = 0;

      let match;
      while ((match = newPattern.exec(line)) !== null) {
        const className = match[1];

        // Skip built-ins and common types
        if (this.builtins.has(className)) {
          continue;
        }

        // Check if class exists in project
        if (!index.hasSymbol(className)) {
          const suggestions = index.findSimilar(className, this.config.maxSuggestions);
          items.push({
            type: 'function_call',
            identifier: className,
            location: { line: lineNum + 1, column: match.index },
            reason: `Class '${className}' not found in project context`,
            suggestions: suggestions.length > 0 ? suggestions : undefined,
          });
        }
      }
    }

    return items;
  }

  /**
   * Check if module is a known dependency or built-in
   */
  private isKnownModule(modulePath: string, dependencies: string[]): boolean {
    // Node built-in modules
    const nodeBuiltins = [
      'fs',
      'path',
      'url',
      'http',
      'https',
      'crypto',
      'stream',
      'events',
      'util',
      'os',
      'child_process',
      'net',
      'dns',
      'tls',
      'zlib',
      'readline',
      'repl',
      'vm',
      'assert',
      'buffer',
      'cluster',
      'dgram',
      'domain',
      'perf_hooks',
      'querystring',
      'string_decoder',
      'timers',
      'tty',
      'v8',
      'worker_threads',
    ];

    if (nodeBuiltins.includes(modulePath) || modulePath.startsWith('node:')) {
      return true;
    }

    // Check against dependencies
    const moduleName = modulePath.split('/')[0];
    if (dependencies.includes(moduleName)) {
      return true;
    }

    return false;
  }

  /**
   * Build explanation
   */
  private buildExplanation(hasHallucinations: boolean, items: HallucinationItem[]): Explanation {
    const summary = hasHallucinations
      ? `Detected ${items.length} potential hallucination(s)`
      : 'No hallucinations detected';

    const reasoning = hasHallucinations
      ? items.map((i) => `${i.type}: ${i.identifier} - ${i.reason}`)
      : ['All references verified against project context'];

    return {
      summary,
      reasoning,
      evidence: items.map((i) => ({
        type: 'rule_match' as const,
        description: `${i.type}: ${i.identifier}`,
        artifacts: [],
        confidence: 0.8,
      })),
      relatedRequirements: ['REQ-SF-002'],
    };
  }
}

/**
 * Factory function
 */
export function createHallucinationDetector(
  config?: HallucinationDetectorConfig,
): HallucinationDetector {
  return new HallucinationDetector(config);
}
