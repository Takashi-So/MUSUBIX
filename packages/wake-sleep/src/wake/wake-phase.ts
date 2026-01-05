/**
 * @fileoverview Wake phase executor for pattern collection
 * @traceability TSK-WAKE-001, REQ-WAKE-001-F001
 */

import type { WakeTask, WakeResult, PatternCandidate } from '../types.js';

/**
 * Pattern extractor configuration
 */
export interface PatternExtractorConfig {
  minPatternSize: number;
  maxPatternSize: number;
  minOccurrences: number;
  similarityThreshold: number;
}

/**
 * AST Node representation
 */
interface ASTNode {
  type: string;
  name?: string;
  value?: unknown;
  children?: ASTNode[];
  isHole?: boolean;
  holeId?: string;
}

/**
 * Wake phase executor
 * 
 * @description
 * Collects patterns from tasks during the wake phase.
 * - Processes code, requirements, and design tasks
 * - Extracts pattern candidates using AST analysis
 * - Supports TypeScript, JavaScript, and pseudo-code
 */
export class WakePhase {
  private tasks: WakeTask[] = [];
  private results: WakeResult[] = [];
  private extractorConfig: PatternExtractorConfig;
  private patternCache: Map<string, PatternCandidate[]> = new Map();

  constructor(config?: Partial<PatternExtractorConfig>) {
    this.extractorConfig = {
      minPatternSize: config?.minPatternSize ?? 3,
      maxPatternSize: config?.maxPatternSize ?? 50,
      minOccurrences: config?.minOccurrences ?? 2,
      similarityThreshold: config?.similarityThreshold ?? 0.7,
    };
  }

  /**
   * Add task for processing
   */
  addTask(task: WakeTask): void {
    this.tasks.push(task);
  }

  /**
   * Process single task and extract patterns
   */
  async processTask(task: WakeTask): Promise<WakeResult> {
    const startTime = Date.now();

    try {
      // Extract patterns based on task type
      const patterns = await this.extractPatterns(task);
      const patternNames = patterns.map(p => p.name);

      // Cache patterns for later analysis
      this.patternCache.set(task.id, patterns);

      const result: WakeResult = {
        taskId: task.id,
        success: true,
        extractedPatterns: patternNames,
        confidence: this.calculateConfidence(patterns),
        processingTime: Date.now() - startTime,
        metadata: {
          patternCount: patterns.length,
          taskType: task.type,
          contentLength: task.content.length,
        },
      };

      this.results.push(result);
      return result;
    } catch (error) {
      const result: WakeResult = {
        taskId: task.id,
        success: false,
        extractedPatterns: [],
        confidence: 0,
        processingTime: Date.now() - startTime,
        error: error instanceof Error ? error.message : String(error),
      };

      this.results.push(result);
      return result;
    }
  }

  /**
   * Process all pending tasks
   */
  async processAll(): Promise<WakeResult[]> {
    const results: WakeResult[] = [];
    for (const task of this.tasks) {
      const result = await this.processTask(task);
      results.push(result);
    }
    this.tasks = [];
    return results;
  }

  /**
   * Extract patterns from task content
   */
  private async extractPatterns(task: WakeTask): Promise<PatternCandidate[]> {
    const patterns: PatternCandidate[] = [];

    switch (task.type) {
      case 'code':
        patterns.push(...this.extractCodePatterns(task.content));
        break;
      case 'requirements':
        patterns.push(...this.extractRequirementPatterns(task.content));
        break;
      case 'design':
        patterns.push(...this.extractDesignPatterns(task.content));
        break;
    }

    return patterns;
  }

  /**
   * Extract patterns from code
   */
  private extractCodePatterns(content: string): PatternCandidate[] {
    const patterns: PatternCandidate[] = [];
    const ast = this.parseToAST(content);

    // Find repeated subtrees
    const subtrees = this.findRepeatedSubtrees(ast);

    for (const [subtreeHash, nodes] of subtrees.entries()) {
      if (nodes.length >= this.extractorConfig.minOccurrences) {
        const abstracted = this.antiUnify(nodes);
        if (abstracted) {
          patterns.push({
            name: `${this.generatePatternName(abstracted)}_${subtreeHash.slice(0, 8)}`,
            structure: abstracted,
            occurrences: nodes.length,
            confidence: this.calculatePatternConfidence(abstracted, nodes),
            source: 'code',
          });
        }
      }
    }

    // Detect common design patterns
    patterns.push(...this.detectDesignPatternUsage(ast));

    return patterns;
  }

  /**
   * Extract patterns from requirements
   */
  private extractRequirementPatterns(content: string): PatternCandidate[] {
    const patterns: PatternCandidate[] = [];

    // EARS pattern detection
    const earsPatterns = [
      { regex: /WHEN\s+(.+?),?\s+THE\s+(.+?)\s+SHALL\s+(.+)/gi, name: 'EARS-Event' },
      { regex: /WHILE\s+(.+?),?\s+THE\s+(.+?)\s+SHALL\s+(.+)/gi, name: 'EARS-State' },
      { regex: /THE\s+(.+?)\s+SHALL\s+(.+)/gi, name: 'EARS-Ubiquitous' },
      { regex: /THE\s+(.+?)\s+SHALL\s+NOT\s+(.+)/gi, name: 'EARS-Unwanted' },
      { regex: /IF\s+(.+?),?\s+THEN\s+THE\s+(.+?)\s+SHALL\s+(.+)/gi, name: 'EARS-Optional' },
    ];

    for (const { regex, name } of earsPatterns) {
      const matches = [...content.matchAll(regex)];
      if (matches.length > 0) {
        patterns.push({
          name,
          structure: { type: 'requirement-pattern', template: name, groups: matches[0].slice(1) },
          occurrences: matches.length,
          confidence: 0.9,
          source: 'requirements',
        });
      }
    }

    return patterns;
  }

  /**
   * Extract patterns from design documents
   */
  private extractDesignPatterns(content: string): PatternCandidate[] {
    const patterns: PatternCandidate[] = [];

    // C4 pattern detection
    const c4Patterns = [
      { marker: /container|component|context|code/gi, name: 'C4-Model' },
      { marker: /service|repository|factory|controller/gi, name: 'LayeredArchitecture' },
      { marker: /API|REST|GraphQL/gi, name: 'APIDesign' },
    ];

    for (const { marker, name } of c4Patterns) {
      const matches = content.match(marker);
      if (matches && matches.length >= 2) {
        patterns.push({
          name,
          structure: { type: 'design-pattern', matches: matches.slice(0, 5) },
          occurrences: matches.length,
          confidence: 0.7,
          source: 'design',
        });
      }
    }

    return patterns;
  }

  /**
   * Parse content to simple AST
   */
  private parseToAST(content: string): ASTNode {
    // Simplified AST parser for common patterns
    const lines = content.split('\n').filter(l => l.trim());
    const root: ASTNode = { type: 'Program', children: [] };

    for (const line of lines) {
      const trimmed = line.trim();

      // Function detection
      if (/^(async\s+)?function\s+\w+|^(const|let|var)\s+\w+\s*=\s*(async\s+)?\(/.test(trimmed)) {
        root.children!.push({ type: 'FunctionDeclaration', value: trimmed });
      }
      // Class detection
      else if (/^(export\s+)?(abstract\s+)?class\s+\w+/.test(trimmed)) {
        root.children!.push({ type: 'ClassDeclaration', value: trimmed });
      }
      // Interface detection
      else if (/^(export\s+)?interface\s+\w+/.test(trimmed)) {
        root.children!.push({ type: 'InterfaceDeclaration', value: trimmed });
      }
      // Import detection
      else if (/^import\s+/.test(trimmed)) {
        root.children!.push({ type: 'ImportDeclaration', value: trimmed });
      }
      // Method call detection
      else if (/\.\w+\(/.test(trimmed)) {
        root.children!.push({ type: 'CallExpression', value: trimmed });
      }
    }

    return root;
  }

  /**
   * Find repeated subtrees in AST
   */
  private findRepeatedSubtrees(ast: ASTNode): Map<string, ASTNode[]> {
    const subtrees = new Map<string, ASTNode[]>();

    const traverse = (node: ASTNode): void => {
      const hash = this.hashNode(node);
      if (!subtrees.has(hash)) {
        subtrees.set(hash, []);
      }
      subtrees.get(hash)!.push(node);

      if (node.children) {
        for (const child of node.children) {
          traverse(child);
        }
      }
    };

    traverse(ast);
    return subtrees;
  }

  /**
   * Hash AST node for comparison
   */
  private hashNode(node: ASTNode): string {
    const parts = [node.type];
    if (node.children) {
      for (const child of node.children) {
        parts.push(child.type);
      }
    }
    return parts.join(':');
  }

  /**
   * Anti-unify multiple AST nodes to create abstracted pattern
   */
  private antiUnify(nodes: ASTNode[]): ASTNode | null {
    if (nodes.length === 0) return null;
    if (nodes.length === 1) return nodes[0];

    const first = nodes[0];
    const result: ASTNode = { type: first.type };

    // Check if all nodes have same type
    if (!nodes.every(n => n.type === first.type)) {
      return { type: 'Hole', isHole: true, holeId: `H${Date.now()}` };
    }

    // Anti-unify values
    if (first.value !== undefined) {
      const allSame = nodes.every(n => n.value === first.value);
      if (allSame) {
        result.value = first.value;
      } else {
        result.isHole = true;
        result.holeId = `V${Date.now()}`;
      }
    }

    // Anti-unify children
    if (first.children) {
      const minChildren = Math.min(...nodes.map(n => n.children?.length ?? 0));
      result.children = [];

      for (let i = 0; i < minChildren; i++) {
        const childNodes = nodes
          .map(n => n.children?.[i])
          .filter((c): c is ASTNode => c !== undefined);
        const unifiedChild = this.antiUnify(childNodes);
        if (unifiedChild) {
          result.children.push(unifiedChild);
        }
      }
    }

    return result;
  }

  /**
   * Detect common design pattern usage in AST
   */
  private detectDesignPatternUsage(ast: ASTNode): PatternCandidate[] {
    const patterns: PatternCandidate[] = [];
    const children = ast.children ?? [];

    // Repository pattern detection
    const repoIndicators = children.filter(c =>
      String(c.value).includes('Repository') ||
      String(c.value).includes('findBy') ||
      String(c.value).includes('save(')
    );
    if (repoIndicators.length >= 2) {
      patterns.push({
        name: 'RepositoryPattern',
        structure: { type: 'design-pattern', indicators: repoIndicators.length },
        occurrences: repoIndicators.length,
        confidence: 0.8,
        source: 'code',
      });
    }

    // Factory pattern detection
    const factoryIndicators = children.filter(c =>
      String(c.value).includes('create') ||
      String(c.value).includes('Factory') ||
      String(c.value).includes('build(')
    );
    if (factoryIndicators.length >= 2) {
      patterns.push({
        name: 'FactoryPattern',
        structure: { type: 'design-pattern', indicators: factoryIndicators.length },
        occurrences: factoryIndicators.length,
        confidence: 0.75,
        source: 'code',
      });
    }

    // Service layer detection
    const serviceIndicators = children.filter(c =>
      String(c.value).includes('Service') ||
      String(c.value).includes('execute') ||
      String(c.value).includes('process(')
    );
    if (serviceIndicators.length >= 2) {
      patterns.push({
        name: 'ServiceLayer',
        structure: { type: 'design-pattern', indicators: serviceIndicators.length },
        occurrences: serviceIndicators.length,
        confidence: 0.7,
        source: 'code',
      });
    }

    return patterns;
  }

  /**
   * Generate pattern name from abstracted AST
   */
  private generatePatternName(ast: ASTNode): string {
    const typeMap: Record<string, string> = {
      FunctionDeclaration: 'Function',
      ClassDeclaration: 'Class',
      InterfaceDeclaration: 'Interface',
      CallExpression: 'Call',
      ImportDeclaration: 'Import',
    };

    const base = typeMap[ast.type] ?? ast.type;
    const childCount = ast.children?.length ?? 0;
    return `${base}Pattern_${childCount}`;
  }

  /**
   * Calculate confidence for pattern
   */
  private calculatePatternConfidence(ast: ASTNode, occurrences: ASTNode[]): number {
    const baseConfidence = 0.5;
    const occurrenceBonus = Math.min(occurrences.length * 0.1, 0.3);
    const sizeBonus = ast.children ? Math.min(ast.children.length * 0.05, 0.2) : 0;

    return Math.min(baseConfidence + occurrenceBonus + sizeBonus, 1.0);
  }

  /**
   * Calculate overall confidence from patterns
   */
  private calculateConfidence(patterns: PatternCandidate[]): number {
    if (patterns.length === 0) return 0;
    const avgConfidence = patterns.reduce((sum, p) => sum + p.confidence, 0) / patterns.length;
    return Math.round(avgConfidence * 100) / 100;
  }

  /**
   * Get accumulated results
   */
  getResults(): WakeResult[] {
    return [...this.results];
  }

  /**
   * Get cached patterns for a task
   */
  getCachedPatterns(taskId: string): PatternCandidate[] {
    return this.patternCache.get(taskId) ?? [];
  }

  /**
   * Get all cached patterns
   */
  getAllCachedPatterns(): Map<string, PatternCandidate[]> {
    return new Map(this.patternCache);
  }

  /**
   * Get task count
   */
  get taskCount(): number {
    return this.tasks.length;
  }

  /**
   * Clear all state
   */
  reset(): void {
    this.tasks = [];
    this.results = [];
    this.patternCache.clear();
  }
}
