/**
 * Pattern Auto Extractor
 *
 * Automatically extracts patterns from generated code for learning
 *
 * @packageDocumentation
 * @module cli/generators/pattern-extractor
 *
 * @traceability REQ-PTN-001, REQ-PTN-002
 * @see DES-PTN-001 - Pattern Auto Extractor Design
 */

/**
 * Extracted pattern from code
 */
export interface ExtractedPattern {
  /** Pattern ID */
  id: string;

  /** Pattern name */
  name: string;

  /** Pattern category */
  category: 'value-object' | 'status-machine' | 'entity' | 'repository' | 'service' | 'other';

  /** Code template */
  template: string;

  /** Extraction metadata */
  metadata: {
    /** Source file */
    sourceFile: string;

    /** Extraction timestamp */
    extractedAt: string;

    /** Domain */
    domain: string;

    /** Confidence score (0-1) */
    confidence: number;
  };

  /** Variables in template */
  variables: PatternVariable[];

  /** Usage examples */
  examples: string[];
}

/**
 * Variable in pattern template
 */
export interface PatternVariable {
  /** Variable name */
  name: string;

  /** Variable type */
  type: 'string' | 'array' | 'object' | 'number' | 'boolean';

  /** Description */
  description?: string;

  /** Default value */
  defaultValue?: unknown;

  /** Required flag */
  required: boolean;
}

/**
 * Pattern extraction result
 */
export interface ExtractionResult {
  /** Extracted patterns */
  patterns: ExtractedPattern[];

  /** Extraction statistics */
  stats: {
    totalFiles: number;
    patternsFound: number;
    byCategory: Record<string, number>;
  };

  /** Extraction errors */
  errors: string[];
}

/**
 * Pattern extractor configuration
 */
export interface PatternExtractorConfig {
  /** Minimum confidence threshold */
  minConfidence?: number;

  /** Categories to extract */
  categories?: ExtractedPattern['category'][];

  /** Include private patterns */
  includePrivate?: boolean;
}

/**
 * Pattern Auto Extractor
 *
 * Analyzes generated code and extracts reusable patterns
 */
export class PatternAutoExtractor {
  private patterns: ExtractedPattern[] = [];
  private errors: string[] = [];
  private patternCounter = 0;

  constructor(private config: PatternExtractorConfig = {}) {
    this.config = {
      minConfidence: 0.7,
      categories: ['value-object', 'status-machine', 'entity', 'repository', 'service'],
      includePrivate: false,
      ...config,
    };
  }

  /**
   * Extract patterns from code content
   */
  extractFromCode(code: string, sourceFile: string, domain: string): ExtractedPattern[] {
    const extracted: ExtractedPattern[] = [];

    try {
      // Extract Value Object patterns
      const voPatterns = this.extractValueObjectPatterns(code, sourceFile, domain);
      extracted.push(...voPatterns);

      // Extract Status Machine patterns
      const smPatterns = this.extractStatusMachinePatterns(code, sourceFile, domain);
      extracted.push(...smPatterns);

      // Extract Entity patterns
      const entityPatterns = this.extractEntityPatterns(code, sourceFile, domain);
      extracted.push(...entityPatterns);

      // Extract Repository patterns
      const repoPatterns = this.extractRepositoryPatterns(code, sourceFile, domain);
      extracted.push(...repoPatterns);

      // Extract Service patterns
      const servicePatterns = this.extractServicePatterns(code, sourceFile, domain);
      extracted.push(...servicePatterns);

      // Filter by confidence
      const filtered = extracted.filter(
        (p) => p.metadata.confidence >= (this.config.minConfidence ?? 0.7)
      );

      this.patterns.push(...filtered);
      return filtered;
    } catch (error) {
      this.errors.push(`Failed to extract from ${sourceFile}: ${(error as Error).message}`);
      return [];
    }
  }

  /**
   * Extract Value Object patterns
   */
  private extractValueObjectPatterns(
    code: string,
    sourceFile: string,
    domain: string
  ): ExtractedPattern[] {
    const patterns: ExtractedPattern[] = [];

    // Match interface + factory function pattern
    const interfaceMatch = code.match(/export\s+interface\s+(\w+)\s*\{([^}]+)\}/);
    const factoryMatch = code.match(/export\s+function\s+create(\w+)\s*\([^)]*\)[^{]*\{/);

    if (interfaceMatch && factoryMatch) {
      const interfaceName = interfaceMatch[1];
      const factoryName = factoryMatch[1];

      if (interfaceName === factoryName) {
        const fields = this.parseInterfaceFields(interfaceMatch[2]);

        patterns.push({
          id: this.generatePatternId('VO'),
          name: `${interfaceName}ValueObject`,
          category: 'value-object',
          template: this.generateVOTemplate(interfaceName, fields),
          metadata: {
            sourceFile,
            extractedAt: new Date().toISOString(),
            domain,
            confidence: 0.9,
          },
          variables: [
            { name: 'name', type: 'string', required: true, description: 'Value Object name' },
            { name: 'fields', type: 'array', required: false, description: 'Field definitions' },
          ],
          examples: [code.substring(0, 500)],
        });
      }
    }

    return patterns;
  }

  /**
   * Extract Status Machine patterns
   */
  private extractStatusMachinePatterns(
    code: string,
    sourceFile: string,
    domain: string
  ): ExtractedPattern[] {
    const patterns: ExtractedPattern[] = [];

    // Match status type + transitions pattern
    const typeMatch = code.match(/export\s+type\s+(\w+)Status\s*=\s*([^;]+);/);
    const transitionsMatch = code.match(/valid(\w+)Transitions\s*:\s*Record<[^>]+>\s*=\s*\{([^}]+)\}/);

    if (typeMatch && transitionsMatch) {
      const entityName = typeMatch[1];
      const statusValues = this.parseUnionType(typeMatch[2]);

      patterns.push({
        id: this.generatePatternId('SM'),
        name: `${entityName}StatusMachine`,
        category: 'status-machine',
        template: this.generateSMTemplate(entityName, statusValues),
        metadata: {
          sourceFile,
          extractedAt: new Date().toISOString(),
          domain,
          confidence: 0.85,
        },
        variables: [
          { name: 'entityName', type: 'string', required: true, description: 'Entity name' },
          { name: 'statuses', type: 'array', required: false, description: 'Status values' },
          { name: 'transitions', type: 'object', required: false, description: 'Transition map' },
        ],
        examples: [code.substring(0, 500)],
      });
    }

    return patterns;
  }

  /**
   * Extract Entity patterns
   */
  private extractEntityPatterns(
    code: string,
    sourceFile: string,
    domain: string
  ): ExtractedPattern[] {
    const patterns: ExtractedPattern[] = [];

    // Match entity interface with id field
    const entityMatch = code.match(/export\s+interface\s+(\w+)\s*\{[^}]*\bid\s*:\s*\w+[^}]*\}/);

    if (entityMatch && !code.includes('ValueObject') && !code.includes('Status')) {
      const entityName = entityMatch[1];

      patterns.push({
        id: this.generatePatternId('ENT'),
        name: `${entityName}Entity`,
        category: 'entity',
        template: `// Entity: {{name}}\nexport interface {{name}} {\n  readonly id: {{name}}Id;\n  // fields\n}`,
        metadata: {
          sourceFile,
          extractedAt: new Date().toISOString(),
          domain,
          confidence: 0.75,
        },
        variables: [
          { name: 'name', type: 'string', required: true, description: 'Entity name' },
        ],
        examples: [entityMatch[0]],
      });
    }

    return patterns;
  }

  /**
   * Extract Repository patterns
   */
  private extractRepositoryPatterns(
    code: string,
    sourceFile: string,
    domain: string
  ): ExtractedPattern[] {
    const patterns: ExtractedPattern[] = [];

    // Match repository interface
    const repoMatch = code.match(/export\s+interface\s+(\w+)Repository\s*\{([^}]+)\}/);

    if (repoMatch) {
      const entityName = repoMatch[1];
      const methods = this.parseRepositoryMethods(repoMatch[2]);

      patterns.push({
        id: this.generatePatternId('REPO'),
        name: `${entityName}Repository`,
        category: 'repository',
        template: this.generateRepoTemplate(entityName, methods),
        metadata: {
          sourceFile,
          extractedAt: new Date().toISOString(),
          domain,
          confidence: 0.8,
        },
        variables: [
          { name: 'entityName', type: 'string', required: true, description: 'Entity name' },
          { name: 'methods', type: 'array', required: false, description: 'Repository methods' },
        ],
        examples: [repoMatch[0]],
      });
    }

    return patterns;
  }

  /**
   * Extract Service patterns
   */
  private extractServicePatterns(
    code: string,
    sourceFile: string,
    domain: string
  ): ExtractedPattern[] {
    const patterns: ExtractedPattern[] = [];

    // Match service class
    const serviceMatch = code.match(/export\s+class\s+(\w+)Service\s*\{([^}]+)\}/);

    if (serviceMatch) {
      const serviceName = serviceMatch[1];

      patterns.push({
        id: this.generatePatternId('SVC'),
        name: `${serviceName}Service`,
        category: 'service',
        template: `// Service: {{name}}Service\nexport class {{name}}Service {\n  constructor(private repo: {{name}}Repository) {}\n}`,
        metadata: {
          sourceFile,
          extractedAt: new Date().toISOString(),
          domain,
          confidence: 0.75,
        },
        variables: [
          { name: 'name', type: 'string', required: true, description: 'Service name' },
        ],
        examples: [serviceMatch[0]],
      });
    }

    return patterns;
  }

  /**
   * Get extraction result
   */
  getResult(): ExtractionResult {
    const byCategory: Record<string, number> = {};

    for (const pattern of this.patterns) {
      byCategory[pattern.category] = (byCategory[pattern.category] || 0) + 1;
    }

    return {
      patterns: this.patterns,
      stats: {
        totalFiles: new Set(this.patterns.map((p) => p.metadata.sourceFile)).size,
        patternsFound: this.patterns.length,
        byCategory,
      },
      errors: this.errors,
    };
  }

  /**
   * Reset extractor state
   */
  reset(): void {
    this.patterns = [];
    this.errors = [];
  }

  /**
   * Generate pattern ID
   */
  private generatePatternId(prefix: string): string {
    this.patternCounter++;
    const date = new Date().toISOString().slice(0, 10).replace(/-/g, '');
    return `PTN-${prefix}-${date}-${String(this.patternCounter).padStart(3, '0')}`;
  }

  /**
   * Parse interface fields
   */
  private parseInterfaceFields(body: string): string[] {
    const fields: string[] = [];
    const lines = body.split('\n');

    for (const line of lines) {
      const match = line.match(/^\s*(?:readonly\s+)?(\w+)\s*:/);
      if (match) {
        fields.push(match[1]);
      }
    }

    return fields;
  }

  /**
   * Parse union type values
   */
  private parseUnionType(unionStr: string): string[] {
    return unionStr
      .split('|')
      .map((s) => s.trim().replace(/['"]/g, ''))
      .filter((s) => s.length > 0);
  }

  /**
   * Parse repository methods
   */
  private parseRepositoryMethods(body: string): string[] {
    const methods: string[] = [];
    const lines = body.split('\n');

    for (const line of lines) {
      const match = line.match(/^\s*(\w+)\s*\(/);
      if (match) {
        methods.push(match[1]);
      }
    }

    return methods;
  }

  /**
   * Generate Value Object template
   */
  private generateVOTemplate(_name: string, fields: string[]): string {
    const fieldDefs = fields.map((f) => `  readonly ${f}: unknown;`).join('\n');
    return `export interface {{name}} {\n${fieldDefs}\n}\n\nexport function create{{name}}(input: {{name}}Input): Result<{{name}}, ValidationError> {\n  // validation\n  return ok({ ...input });\n}`;
  }

  /**
   * Generate Status Machine template
   */
  private generateSMTemplate(_entityName: string, statuses: string[]): string {
    const statusUnion = statuses.map((s) => `'${s}'`).join(' | ');
    return `export type {{entityName}}Status = ${statusUnion};\n\nexport const valid{{entityName}}Transitions: Record<{{entityName}}Status, {{entityName}}Status[]> = {\n  // transitions\n};`;
  }

  /**
   * Generate Repository template
   */
  private generateRepoTemplate(_entityName: string, methods: string[]): string {
    const methodDefs = methods.map((m) => `  ${m}(): Promise<unknown>;`).join('\n');
    return `export interface {{entityName}}Repository {\n${methodDefs}\n}`;
  }
}

/**
 * Create a new pattern extractor
 */
export function createPatternExtractor(config?: PatternExtractorConfig): PatternAutoExtractor {
  return new PatternAutoExtractor(config);
}
