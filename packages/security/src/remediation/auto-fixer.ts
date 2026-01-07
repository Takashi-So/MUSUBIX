/**
 * @fileoverview Auto-Fixer for Security Vulnerabilities
 * @module @nahisaho/musubix-security/remediation/auto-fixer
 * 
 * Provides automated fix generation and application for detected vulnerabilities.
 */

import type { Vulnerability, Fix, CodeEdit, FixStrategy } from '../types/index.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Fix template for a vulnerability type
 */
export interface FixTemplate {
  /** Template ID */
  id: string;
  /** Vulnerability types this template applies to */
  vulnerabilityTypes: string[];
  /** Rule patterns to match */
  rulePatterns: string[];
  /** Fix strategy */
  strategy: FixStrategy;
  /** Template code transformations */
  transformations: CodeTransformation[];
  /** Required imports */
  imports: ImportSpec[];
  /** Confidence score for this template */
  confidence: number;
  /** Whether fix might break functionality */
  breakingChange: boolean;
  /** Description */
  description: string;
}

/**
 * Code transformation specification
 */
export interface CodeTransformation {
  /** Transformation type */
  type: 'replace' | 'wrap' | 'insert_before' | 'insert_after' | 'delete';
  /** Pattern to match (regex) */
  pattern?: string;
  /** Replacement template (can use $1, $2 etc for captured groups) */
  replacement?: string;
  /** Wrapper template (for wrap type) */
  wrapper?: { before: string; after: string };
  /** Content to insert */
  content?: string;
}

/**
 * Import specification
 */
export interface ImportSpec {
  /** Module name */
  module: string;
  /** Named imports */
  namedImports?: string[];
  /** Default import name */
  defaultImport?: string;
  /** Is type import */
  isTypeOnly?: boolean;
}

/**
 * Fix application result
 */
export interface FixApplicationResult {
  /** Whether fix was applied */
  applied: boolean;
  /** Fix that was applied */
  fix: Fix;
  /** Files modified */
  modifiedFiles: string[];
  /** Backup created */
  backupPath?: string;
  /** Error if failed */
  error?: string;
  /** Warnings */
  warnings: string[];
}

/**
 * Fix generation options
 */
export interface FixGenerationOptions {
  /** Maximum fixes to generate per vulnerability */
  maxFixes?: number;
  /** Minimum confidence threshold */
  minConfidence?: number;
  /** Include breaking changes */
  includeBreakingChanges?: boolean;
  /** Preferred strategies */
  preferredStrategies?: FixStrategy[];
  /** Custom templates */
  customTemplates?: FixTemplate[];
}

/**
 * Auto-fixer options
 */
export interface AutoFixerOptions {
  /** Create backups before applying fixes */
  createBackups?: boolean;
  /** Backup directory */
  backupDir?: string;
  /** Dry run mode (don't actually modify files) */
  dryRun?: boolean;
  /** Validate fixes after applying */
  validateAfterApply?: boolean;
  /** Custom fix templates */
  templates?: FixTemplate[];
}

// ============================================================================
// Built-in Fix Templates
// ============================================================================

const XSS_FIX_TEMPLATES: FixTemplate[] = [
  {
    id: 'xss-sanitize-html',
    vulnerabilityTypes: ['xss'],
    rulePatterns: ['xss', 'cross-site-scripting'],
    strategy: 'sanitization',
    transformations: [
      {
        type: 'wrap',
        pattern: '(\\w+)',
        wrapper: { before: 'sanitizeHtml(', after: ')' },
      },
    ],
    imports: [{ module: 'dompurify', defaultImport: 'DOMPurify' }],
    confidence: 0.85,
    breakingChange: false,
    description: 'Sanitize HTML output using DOMPurify',
  },
  {
    id: 'xss-encode-output',
    vulnerabilityTypes: ['xss'],
    rulePatterns: ['xss', 'cross-site-scripting'],
    strategy: 'encoding',
    transformations: [
      {
        type: 'wrap',
        pattern: '(\\w+)',
        wrapper: { before: 'encodeHtml(', after: ')' },
      },
    ],
    imports: [{ module: 'he', namedImports: ['encode as encodeHtml'] }],
    confidence: 0.9,
    breakingChange: false,
    description: 'HTML encode output to prevent XSS',
  },
];

const SQL_INJECTION_FIX_TEMPLATES: FixTemplate[] = [
  {
    id: 'sqli-parameterized',
    vulnerabilityTypes: ['sql_injection'],
    rulePatterns: ['sql-injection', 'sqli'],
    strategy: 'parameterization',
    transformations: [
      {
        type: 'replace',
        pattern: '`([^`]*\\$\\{([^}]+)\\}[^`]*)`',
        replacement: "'$1', [$2]",
      },
    ],
    imports: [],
    confidence: 0.9,
    breakingChange: true,
    description: 'Use parameterized queries instead of string concatenation',
  },
  {
    id: 'sqli-prepared-statement',
    vulnerabilityTypes: ['sql_injection'],
    rulePatterns: ['sql-injection', 'sqli'],
    strategy: 'parameterization',
    transformations: [
      {
        type: 'replace',
        pattern: 'query\\(`([^`]*)`\\)',
        replacement: 'prepare($1).execute()',
      },
    ],
    imports: [],
    confidence: 0.85,
    breakingChange: true,
    description: 'Use prepared statements',
  },
];

const PATH_TRAVERSAL_FIX_TEMPLATES: FixTemplate[] = [
  {
    id: 'path-traversal-normalize',
    vulnerabilityTypes: ['path_traversal'],
    rulePatterns: ['path-traversal', 'directory-traversal'],
    strategy: 'validation',
    transformations: [
      {
        type: 'wrap',
        pattern: '(\\w+)',
        wrapper: { before: 'path.normalize(path.resolve(baseDir, ', after: '))' },
      },
    ],
    imports: [{ module: 'path', namedImports: ['normalize', 'resolve'] }],
    confidence: 0.85,
    breakingChange: false,
    description: 'Normalize and resolve path to prevent traversal',
  },
];

const SECRET_FIX_TEMPLATES: FixTemplate[] = [
  {
    id: 'secret-env-var',
    vulnerabilityTypes: ['hardcoded_secret', 'exposed_credential'],
    rulePatterns: ['hardcoded', 'secret', 'credential', 'api-key'],
    strategy: 'configuration',
    transformations: [
      {
        type: 'replace',
        pattern: '["\']([A-Za-z0-9+/=]{20,})["\']',
        replacement: 'process.env.SECRET_KEY',
      },
    ],
    imports: [],
    confidence: 0.8,
    breakingChange: true,
    description: 'Move secret to environment variable',
  },
];

const CRYPTO_FIX_TEMPLATES: FixTemplate[] = [
  {
    id: 'crypto-weak-hash',
    vulnerabilityTypes: ['weak_cryptography'],
    rulePatterns: ['weak-hash', 'md5', 'sha1'],
    strategy: 'replacement',
    transformations: [
      {
        type: 'replace',
        pattern: "createHash\\(['\"]md5['\"]\\)",
        replacement: "createHash('sha256')",
      },
      {
        type: 'replace',
        pattern: "createHash\\(['\"]sha1['\"]\\)",
        replacement: "createHash('sha256')",
      },
    ],
    imports: [],
    confidence: 0.95,
    breakingChange: false,
    description: 'Replace weak hash algorithm with SHA-256',
  },
  {
    id: 'crypto-weak-random',
    vulnerabilityTypes: ['weak_cryptography'],
    rulePatterns: ['weak-random', 'math-random'],
    strategy: 'replacement',
    transformations: [
      {
        type: 'replace',
        pattern: 'Math\\.random\\(\\)',
        replacement: 'crypto.randomUUID()',
      },
    ],
    imports: [{ module: 'crypto', namedImports: ['randomUUID'] }],
    confidence: 0.9,
    breakingChange: true,
    description: 'Replace Math.random with cryptographically secure random',
  },
];

const ALL_FIX_TEMPLATES: FixTemplate[] = [
  ...XSS_FIX_TEMPLATES,
  ...SQL_INJECTION_FIX_TEMPLATES,
  ...PATH_TRAVERSAL_FIX_TEMPLATES,
  ...SECRET_FIX_TEMPLATES,
  ...CRYPTO_FIX_TEMPLATES,
];

// ============================================================================
// AutoFixer Class
// ============================================================================

/**
 * AutoFixer for generating and applying security fixes
 * 
 * @example
 * ```typescript
 * const fixer = createAutoFixer({ dryRun: true });
 * const fixes = fixer.generateFixes(vulnerability);
 * const result = await fixer.applyFix(fixes[0], fileContent);
 * ```
 */
export class AutoFixer {
  private templates: FixTemplate[];
  private options: Required<AutoFixerOptions>;

  constructor(options: AutoFixerOptions = {}) {
    this.options = {
      createBackups: options.createBackups ?? true,
      backupDir: options.backupDir ?? '.musubix-backups',
      dryRun: options.dryRun ?? false,
      validateAfterApply: options.validateAfterApply ?? true,
      templates: options.templates ?? [],
    };
    this.templates = [...ALL_FIX_TEMPLATES, ...this.options.templates];
  }

  /**
   * Generate fixes for a vulnerability
   */
  generateFixes(
    vulnerability: Vulnerability,
    options: FixGenerationOptions = {}
  ): Fix[] {
    const {
      maxFixes = 3,
      minConfidence = 0.7,
      includeBreakingChanges = false,
      preferredStrategies = [],
      customTemplates = [],
    } = options;

    const allTemplates = [...this.templates, ...customTemplates];
    const matchingTemplates = this.findMatchingTemplates(
      vulnerability,
      allTemplates,
      minConfidence,
      includeBreakingChanges
    );

    // Sort by preference and confidence
    const sorted = this.sortTemplates(matchingTemplates, preferredStrategies);

    // Generate fixes from templates
    const fixes: Fix[] = [];
    for (const template of sorted.slice(0, maxFixes)) {
      const fix = this.generateFixFromTemplate(vulnerability, template);
      if (fix) {
        fixes.push(fix);
      }
    }

    return fixes;
  }

  /**
   * Generate fix for multiple vulnerabilities
   */
  generateBatchFixes(
    vulnerabilities: Vulnerability[],
    options: FixGenerationOptions = {}
  ): Map<string, Fix[]> {
    const result = new Map<string, Fix[]>();

    for (const vuln of vulnerabilities) {
      const fixes = this.generateFixes(vuln, options);
      result.set(vuln.id, fixes);
    }

    return result;
  }

  /**
   * Apply a fix to file content
   */
  applyFix(fix: Fix, fileContent: string): FixApplicationResult {
    const warnings: string[] = [];
    let modifiedContent = fileContent;
    const modifiedFiles: string[] = [];

    try {
      // Apply each edit
      for (const edit of fix.edits) {
        const result = this.applyEdit(modifiedContent, edit);
        modifiedContent = result.content;
        if (result.warning) {
          warnings.push(result.warning);
        }
      }

      // Add imports if needed
      if (fix.imports && fix.imports.length > 0) {
        modifiedContent = this.addImports(modifiedContent, fix.imports);
      }

      if (fix.edits.length > 0) {
        modifiedFiles.push(fix.edits[0].location.file);
      }

      return {
        applied: true,
        fix,
        modifiedFiles,
        warnings,
      };
    } catch (error) {
      return {
        applied: false,
        fix,
        modifiedFiles: [],
        error: error instanceof Error ? error.message : 'Unknown error',
        warnings,
      };
    }
  }

  /**
   * Get available fix strategies for a vulnerability type
   */
  getAvailableStrategies(vulnerabilityType: string): FixStrategy[] {
    const strategies = new Set<FixStrategy>();

    for (const template of this.templates) {
      if (template.vulnerabilityTypes.includes(vulnerabilityType)) {
        strategies.add(template.strategy);
      }
    }

    return Array.from(strategies);
  }

  /**
   * Get fix template by ID
   */
  getTemplate(templateId: string): FixTemplate | undefined {
    return this.templates.find(t => t.id === templateId);
  }

  /**
   * Register custom fix template
   */
  registerTemplate(template: FixTemplate): void {
    this.templates.push(template);
  }

  /**
   * Validate a fix before applying
   */
  validateFix(fix: Fix): { valid: boolean; errors: string[] } {
    const errors: string[] = [];

    if (!fix.id) {
      errors.push('Fix must have an ID');
    }

    if (!fix.vulnerabilityId) {
      errors.push('Fix must reference a vulnerability');
    }

    if (!fix.edits || fix.edits.length === 0) {
      errors.push('Fix must have at least one edit');
    }

    for (const edit of fix.edits) {
      if (!edit.location) {
        errors.push('Edit must have a location');
      }
      if (edit.newCode === undefined) {
        errors.push('Edit must have newCode');
      }
    }

    return { valid: errors.length === 0, errors };
  }

  /**
   * Preview fix without applying
   */
  previewFix(fix: Fix, fileContent: string): string {
    const result = this.applyFix(fix, fileContent);
    if (!result.applied) {
      return fileContent;
    }

    // Generate diff preview
    const lines = fileContent.split('\n');
    const newLines = this.getModifiedContent(fix, fileContent).split('\n');
    
    const preview: string[] = [];
    preview.push('=== Fix Preview ===');
    preview.push(`Fix: ${fix.title}`);
    preview.push(`Strategy: ${fix.strategy}`);
    preview.push(`Confidence: ${(fix.confidence * 100).toFixed(0)}%`);
    preview.push('');
    preview.push('Changes:');

    for (const edit of fix.edits) {
      const line = edit.location.startLine;
      preview.push(`  Line ${line}:`);
      preview.push(`    - ${lines[line - 1] || ''}`);
      preview.push(`    + ${newLines[line - 1] || ''}`);
    }

    return preview.join('\n');
  }

  // ============================================================================
  // Private Methods
  // ============================================================================

  private findMatchingTemplates(
    vulnerability: Vulnerability,
    templates: FixTemplate[],
    minConfidence: number,
    includeBreaking: boolean
  ): FixTemplate[] {
    return templates.filter(template => {
      // Check vulnerability type match
      const typeMatch = template.vulnerabilityTypes.includes(vulnerability.type);
      
      // Check rule pattern match
      const ruleMatch = template.rulePatterns.some(pattern =>
        vulnerability.ruleId.toLowerCase().includes(pattern.toLowerCase())
      );

      // Check confidence
      const confidenceOk = template.confidence >= minConfidence;

      // Check breaking change
      const breakingOk = includeBreaking || !template.breakingChange;

      return (typeMatch || ruleMatch) && confidenceOk && breakingOk;
    });
  }

  private sortTemplates(
    templates: FixTemplate[],
    preferredStrategies: FixStrategy[]
  ): FixTemplate[] {
    return [...templates].sort((a, b) => {
      // Prefer specified strategies
      const aPreferred = preferredStrategies.indexOf(a.strategy);
      const bPreferred = preferredStrategies.indexOf(b.strategy);
      
      if (aPreferred !== -1 && bPreferred === -1) return -1;
      if (bPreferred !== -1 && aPreferred === -1) return 1;
      if (aPreferred !== -1 && bPreferred !== -1) return aPreferred - bPreferred;

      // Then by confidence
      return b.confidence - a.confidence;
    });
  }

  private generateFixFromTemplate(
    vulnerability: Vulnerability,
    template: FixTemplate
  ): Fix | null {
    const edits: CodeEdit[] = [];

    for (const transform of template.transformations) {
      const edit = this.createEditFromTransformation(vulnerability, transform);
      if (edit) {
        edits.push(edit);
      }
    }

    if (edits.length === 0) {
      return null;
    }

    return {
      id: `FIX-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
      vulnerabilityId: vulnerability.id,
      strategy: template.strategy,
      title: template.description,
      description: template.description,
      confidence: template.confidence,
      breakingChange: template.breakingChange,
      rationale: `Applied fix template: ${template.id}`,
      edits,
      imports: template.imports.map(imp => ({
        module: imp.module,
        namedImports: imp.namedImports,
        defaultImport: imp.defaultImport,
        isTypeOnly: imp.isTypeOnly,
        insertLine: 0, // Default to top of file
      })),
      generatedAt: new Date(),
    };
  }

  private createEditFromTransformation(
    vulnerability: Vulnerability,
    transform: CodeTransformation
  ): CodeEdit | null {
    const location = vulnerability.location;

    switch (transform.type) {
      case 'replace':
        return {
          location,
          originalCode: vulnerability.codeSnippet || '',
          newCode: this.applyReplacement(
            vulnerability.codeSnippet || '',
            transform.pattern || '',
            transform.replacement || ''
          ),
          description: 'Replace vulnerable code',
        };

      case 'wrap':
        if (!transform.wrapper) return null;
        return {
          location,
          originalCode: vulnerability.codeSnippet || '',
          newCode: `${transform.wrapper.before}${vulnerability.codeSnippet || ''}${transform.wrapper.after}`,
          description: 'Wrap vulnerable code',
        };

      case 'insert_before':
        return {
          location: { ...location, endLine: location.startLine },
          originalCode: '',
          newCode: transform.content || '',
          description: 'Insert code before vulnerability',
        };

      case 'insert_after':
        return {
          location: { ...location, startLine: location.endLine },
          originalCode: '',
          newCode: transform.content || '',
          description: 'Insert code after vulnerability',
        };

      case 'delete':
        return {
          location,
          originalCode: vulnerability.codeSnippet || '',
          newCode: '',
          description: 'Delete vulnerable code',
        };

      default:
        return null;
    }
  }

  private applyReplacement(code: string, pattern: string, replacement: string): string {
    try {
      const regex = new RegExp(pattern, 'g');
      return code.replace(regex, replacement);
    } catch {
      return code;
    }
  }

  private applyEdit(
    content: string,
    edit: CodeEdit
  ): { content: string; warning?: string } {
    const lines = content.split('\n');
    const { startLine, endLine } = edit.location;

    if (startLine < 1 || startLine > lines.length) {
      return { content, warning: `Invalid line number: ${startLine}` };
    }

    // Replace lines
    const newLines = edit.newCode.split('\n');
    lines.splice(startLine - 1, endLine - startLine + 1, ...newLines);

    return { content: lines.join('\n') };
  }

  private addImports(content: string, imports: Fix['imports']): string {
    if (!imports || imports.length === 0) {
      return content;
    }

    const importStatements: string[] = [];

    for (const imp of imports) {
      let statement = '';
      const typePrefix = imp.isTypeOnly ? 'type ' : '';

      if (imp.defaultImport && imp.namedImports?.length) {
        statement = `import ${typePrefix}${imp.defaultImport}, { ${imp.namedImports.join(', ')} } from '${imp.module}';`;
      } else if (imp.defaultImport) {
        statement = `import ${typePrefix}${imp.defaultImport} from '${imp.module}';`;
      } else if (imp.namedImports?.length) {
        statement = `import ${typePrefix}{ ${imp.namedImports.join(', ')} } from '${imp.module}';`;
      }

      if (statement && !content.includes(statement)) {
        importStatements.push(statement);
      }
    }

    if (importStatements.length === 0) {
      return content;
    }

    // Find the last import statement and add after it
    const lines = content.split('\n');
    let lastImportIndex = -1;

    for (let i = 0; i < lines.length; i++) {
      if (lines[i].startsWith('import ')) {
        lastImportIndex = i;
      }
    }

    if (lastImportIndex >= 0) {
      lines.splice(lastImportIndex + 1, 0, ...importStatements);
    } else {
      lines.unshift(...importStatements, '');
    }

    return lines.join('\n');
  }

  private getModifiedContent(fix: Fix, originalContent: string): string {
    let content = originalContent;

    for (const edit of fix.edits) {
      const result = this.applyEdit(content, edit);
      content = result.content;
    }

    if (fix.imports && fix.imports.length > 0) {
      content = this.addImports(content, fix.imports);
    }

    return content;
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create an auto-fixer instance
 */
export function createAutoFixer(options?: AutoFixerOptions): AutoFixer {
  return new AutoFixer(options);
}

/**
 * Get all built-in fix templates
 */
export function getBuiltInTemplates(): FixTemplate[] {
  return [...ALL_FIX_TEMPLATES];
}

/**
 * Create a custom fix template
 */
export function createFixTemplate(
  config: Omit<FixTemplate, 'id'>
): FixTemplate {
  return {
    ...config,
    id: `custom-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
  };
}
