/**
 * @fileoverview Secure Code Transformer
 * @module @nahisaho/musubix-security/remediation/secure-code-transformer
 * 
 * Transforms insecure code patterns into secure alternatives using
 * AST-based transformations and secure coding patterns.
 */

import type { SourceLocation, Vulnerability } from '../types/index.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Code transformation
 */
export interface CodeTransformation {
  /** Transformation ID */
  id: string;
  /** Transformation name */
  name: string;
  /** Category */
  category: TransformationCategory;
  /** Pattern to match */
  pattern: CodePattern;
  /** Replacement pattern */
  replacement: ReplacementPattern;
  /** Description */
  description: string;
  /** Risk level */
  riskLevel: 'safe' | 'caution' | 'review-required';
  /** Applicable languages */
  languages: string[];
  /** Required imports */
  imports?: ImportSpec[];
}

/**
 * Transformation category
 */
export type TransformationCategory = 
  | 'input-validation'
  | 'output-encoding'
  | 'authentication'
  | 'authorization'
  | 'cryptography'
  | 'data-protection'
  | 'error-handling'
  | 'logging'
  | 'session-management'
  | 'general';

/**
 * Code pattern
 */
export interface CodePattern {
  /** Pattern type */
  type: 'regex' | 'ast' | 'function-call' | 'api-usage';
  /** Pattern value */
  value: string;
  /** Flags (for regex) */
  flags?: string;
  /** Context requirements */
  context?: PatternContext;
}

/**
 * Pattern context
 */
export interface PatternContext {
  /** Must be inside function */
  insideFunction?: boolean;
  /** Must be inside class */
  insideClass?: boolean;
  /** Must have specific imports */
  hasImports?: string[];
  /** File extension */
  fileExtension?: string[];
}

/**
 * Replacement pattern
 */
export interface ReplacementPattern {
  /** Replacement type */
  type: 'template' | 'function' | 'snippet';
  /** Template/snippet value */
  value: string;
  /** Capture group mappings */
  captures?: Record<string, string>;
  /** Wrap existing code */
  wrapExisting?: boolean;
}

/**
 * Import specification
 */
export interface ImportSpec {
  /** Module name */
  module: string;
  /** Named imports */
  named?: string[];
  /** Default import */
  default?: string;
  /** Is type import */
  typeOnly?: boolean;
}

/**
 * Transformation result
 */
export interface TransformationResult {
  /** Whether transformation succeeded */
  success: boolean;
  /** Original code */
  originalCode: string;
  /** Transformed code */
  transformedCode: string;
  /** Applied transformations */
  transformationsApplied: AppliedTransformation[];
  /** Warnings */
  warnings: string[];
  /** Errors */
  errors: string[];
  /** Required imports */
  requiredImports: ImportSpec[];
}

/**
 * Applied transformation
 */
export interface AppliedTransformation {
  /** Transformation ID */
  transformationId: string;
  /** Location in code */
  location: SourceLocation;
  /** Original code snippet */
  original: string;
  /** Replacement code */
  replacement: string;
}

/**
 * Transformer options
 */
export interface SecureCodeTransformerOptions {
  /** Custom transformations */
  customTransformations?: CodeTransformation[];
  /** Enable specific categories */
  enabledCategories?: TransformationCategory[];
  /** Target language */
  language?: string;
  /** Preserve formatting */
  preserveFormatting?: boolean;
  /** Dry run (preview only) */
  dryRun?: boolean;
}

/**
 * Transform options
 */
export interface TransformOptions {
  /** Only apply specific transformations */
  onlyTransformations?: string[];
  /** Exclude transformations */
  excludeTransformations?: string[];
  /** Target specific vulnerabilities */
  targetVulnerabilities?: Vulnerability[];
  /** Max transformations */
  maxTransformations?: number;
}

// ============================================================================
// Built-in Transformations
// ============================================================================

const BUILT_IN_TRANSFORMATIONS: CodeTransformation[] = [
  // Input Validation
  {
    id: 'transform-escape-html',
    name: 'Escape HTML Output',
    category: 'output-encoding',
    pattern: {
      type: 'regex',
      value: 'innerHTML\\s*=\\s*([^;]+)',
      flags: 'g',
    },
    replacement: {
      type: 'template',
      value: 'textContent = $1',
      captures: { '1': 'content' },
    },
    description: 'Replace innerHTML with textContent to prevent XSS',
    riskLevel: 'safe',
    languages: ['javascript', 'typescript'],
  },
  {
    id: 'transform-encode-uri',
    name: 'Encode URI Components',
    category: 'output-encoding',
    pattern: {
      type: 'regex',
      value: '(["\'])\\s*\\+\\s*(\\w+)\\s*\\+\\s*(["\'])',
      flags: 'g',
    },
    replacement: {
      type: 'template',
      value: '$1 + encodeURIComponent($2) + $3',
    },
    description: 'Encode user input in URL contexts',
    riskLevel: 'caution',
    languages: ['javascript', 'typescript'],
  },

  // SQL Injection
  {
    id: 'transform-parameterized-query',
    name: 'Use Parameterized Queries',
    category: 'input-validation',
    pattern: {
      type: 'regex',
      value: 'query\\(\\s*[`"\']SELECT\\s+.+\\$\\{([^}]+)\\}',
      flags: 'gi',
    },
    replacement: {
      type: 'template',
      value: 'query("SELECT ... WHERE column = $1", [$1])',
      wrapExisting: true,
    },
    description: 'Convert string interpolation to parameterized queries',
    riskLevel: 'review-required',
    languages: ['javascript', 'typescript'],
  },

  // Cryptography
  {
    id: 'transform-md5-to-sha256',
    name: 'Replace MD5 with SHA-256',
    category: 'cryptography',
    pattern: {
      type: 'function-call',
      value: "createHash('md5')",
    },
    replacement: {
      type: 'template',
      value: "createHash('sha256')",
    },
    description: 'Replace weak MD5 hash with SHA-256',
    riskLevel: 'safe',
    languages: ['javascript', 'typescript'],
  },
  {
    id: 'transform-sha1-to-sha256',
    name: 'Replace SHA-1 with SHA-256',
    category: 'cryptography',
    pattern: {
      type: 'function-call',
      value: "createHash('sha1')",
    },
    replacement: {
      type: 'template',
      value: "createHash('sha256')",
    },
    description: 'Replace weak SHA-1 hash with SHA-256',
    riskLevel: 'safe',
    languages: ['javascript', 'typescript'],
  },
  {
    id: 'transform-math-random',
    name: 'Replace Math.random with crypto',
    category: 'cryptography',
    pattern: {
      type: 'function-call',
      value: 'Math.random()',
    },
    replacement: {
      type: 'snippet',
      value: 'crypto.randomBytes(16).toString("hex")',
    },
    description: 'Replace insecure Math.random() with cryptographic random',
    riskLevel: 'caution',
    languages: ['javascript', 'typescript'],
    imports: [{ module: 'crypto', named: ['randomBytes'] }],
  },

  // Path Traversal
  {
    id: 'transform-path-normalize',
    name: 'Normalize File Paths',
    category: 'input-validation',
    pattern: {
      type: 'regex',
      value: 'readFile(?:Sync)?\\(\\s*([^,)]+)',
      flags: 'g',
    },
    replacement: {
      type: 'template',
      value: 'readFile(path.normalize(path.join(baseDir, path.basename($1)))',
    },
    description: 'Normalize paths to prevent traversal',
    riskLevel: 'review-required',
    languages: ['javascript', 'typescript'],
    imports: [{ module: 'path', default: 'path' }],
  },

  // Error Handling
  {
    id: 'transform-generic-error',
    name: 'Use Generic Error Messages',
    category: 'error-handling',
    pattern: {
      type: 'regex',
      value: 'res\\.send\\(err\\.message\\)',
      flags: 'g',
    },
    replacement: {
      type: 'template',
      value: 'res.send("An error occurred")',
    },
    description: 'Prevent error message information disclosure',
    riskLevel: 'safe',
    languages: ['javascript', 'typescript'],
  },
  {
    id: 'transform-error-stack',
    name: 'Remove Stack Traces from Responses',
    category: 'error-handling',
    pattern: {
      type: 'regex',
      value: 'res\\.(json|send)\\(.*err\\.stack.*\\)',
      flags: 'g',
    },
    replacement: {
      type: 'template',
      value: 'res.$1({ error: "Internal server error" })',
    },
    description: 'Prevent stack trace information disclosure',
    riskLevel: 'safe',
    languages: ['javascript', 'typescript'],
  },

  // Data Protection
  {
    id: 'transform-hardcoded-secret',
    name: 'Move Secrets to Environment Variables',
    category: 'data-protection',
    pattern: {
      type: 'regex',
      value: '(const|let|var)\\s+(\\w*(?:secret|key|password|token|api_key)\\w*)\\s*=\\s*["\']([^"\']+)["\']',
      flags: 'gi',
    },
    replacement: {
      type: 'template',
      value: '$1 $2 = process.env.$2 || ""',
      captures: { '2': 'varName' },
    },
    description: 'Move hardcoded secrets to environment variables',
    riskLevel: 'review-required',
    languages: ['javascript', 'typescript'],
  },

  // Session Management
  {
    id: 'transform-cookie-httponly',
    name: 'Add HttpOnly to Cookies',
    category: 'session-management',
    pattern: {
      type: 'regex',
      value: 'cookie\\(["\']([^"\']+)["\'],\\s*([^,)]+)\\)',
      flags: 'g',
    },
    replacement: {
      type: 'template',
      value: 'cookie("$1", $2, { httpOnly: true, secure: true })',
    },
    description: 'Add HttpOnly and Secure flags to cookies',
    riskLevel: 'safe',
    languages: ['javascript', 'typescript'],
  },

  // Logging
  {
    id: 'transform-sanitize-logs',
    name: 'Sanitize Sensitive Data in Logs',
    category: 'logging',
    pattern: {
      type: 'regex',
      value: 'console\\.log\\(.*(?:password|secret|token|key).*\\)',
      flags: 'gi',
    },
    replacement: {
      type: 'template',
      value: 'console.log("[REDACTED]")',
    },
    description: 'Remove sensitive data from log statements',
    riskLevel: 'review-required',
    languages: ['javascript', 'typescript'],
  },
];

// ============================================================================
// SecureCodeTransformer Class
// ============================================================================

/**
 * Transforms insecure code patterns to secure alternatives
 * 
 * @example
 * ```typescript
 * const transformer = createSecureCodeTransformer();
 * const result = transformer.transform(code, { targetVulnerabilities: [...] });
 * console.log(result.transformedCode);
 * ```
 */
export class SecureCodeTransformer {
  private transformations: Map<string, CodeTransformation>;
  private options: Required<Omit<SecureCodeTransformerOptions, 'customTransformations' | 'enabledCategories'>> & {
    enabledCategories: Set<TransformationCategory>;
  };

  constructor(options: SecureCodeTransformerOptions = {}) {
    this.transformations = new Map();
    this.options = {
      language: options.language ?? 'typescript',
      preserveFormatting: options.preserveFormatting ?? true,
      dryRun: options.dryRun ?? false,
      enabledCategories: new Set(options.enabledCategories ?? [
        'input-validation',
        'output-encoding',
        'cryptography',
        'data-protection',
        'error-handling',
        'session-management',
      ]),
    };

    // Load built-in transformations
    for (const t of BUILT_IN_TRANSFORMATIONS) {
      this.transformations.set(t.id, t);
    }

    // Add custom transformations
    if (options.customTransformations) {
      for (const t of options.customTransformations) {
        this.transformations.set(t.id, t);
      }
    }
  }

  /**
   * Transform code using security patterns
   */
  transform(code: string, options: TransformOptions = {}): TransformationResult {
    const result: TransformationResult = {
      success: false,
      originalCode: code,
      transformedCode: code,
      transformationsApplied: [],
      warnings: [],
      errors: [],
      requiredImports: [],
    };

    let transformedCode = code;
    const appliedTransformations: AppliedTransformation[] = [];
    const requiredImports: ImportSpec[] = [];

    // Get applicable transformations
    const transformations = this.getApplicableTransformations(options);

    // Apply transformations
    for (const transformation of transformations) {
      if (options.maxTransformations && 
          appliedTransformations.length >= options.maxTransformations) {
        break;
      }

      try {
        const transformResult = this.applyTransformation(
          transformedCode,
          transformation
        );

        if (transformResult.applied) {
          transformedCode = transformResult.code;
          appliedTransformations.push(...transformResult.applications);
          
          if (transformation.imports) {
            requiredImports.push(...transformation.imports);
          }
        }
      } catch (error) {
        result.errors.push(
          `Failed to apply ${transformation.name}: ${error instanceof Error ? error.message : String(error)}`
        );
      }
    }

    // Add required imports
    if (requiredImports.length > 0 && !this.options.dryRun) {
      transformedCode = this.addImports(transformedCode, requiredImports);
    }

    result.success = appliedTransformations.length > 0;
    result.transformedCode = transformedCode;
    result.transformationsApplied = appliedTransformations;
    result.requiredImports = requiredImports;

    return result;
  }

  /**
   * Transform code for specific vulnerability
   */
  transformForVulnerability(
    code: string,
    vulnerability: Vulnerability
  ): TransformationResult {
    const category = this.mapVulnerabilityToCategory(vulnerability.type);
    const relevantTransformations = [...this.transformations.values()]
      .filter(t => t.category === category);

    return this.transform(code, {
      onlyTransformations: relevantTransformations.map(t => t.id),
      targetVulnerabilities: [vulnerability],
    });
  }

  /**
   * Get available transformations
   */
  getAvailableTransformations(): CodeTransformation[] {
    return [...this.transformations.values()];
  }

  /**
   * Get transformations by category
   */
  getTransformationsByCategory(category: TransformationCategory): CodeTransformation[] {
    return [...this.transformations.values()]
      .filter(t => t.category === category);
  }

  /**
   * Add custom transformation
   */
  addTransformation(transformation: CodeTransformation): void {
    this.transformations.set(transformation.id, transformation);
  }

  /**
   * Remove transformation
   */
  removeTransformation(id: string): boolean {
    return this.transformations.delete(id);
  }

  /**
   * Preview transformation without applying
   */
  preview(code: string, transformationId: string): {
    matches: Array<{ location: SourceLocation; original: string; preview: string }>;
    wouldApply: boolean;
  } {
    const transformation = this.transformations.get(transformationId);
    if (!transformation) {
      return { matches: [], wouldApply: false };
    }

    const matches: Array<{ location: SourceLocation; original: string; preview: string }> = [];
    // const lines = code.split('\n'); // Available if needed for line-based processing

    if (transformation.pattern.type === 'regex') {
      const regex = new RegExp(transformation.pattern.value, transformation.pattern.flags || 'g');
      let match;

      while ((match = regex.exec(code)) !== null) {
        const lineNumber = code.substring(0, match.index).split('\n').length;
        const column = match.index - code.lastIndexOf('\n', match.index - 1);

        const preview = this.generateReplacement(
          match[0],
          match,
          transformation.replacement
        );

        matches.push({
          location: {
            file: 'preview',
            startLine: lineNumber,
            endLine: lineNumber,
            startColumn: column,
            endColumn: column + match[0].length,
          },
          original: match[0],
          preview,
        });
      }
    } else if (transformation.pattern.type === 'function-call') {
      const searchStr = transformation.pattern.value;
      let index = 0;

      while ((index = code.indexOf(searchStr, index)) !== -1) {
        const lineNumber = code.substring(0, index).split('\n').length;
        const column = index - code.lastIndexOf('\n', index - 1);

        matches.push({
          location: {
            file: 'preview',
            startLine: lineNumber,
            endLine: lineNumber,
            startColumn: column,
            endColumn: column + searchStr.length,
          },
          original: searchStr,
          preview: transformation.replacement.value,
        });

        index += searchStr.length;
      }
    }

    return { matches, wouldApply: matches.length > 0 };
  }

  /**
   * Validate code after transformation
   */
  validateTransformation(
    _originalCode: string,
    transformedCode: string
  ): { valid: boolean; issues: string[] } {
    const issues: string[] = [];

    // Basic validation
    if (transformedCode.trim().length === 0) {
      issues.push('Transformation resulted in empty code');
    }

    // Check bracket balance
    const brackets = ['()', '[]', '{}'];
    for (const pair of brackets) {
      const open = (transformedCode.match(new RegExp('\\' + pair[0], 'g')) || []).length;
      const close = (transformedCode.match(new RegExp('\\' + pair[1], 'g')) || []).length;
      if (open !== close) {
        issues.push(`Unbalanced ${pair}: ${open} opens, ${close} closes`);
      }
    }

    // Check for common syntax issues
    const syntaxPatterns = [
      { pattern: /;\s*;/g, issue: 'Double semicolon' },
      { pattern: /\(\s*,/g, issue: 'Missing argument before comma' },
      { pattern: /,\s*\)/g, issue: 'Trailing comma before parenthesis' },
      { pattern: /\[\s*,/g, issue: 'Missing element before comma in array' },
    ];

    for (const { pattern, issue } of syntaxPatterns) {
      if (pattern.test(transformedCode)) {
        issues.push(issue);
      }
    }

    return { valid: issues.length === 0, issues };
  }

  // ============================================================================
  // Private Methods
  // ============================================================================

  private getApplicableTransformations(options: TransformOptions): CodeTransformation[] {
    let transformations = [...this.transformations.values()];

    // Filter by enabled categories
    transformations = transformations.filter(t => 
      this.options.enabledCategories.has(t.category)
    );

    // Filter by language
    transformations = transformations.filter(t =>
      t.languages.includes(this.options.language)
    );

    // Filter by specific IDs
    if (options.onlyTransformations) {
      const ids = new Set(options.onlyTransformations);
      transformations = transformations.filter(t => ids.has(t.id));
    }

    // Exclude specific IDs
    if (options.excludeTransformations) {
      const excludeIds = new Set(options.excludeTransformations);
      transformations = transformations.filter(t => !excludeIds.has(t.id));
    }

    // Sort by risk level (safest first)
    const riskOrder = { 'safe': 0, 'caution': 1, 'review-required': 2 };
    transformations.sort((a, b) => 
      riskOrder[a.riskLevel] - riskOrder[b.riskLevel]
    );

    return transformations;
  }

  private applyTransformation(
    code: string,
    transformation: CodeTransformation
  ): { applied: boolean; code: string; applications: AppliedTransformation[] } {
    const applications: AppliedTransformation[] = [];
    let newCode = code;

    if (transformation.pattern.type === 'regex') {
      const regex = new RegExp(
        transformation.pattern.value,
        transformation.pattern.flags || 'g'
      );

      const matches: Array<{ match: RegExpExecArray; index: number }> = [];
      let match;
      while ((match = regex.exec(code)) !== null) {
        matches.push({ match: [...match] as unknown as RegExpExecArray, index: match.index });
      }

      // Apply in reverse order to preserve indices
      for (let i = matches.length - 1; i >= 0; i--) {
        const { match, index } = matches[i];
        const original = match[0];
        const replacement = this.generateReplacement(original, match, transformation.replacement);
        const lineNumber = code.substring(0, index).split('\n').length;
        const lastNewline = code.lastIndexOf('\n', index - 1);
        const column = index - lastNewline;

        newCode = newCode.substring(0, index) + replacement + newCode.substring(index + original.length);

        applications.unshift({
          transformationId: transformation.id,
          location: {
            file: 'unknown',
            startLine: lineNumber,
            endLine: lineNumber,
            startColumn: column,
            endColumn: column + original.length,
          },
          original,
          replacement,
        });
      }
    } else if (transformation.pattern.type === 'function-call') {
      const searchStr = transformation.pattern.value;
      let index = 0;
      const indices: number[] = [];

      while ((index = code.indexOf(searchStr, index)) !== -1) {
        indices.push(index);
        index += searchStr.length;
      }

      // Apply in reverse order
      for (let i = indices.length - 1; i >= 0; i--) {
        const idx = indices[i];
        const lineNumber = code.substring(0, idx).split('\n').length;
        const lastNewline = code.lastIndexOf('\n', idx - 1);
        const column = idx - lastNewline;

        newCode = newCode.substring(0, idx) + 
                  transformation.replacement.value + 
                  newCode.substring(idx + searchStr.length);

        applications.unshift({
          transformationId: transformation.id,
          location: {
            file: 'unknown',
            startLine: lineNumber,
            endLine: lineNumber,
            startColumn: column,
            endColumn: column + searchStr.length,
          },
          original: searchStr,
          replacement: transformation.replacement.value,
        });
      }
    }

    return {
      applied: applications.length > 0,
      code: newCode,
      applications,
    };
  }

  private generateReplacement(
    original: string,
    match: RegExpExecArray | string[],
    replacement: ReplacementPattern
  ): string {
    let result = replacement.value;

    // Replace capture groups
    for (let i = 1; i < match.length; i++) {
      result = result.replace(new RegExp(`\\$${i}`, 'g'), match[i] || '');
    }

    if (replacement.wrapExisting) {
      result = result.replace('$0', original);
    }

    return result;
  }

  private addImports(code: string, imports: ImportSpec[]): string {
    // Deduplicate imports
    const uniqueImports = new Map<string, ImportSpec>();
    for (const imp of imports) {
      const existing = uniqueImports.get(imp.module);
      if (existing) {
        // Merge named imports
        if (imp.named) {
          existing.named = [...new Set([...(existing.named || []), ...imp.named])];
        }
      } else {
        uniqueImports.set(imp.module, { ...imp });
      }
    }

    // Generate import statements
    const importStatements: string[] = [];
    for (const imp of uniqueImports.values()) {
      if (imp.default && imp.named?.length) {
        importStatements.push(
          `import ${imp.default}, { ${imp.named.join(', ')} } from '${imp.module}';`
        );
      } else if (imp.default) {
        importStatements.push(`import ${imp.default} from '${imp.module}';`);
      } else if (imp.named?.length) {
        const keyword = imp.typeOnly ? 'import type' : 'import';
        importStatements.push(
          `${keyword} { ${imp.named.join(', ')} } from '${imp.module}';`
        );
      }
    }

    if (importStatements.length === 0) return code;

    // Find insertion point (after existing imports or at start)
    const lines = code.split('\n');
    let insertIndex = 0;

    for (let i = 0; i < lines.length; i++) {
      if (lines[i].startsWith('import ')) {
        insertIndex = i + 1;
      } else if (insertIndex > 0 && !lines[i].trim().startsWith('import')) {
        break;
      }
    }

    lines.splice(insertIndex, 0, ...importStatements);
    return lines.join('\n');
  }

  private mapVulnerabilityToCategory(vulnType: string): TransformationCategory {
    const mapping: Record<string, TransformationCategory> = {
      'xss': 'output-encoding',
      'sql-injection': 'input-validation',
      'path-traversal': 'input-validation',
      'command-injection': 'input-validation',
      'hardcoded-secret': 'data-protection',
      'weak-crypto': 'cryptography',
      'weak-random': 'cryptography',
      'information-disclosure': 'error-handling',
      'session-fixation': 'session-management',
    };

    return mapping[vulnType] || 'general';
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create a secure code transformer
 */
export function createSecureCodeTransformer(
  options?: SecureCodeTransformerOptions
): SecureCodeTransformer {
  return new SecureCodeTransformer(options);
}

/**
 * Quick transform code
 */
export function quickTransform(code: string): TransformationResult {
  const transformer = createSecureCodeTransformer();
  return transformer.transform(code);
}

/**
 * Get all built-in transformations
 */
export function getBuiltInTransformations(): CodeTransformation[] {
  return [...BUILT_IN_TRANSFORMATIONS];
}
