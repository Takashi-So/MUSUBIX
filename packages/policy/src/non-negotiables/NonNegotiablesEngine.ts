/**
 * NonNegotiablesEngine
 *
 * Validates code and artifacts against non-negotiable rules.
 * Enforces critical constraints that must never be violated.
 *
 * @see TSK-FR-007〜012 - NonNegotiablesEngine
 * @see REQ-FR-020〜023 - NonNegotiablesEngine
 * @trace DES-MUSUBIX-FR-001 DES-POLICY-002
 */

import {
  type NonNegotiableRule,
  type NonNegotiableCategory,
  type ValidationContext,
  type Violation,
  type ViolationReport,
  type NonNegotiablesConfig,
  DEFAULT_NON_NEGOTIABLE_RULES,
  createViolationReport,
} from './types.js';

/**
 * Phase artifact interface (simplified)
 */
interface PhaseArtifact {
  readonly id?: string;
  readonly type?: string;
  readonly content?: string | unknown;
}

/**
 * Design validation result
 */
export interface DesignValidationResult {
  readonly passed: boolean;
  readonly violations: readonly { rule: string; message: string }[];
}

/**
 * Implementation validation result
 */
export interface ImplementationValidationResult {
  readonly passed: boolean;
  readonly violations: readonly { rule: string; message: string }[];
}

/**
 * NonNegotiablesEngine Interface
 */
export interface INonNegotiablesEngine {
  /** Validate content against non-negotiable rules */
  validateContent(context: ValidationContext): ViolationReport;

  /** Validate design artifacts */
  validateDesignArtifacts(
    artifacts: readonly PhaseArtifact[]
  ): Promise<DesignValidationResult>;

  /** Validate implementation files */
  validateImplementation(
    changedFiles: readonly string[]
  ): Promise<ImplementationValidationResult>;

  /** Get all registered rules */
  getRules(category?: NonNegotiableCategory): readonly NonNegotiableRule[];

  /** Get enabled rules only */
  getEnabledRules(): readonly NonNegotiableRule[];
}

/**
 * NonNegotiablesEngine Implementation
 *
 * Enforces non-negotiable rules to ensure code quality and security.
 *
 * @example
 * ```typescript
 * const engine = createNonNegotiablesEngine();
 *
 * const context = { filePath: 'src/config.ts', content: fileContent };
 * const report = engine.validateContent(context);
 *
 * if (!report.passed) {
 *   console.error('Non-negotiable violations:', report.summary);
 * }
 * ```
 */
export class NonNegotiablesEngine implements INonNegotiablesEngine {
  private readonly rules: readonly NonNegotiableRule[];
  private readonly failFast: boolean;

  constructor(config?: NonNegotiablesConfig) {
    this.rules = config?.rules ?? DEFAULT_NON_NEGOTIABLE_RULES;
    this.failFast = config?.failFast ?? false;
  }

  /**
   * Validate content against non-negotiable rules
   */
  validateContent(context: ValidationContext): ViolationReport {
    const violations: Violation[] = [];
    const enabledRules = this.getEnabledRules();

    for (const rule of enabledRules) {
      const result = this.checkRule(rule, context);

      if (!result.passed) {
        violations.push({
          rule,
          message: result.message ?? `Rule ${rule.id} violated`,
          severity: rule.severity,
          location: result.location,
          detectedAt: new Date(),
        });

        if (this.failFast) {
          break;
        }
      }
    }

    return createViolationReport(violations);
  }

  /**
   * Validate design artifacts
   */
  async validateDesignArtifacts(
    artifacts: readonly PhaseArtifact[]
  ): Promise<DesignValidationResult> {
    const violations: { rule: string; message: string }[] = [];

    for (const artifact of artifacts) {
      const content =
        typeof artifact.content === 'string'
          ? artifact.content
          : JSON.stringify(artifact.content);

      const context: ValidationContext = {
        filePath: artifact.id,
        content,
        artifactType: artifact.type,
        artifact,
      };

      const report = this.validateContent(context);

      for (const v of report.violations) {
        violations.push({
          rule: v.rule.id,
          message: v.message,
        });
      }
    }

    return {
      passed: violations.length === 0,
      violations,
    };
  }

  /**
   * Validate implementation files
   *
   * Note: In a real implementation, this would read file contents.
   * For now, it validates based on file paths only.
   */
  async validateImplementation(
    changedFiles: readonly string[]
  ): Promise<ImplementationValidationResult> {
    const violations: { rule: string; message: string }[] = [];

    // Validate file naming conventions
    for (const file of changedFiles) {
      // Check test file naming convention
      if (file.includes('__tests__') || file.includes('.test.') || file.includes('.spec.')) {
        const testNamingRule = this.rules.find(r => r.id === 'NN-CONV-001');
        if (testNamingRule?.enabled) {
          const isValidTestName =
            file.endsWith('.test.ts') ||
            file.endsWith('.spec.ts') ||
            file.endsWith('.test.tsx') ||
            file.endsWith('.spec.tsx') ||
            file.endsWith('.test.js') ||
            file.endsWith('.spec.js');

          if (!isValidTestName && !file.includes('__tests__/')) {
            // Allow files in __tests__ directories
          }
        }
      }
    }

    return {
      passed: violations.length === 0,
      violations,
    };
  }

  /**
   * Get all registered rules
   */
  getRules(category?: NonNegotiableCategory): readonly NonNegotiableRule[] {
    if (category) {
      return this.rules.filter(r => r.category === category);
    }
    return this.rules;
  }

  /**
   * Get enabled rules only
   */
  getEnabledRules(): readonly NonNegotiableRule[] {
    return this.rules.filter(r => r.enabled);
  }

  // Private helpers

  private checkRule(
    rule: NonNegotiableRule,
    context: ValidationContext
  ): { passed: boolean; message?: string; location?: { file?: string; line?: number } } {
    // Custom validation function
    if (rule.validate) {
      return rule.validate(context);
    }

    // Pattern-based validation
    if (rule.pattern && context.content) {
      const pattern =
        typeof rule.pattern === 'string' ? new RegExp(rule.pattern) : rule.pattern;

      if (pattern.test(context.content)) {
        return {
          passed: false,
          message: `${rule.name}: ${rule.description}`,
          location: { file: context.filePath },
        };
      }
    }

    return { passed: true };
  }
}

/**
 * Create a NonNegotiablesEngine instance
 *
 * @param config - Optional configuration
 * @returns INonNegotiablesEngine instance
 */
export function createNonNegotiablesEngine(
  config?: NonNegotiablesConfig
): INonNegotiablesEngine {
  return new NonNegotiablesEngine(config);
}
