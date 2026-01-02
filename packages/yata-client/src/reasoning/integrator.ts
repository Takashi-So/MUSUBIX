/**
 * Neuro-Symbolic Integrator
 * 
 * Integrates neural (LLM) and symbolic (YATA knowledge graph) reasoning
 * 
 * @packageDocumentation
 * @module reasoning/integrator
 * 
 * @see REQ-INT-001 - Neuro-Symbolic Integration
 * @see REQ-INT-001 - Symbolic Reasoning
 */

import type { YataMCPClient } from '../mcp/client.js';
import type {
  KnowledgeNode,
  PatternMatchResult,
} from '../types.js';

/**
 * Internal reasoning step (more flexible than exported type)
 */
interface InternalReasoningStep {
  /** Step number */
  step: number;
  /** Step type */
  type: string;
  /** Description */
  description: string;
  /** Confidence */
  confidence: number;
  /** Evidence/premises */
  evidence?: string[];
  premises?: string[];
  /** Conclusion */
  conclusion?: string;
}

/**
 * Internal reasoning chain result
 */
interface InternalReasoningChainResult {
  /** Reasoning steps */
  steps: InternalReasoningStep[];
  /** Final confidence */
  finalConfidence: number;
  /** Human-readable explanation */
  explanation: string;
}

/**
 * Integration mode
 */
export type IntegrationMode = 
  | 'neural-first'      // LLM generates, YATA validates
  | 'symbolic-first'    // YATA constrains, LLM completes
  | 'hybrid'            // Iterative refinement
  | 'parallel';         // Both run simultaneously, merge results

/**
 * Integration configuration
 */
export interface IntegratorConfig {
  /** Integration mode */
  mode: IntegrationMode;
  /** Maximum iterations for hybrid mode */
  maxIterations: number;
  /** Confidence threshold for acceptance */
  confidenceThreshold: number;
  /** Enable explanation generation */
  enableExplanations: boolean;
  /** Timeout per operation (ms) */
  timeout: number;
}

/**
 * Default integrator configuration
 */
export const DEFAULT_INTEGRATOR_CONFIG: IntegratorConfig = {
  mode: 'hybrid',
  maxIterations: 3,
  confidenceThreshold: 0.8,
  enableExplanations: true,
  timeout: 30000,
};

/**
 * Neural input (from LLM)
 */
export interface NeuralInput {
  /** Generated content */
  content: string;
  /** Confidence score (0-1) */
  confidence: number;
  /** Token count */
  tokens?: number;
  /** Model used */
  model?: string;
  /** Generation metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Symbolic constraints
 */
export interface SymbolicConstraints {
  /** Required patterns to match */
  patterns: string[];
  /** Required node types */
  nodeTypes: string[];
  /** Required relations */
  relations: Array<{
    type: string;
    sourceType?: string;
    targetType?: string;
  }>;
  /** Custom validation rules */
  rules: ValidationRule[];
}

/**
 * Validation rule
 */
export interface ValidationRule {
  /** Rule ID */
  id: string;
  /** Rule name */
  name: string;
  /** Rule description */
  description: string;
  /** Validation function */
  validate: (content: string, context: ValidationContext) => ValidationResult;
}

/**
 * Validation context
 */
export interface ValidationContext {
  /** Related knowledge nodes */
  relatedNodes: KnowledgeNode[];
  /** Pattern matches */
  patternMatches: PatternMatchResult[];
  /** Integration config */
  config: IntegratorConfig;
}

/**
 * Validation result
 */
export interface ValidationResult {
  /** Is valid */
  valid: boolean;
  /** Confidence (0-1) */
  confidence: number;
  /** Issues found */
  issues: ValidationIssue[];
  /** Suggestions for improvement */
  suggestions: string[];
}

/**
 * Validation issue
 */
export interface ValidationIssue {
  /** Issue severity */
  severity: 'error' | 'warning' | 'info';
  /** Issue message */
  message: string;
  /** Location in content */
  location?: {
    start: number;
    end: number;
  };
  /** Related rule ID */
  ruleId?: string;
}

/**
 * Integration result
 */
export interface IntegrationResult {
  /** Success status */
  success: boolean;
  /** Final content */
  content: string;
  /** Overall confidence */
  confidence: number;
  /** Validation results */
  validation: ValidationResult;
  /** Reasoning chain (if enabled) */
  reasoning?: InternalReasoningChainResult;
  /** Number of iterations used */
  iterations: number;
  /** Execution time (ms) */
  executionTime: number;
}

/**
 * Neuro-Symbolic Integrator
 * 
 * Bridges neural and symbolic reasoning systems
 */
export class NeuroSymbolicIntegrator {
  private client: YataMCPClient;
  private config: IntegratorConfig;
  private rules: Map<string, ValidationRule> = new Map();

  constructor(client: YataMCPClient, config?: Partial<IntegratorConfig>) {
    this.client = client;
    this.config = { ...DEFAULT_INTEGRATOR_CONFIG, ...config };
    this.initializeBuiltinRules();
  }

  /**
   * Initialize built-in validation rules
   */
  private initializeBuiltinRules(): void {
    // EARS pattern validation
    this.addRule({
      id: 'ears-pattern',
      name: 'EARS Pattern',
      description: 'Validates EARS requirement patterns',
      validate: (content, _ctx) => {
        const patterns = [
          /The .+ shall .+/i,
          /When .+, the .+ shall .+/i,
          /While .+, the .+ shall .+/i,
          /Where .+, the .+ shall .+/i,
          /If .+, then the .+ shall .+/i,
        ];

        const hasPattern = patterns.some((p) => p.test(content));

        return {
          valid: hasPattern,
          confidence: hasPattern ? 0.9 : 0.3,
          issues: hasPattern
            ? []
            : [
                {
                  severity: 'warning',
                  message: 'Content does not match any EARS pattern',
                  ruleId: 'ears-pattern',
                },
              ],
          suggestions: hasPattern
            ? []
            : ['Consider using an EARS pattern: "The <system> shall <action>"'],
        };
      },
    });

    // C4 structure validation
    this.addRule({
      id: 'c4-structure',
      name: 'C4 Structure',
      description: 'Validates C4 model structure',
      validate: (content, _ctx) => {
        const hasContext = /context|boundary|actor/i.test(content);
        const hasContainer = /container|service|database/i.test(content);

        return {
          valid: hasContext || hasContainer,
          confidence: hasContext && hasContainer ? 0.9 : 0.6,
          issues: [],
          suggestions: [],
        };
      },
    });

    // Traceability validation
    this.addRule({
      id: 'traceability',
      name: 'Traceability',
      description: 'Validates requirement-design traceability',
      validate: (content, _ctx) => {
        const hasReqRef = /REQ-[A-Z]+-\d+/i.test(content);

        return {
          valid: hasReqRef,
          confidence: hasReqRef ? 0.95 : 0.4,
          issues: hasReqRef
            ? []
            : [
                {
                  severity: 'warning',
                  message: 'No requirement reference found',
                  ruleId: 'traceability',
                },
              ],
          suggestions: hasReqRef
            ? []
            : ['Add requirement references (e.g., REQ-XXX-001)'],
        };
      },
    });
  }

  /**
   * Add validation rule
   */
  addRule(rule: ValidationRule): void {
    this.rules.set(rule.id, rule);
  }

  /**
   * Remove validation rule
   */
  removeRule(ruleId: string): boolean {
    return this.rules.delete(ruleId);
  }

  /**
   * Integrate neural output with symbolic constraints
   */
  async integrate(
    neuralInput: NeuralInput,
    constraints: Partial<SymbolicConstraints>
  ): Promise<IntegrationResult> {
    const startTime = Date.now();
    let iterations = 0;
    let content = neuralInput.content;
    let validation: ValidationResult;

    switch (this.config.mode) {
      case 'neural-first':
        validation = await this.validateWithSymbolic(content, constraints);
        iterations = 1;
        break;

      case 'symbolic-first':
        content = await this.constrainWithSymbolic(content, constraints);
        validation = await this.validateWithSymbolic(content, constraints);
        iterations = 1;
        break;

      case 'hybrid':
        ({ content, validation, iterations } = await this.hybridIntegration(
          content,
          constraints
        ));
        break;

      case 'parallel':
        ({ content, validation } = await this.parallelIntegration(
          neuralInput,
          constraints
        ));
        iterations = 1;
        break;

      default:
        validation = {
          valid: true,
          confidence: neuralInput.confidence,
          issues: [],
          suggestions: [],
        };
    }

    const result: IntegrationResult = {
      success: validation.valid && validation.confidence >= this.config.confidenceThreshold,
      content,
      confidence: validation.confidence,
      validation,
      iterations,
      executionTime: Date.now() - startTime,
    };

    if (this.config.enableExplanations) {
      result.reasoning = this.generateReasoningChain(
        neuralInput,
        constraints,
        validation
      );
    }

    return result;
  }

  /**
   * Validate content with symbolic system
   */
  private async validateWithSymbolic(
    content: string,
    constraints: Partial<SymbolicConstraints>
  ): Promise<ValidationResult> {
    const issues: ValidationIssue[] = [];
    const suggestions: string[] = [];
    let totalConfidence = 1.0;
    let ruleCount = 0;

    // Get context from knowledge graph
    let relatedNodes: KnowledgeNode[] = [];
    let patternMatches: PatternMatchResult[] = [];

    try {
      // Query related nodes
      if (constraints.nodeTypes?.length) {
        const response = await this.client.callTool<{ nodes: KnowledgeNode[] }>({
          name: 'query_graph',
          arguments: {
            query: { types: constraints.nodeTypes },
          },
        });
        if (response.success && response.result) {
          relatedNodes = response.result.nodes;
        }
      }

      // Run pattern matching
      if (constraints.patterns?.length) {
        const response = await this.client.callTool<{ matches: PatternMatchResult[] }>({
          name: 'match_patterns',
          arguments: {
            content,
            patterns: constraints.patterns,
          },
        });
        if (response.success && response.result) {
          patternMatches = response.result.matches;
        }
      }
    } catch {
      // Continue with local validation if YATA unavailable
    }

    const context: ValidationContext = {
      relatedNodes,
      patternMatches,
      config: this.config,
    };

    // Run validation rules
    const rulesToRun = constraints.rules ?? Array.from(this.rules.values());

    for (const rule of rulesToRun) {
      const result = rule.validate(content, context);
      ruleCount++;

      if (!result.valid) {
        issues.push(...result.issues);
      }
      suggestions.push(...result.suggestions);
      totalConfidence *= result.confidence;
    }

    // Normalize confidence
    const normalizedConfidence = ruleCount > 0
      ? Math.pow(totalConfidence, 1 / ruleCount)
      : 1.0;

    return {
      valid: issues.filter((i) => i.severity === 'error').length === 0,
      confidence: normalizedConfidence,
      issues,
      suggestions: [...new Set(suggestions)],
    };
  }

  /**
   * Constrain content with symbolic system
   */
  private async constrainWithSymbolic(
    content: string,
    _constraints: Partial<SymbolicConstraints>
  ): Promise<string> {
    // For now, return content as-is
    // Future: apply symbolic transformations
    return content;
  }

  /**
   * Hybrid integration with iterative refinement
   */
  private async hybridIntegration(
    content: string,
    constraints: Partial<SymbolicConstraints>
  ): Promise<{
    content: string;
    validation: ValidationResult;
    iterations: number;
  }> {
    let currentContent = content;
    let validation: ValidationResult;
    let iterations = 0;

    while (iterations < this.config.maxIterations) {
      iterations++;

      validation = await this.validateWithSymbolic(currentContent, constraints);

      if (
        validation.valid &&
        validation.confidence >= this.config.confidenceThreshold
      ) {
        break;
      }

      // Apply suggestions for refinement
      currentContent = this.applyRefinements(currentContent, validation);
    }

    return {
      content: currentContent,
      validation: validation!,
      iterations,
    };
  }

  /**
   * Parallel integration
   */
  private async parallelIntegration(
    neuralInput: NeuralInput,
    constraints: Partial<SymbolicConstraints>
  ): Promise<{
    content: string;
    validation: ValidationResult;
  }> {
    // Run validation in parallel with constraint application
    const [validation, constrained] = await Promise.all([
      this.validateWithSymbolic(neuralInput.content, constraints),
      this.constrainWithSymbolic(neuralInput.content, constraints),
    ]);

    // Merge results - prefer constrained if validation failed
    const content = validation.valid ? neuralInput.content : constrained;

    return { content, validation };
  }

  /**
   * Apply refinements based on validation results
   */
  private applyRefinements(
    content: string,
    validation: ValidationResult
  ): string {
    // Simple refinement: add suggestions as comments
    // Future: intelligent content modification
    let refined = content;

    for (const suggestion of validation.suggestions) {
      if (!refined.includes(suggestion)) {
        refined += `\n<!-- Suggestion: ${suggestion} -->`;
      }
    }

    return refined;
  }

  /**
   * Generate reasoning chain for explanation
   */
  private generateReasoningChain(
    input: NeuralInput,
    _constraints: Partial<SymbolicConstraints>,
    validation: ValidationResult
  ): InternalReasoningChainResult {
    const steps: InternalReasoningStep[] = [
      {
        step: 1,
        type: 'input',
        description: 'Received neural input',
        confidence: input.confidence,
        evidence: [`Model: ${input.model ?? 'unknown'}`, `Tokens: ${input.tokens ?? 'unknown'}`],
      },
      {
        step: 2,
        type: 'constraint-check',
        description: 'Applied symbolic constraints',
        confidence: 0.95,
        evidence: [
          `Patterns: ${_constraints.patterns?.length ?? 0}`,
          `Node types: ${_constraints.nodeTypes?.length ?? 0}`,
          `Rules: ${_constraints.rules?.length ?? this.rules.size}`,
        ],
      },
      {
        step: 3,
        type: 'validation',
        description: 'Validated against rules',
        confidence: validation.confidence,
        evidence: [
          `Valid: ${validation.valid}`,
          `Issues: ${validation.issues.length}`,
          `Suggestions: ${validation.suggestions.length}`,
        ],
      },
    ];

    return {
      steps,
      finalConfidence: validation.confidence,
      explanation: this.generateExplanation(steps, validation),
    };
  }

  /**
   * Generate human-readable explanation
   */
  private generateExplanation(
    steps: InternalReasoningStep[],
    validation: ValidationResult
  ): string {
    const parts: string[] = [
      `Integration completed in ${steps.length} steps.`,
    ];

    if (validation.valid) {
      parts.push(
        `Content passed validation with ${(validation.confidence * 100).toFixed(1)}% confidence.`
      );
    } else {
      parts.push(
        `Content has ${validation.issues.length} issue(s) requiring attention.`
      );
    }

    if (validation.suggestions.length > 0) {
      parts.push(`Suggestions: ${validation.suggestions.join('; ')}`);
    }

    return parts.join(' ');
  }
}

/**
 * Create neuro-symbolic integrator instance
 */
export function createNeuroSymbolicIntegrator(
  client: YataMCPClient,
  config?: Partial<IntegratorConfig>
): NeuroSymbolicIntegrator {
  return new NeuroSymbolicIntegrator(client, config);
}
