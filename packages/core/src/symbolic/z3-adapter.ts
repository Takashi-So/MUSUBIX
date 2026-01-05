/**
 * Z3 SMT Solver Adapter
 *
 * Adapter for Z3 theorem prover with timeout handling,
 * result parsing, and graceful degradation.
 *
 * @packageDocumentation
 * @module symbolic/formal
 *
 * @see REQ-FV-002, REQ-FV-003, REQ-FV-004 - Formal Verification
 * @see REQ-NFR-001 - Performance Requirements
 * @see DES-SYMB-001 §4.5〜§4.7, §6.1
 * @see TSK-SYMB-011
 */

import { spawn } from 'child_process';
import type { Explanation, Evidence } from './types.js';
import type { VerificationCondition } from './vc-generator.js';

// ============================================================
// Z3 Result Types
// ============================================================

/**
 * Z3 verification verdict
 */
export type Z3Verdict = 'sat' | 'unsat' | 'unknown' | 'timeout' | 'error';

/**
 * Z3 execution result
 */
export interface Z3Result {
  /** Verification verdict */
  verdict: Z3Verdict;
  /** Model (if sat) */
  model?: Record<string, unknown>;
  /** Unsat core (if available and unsat) */
  unsatCore?: string[];
  /** Raw Z3 output */
  rawOutput: string;
  /** Execution time in ms */
  executionTimeMs: number;
  /** Whether timeout occurred */
  timedOut: boolean;
  /** Error message if error */
  errorMessage?: string;
}

/**
 * Verification result for a single condition
 */
export interface VcVerificationResult {
  /** VC ID */
  vcId: string;
  /** Verification status */
  status: 'verified' | 'failed' | 'unknown' | 'timeout' | 'error';
  /** Z3 result */
  z3Result: Z3Result;
  /** Counter-example (if failed) */
  counterExample?: Record<string, unknown>;
  /** Fix suggestions */
  fixSuggestions?: string[];
  /** Explanation */
  explanation: Explanation;
}

/**
 * Complete formal verification result
 */
export interface FormalVerificationResult {
  /** Overall verdict */
  overallVerdict: 'valid' | 'invalid' | 'unknown' | 'partial';
  /** Individual VC results */
  vcResults: VcVerificationResult[];
  /** SMT-LIB used (for evidence) */
  smtLibUsed: string;
  /** Total execution time */
  totalExecutionTimeMs: number;
  /** Partial result metadata */
  partialResultMetadata?: {
    completedVcs: number;
    totalVcs: number;
    unavailableChecks: string[];
    reason: string;
  };
  /** Overall explanation */
  explanation: Explanation;
}

// ============================================================
// Z3 Adapter Configuration
// ============================================================

/**
 * Z3 Adapter configuration
 */
export interface Z3AdapterConfig {
  /** Path to Z3 executable */
  z3Path?: string;
  /** Timeout per VC in ms */
  timeoutMs?: number;
  /** Total timeout in ms */
  totalTimeoutMs?: number;
  /** Enable model generation */
  produceModels?: boolean;
  /** Enable unsat core generation */
  produceUnsatCores?: boolean;
  /** Enable proof generation */
  produceProofs?: boolean;
  /** Memory limit in MB */
  memoryLimitMb?: number;
  /** Fallback when Z3 unavailable */
  fallbackBehavior?: 'skip' | 'warn' | 'error';
}

/**
 * Default configuration
 */
export const DEFAULT_Z3_CONFIG: Z3AdapterConfig = {
  z3Path: 'z3',
  timeoutMs: 5000,
  totalTimeoutMs: 30000,
  produceModels: true,
  produceUnsatCores: false,
  produceProofs: false,
  memoryLimitMb: 512,
  fallbackBehavior: 'warn',
};

// ============================================================
// Z3 Adapter
// ============================================================

/**
 * Z3 SMT Solver Adapter
 *
 * Provides interface to Z3 theorem prover for formal verification
 * of verification conditions.
 */
export class Z3Adapter {
  private readonly config: Z3AdapterConfig;
  private z3Available: boolean | null = null;

  constructor(config: Partial<Z3AdapterConfig> = {}) {
    this.config = { ...DEFAULT_Z3_CONFIG, ...config };
  }

  /**
   * Check if Z3 is available
   */
  async isAvailable(): Promise<boolean> {
    if (this.z3Available !== null) {
      return this.z3Available;
    }

    try {
      const result = await this.executeZ3('(check-sat)\n', 1000);
      this.z3Available = !result.timedOut && result.verdict !== 'error';
      return this.z3Available;
    } catch {
      this.z3Available = false;
      return false;
    }
  }

  /**
   * Execute SMT-LIB on Z3
   */
  async executeZ3(smtLib: string, timeoutMs?: number): Promise<Z3Result> {
    const timeout = timeoutMs ?? this.config.timeoutMs ?? 5000;
    const startTime = Date.now();

    return new Promise((resolve) => {
      try {
        const z3Process = spawn(this.config.z3Path ?? 'z3', ['-in', `-T:${Math.ceil(timeout / 1000)}`], {
          timeout,
        });

        let stdout = '';
        let stderr = '';
        let timedOut = false;

        const timeoutHandle = setTimeout(() => {
          timedOut = true;
          z3Process.kill('SIGTERM');
        }, timeout);

        z3Process.stdout.on('data', (data) => {
          stdout += data.toString();
        });

        z3Process.stderr.on('data', (data) => {
          stderr += data.toString();
        });

        z3Process.on('close', (code) => {
          clearTimeout(timeoutHandle);
          const executionTimeMs = Date.now() - startTime;

          if (timedOut) {
            resolve({
              verdict: 'timeout',
              rawOutput: stdout,
              executionTimeMs,
              timedOut: true,
              errorMessage: 'Z3 execution timed out',
            });
            return;
          }

          const result = this.parseZ3Output(stdout, executionTimeMs);
          if (code !== 0 && result.verdict !== 'sat' && result.verdict !== 'unsat') {
            result.verdict = 'error';
            result.errorMessage = stderr || `Z3 exited with code ${code}`;
          }

          resolve(result);
        });

        z3Process.on('error', (err) => {
          clearTimeout(timeoutHandle);
          resolve({
            verdict: 'error',
            rawOutput: '',
            executionTimeMs: Date.now() - startTime,
            timedOut: false,
            errorMessage: `Z3 spawn error: ${err.message}`,
          });
        });

        z3Process.stdin.write(smtLib);
        z3Process.stdin.end();
      } catch (err) {
        resolve({
          verdict: 'error',
          rawOutput: '',
          executionTimeMs: Date.now() - startTime,
          timedOut: false,
          errorMessage: `Z3 execution error: ${err instanceof Error ? err.message : String(err)}`,
        });
      }
    });
  }

  /**
   * Parse Z3 output
   */
  private parseZ3Output(output: string, executionTimeMs: number): Z3Result {
    const trimmedOutput = output.trim();

    // Check verdict
    let verdict: Z3Verdict = 'unknown';
    if (trimmedOutput.includes('unsat')) {
      verdict = 'unsat';
    } else if (trimmedOutput.includes('sat')) {
      verdict = 'sat';
    } else if (trimmedOutput.includes('unknown')) {
      verdict = 'unknown';
    } else if (trimmedOutput.includes('timeout')) {
      verdict = 'timeout';
    }

    // Parse model if sat
    let model: Record<string, unknown> | undefined;
    if (verdict === 'sat' && this.config.produceModels) {
      model = this.parseModel(trimmedOutput);
    }

    return {
      verdict,
      model,
      rawOutput: trimmedOutput,
      executionTimeMs,
      timedOut: false,
    };
  }

  /**
   * Parse model from Z3 output
   */
  private parseModel(output: string): Record<string, unknown> {
    const model: Record<string, unknown> = {};

    // Simple model parsing for common patterns
    // (define-fun x () Int 42)
    const defineMatches = output.matchAll(/\(define-fun\s+(\w+)\s+\([^)]*\)\s+(\w+)\s+([^)]+)\)/g);
    for (const match of defineMatches) {
      const [, name, type, value] = match;
      if (type === 'Int') {
        model[name] = parseInt(value, 10);
      } else if (type === 'Bool') {
        model[name] = value === 'true';
      } else {
        model[name] = value;
      }
    }

    return model;
  }

  /**
   * Verify single verification condition
   */
  async verifyCondition(vc: VerificationCondition, smtLib: string): Promise<VcVerificationResult> {
    const available = await this.isAvailable();

    if (!available) {
      return this.handleUnavailable(vc);
    }

    const z3Result = await this.executeZ3(smtLib);

    return this.interpretResult(vc, z3Result, smtLib);
  }

  /**
   * Verify multiple verification conditions
   */
  async verifyAll(
    conditions: VerificationCondition[],
    combinedSmtLib: string,
  ): Promise<FormalVerificationResult> {
    const startTime = Date.now();
    const available = await this.isAvailable();

    if (!available) {
      return this.handleAllUnavailable(conditions, combinedSmtLib);
    }

    // Execute combined verification
    const z3Result = await this.executeZ3(combinedSmtLib, this.config.totalTimeoutMs);
    const totalExecutionTimeMs = Date.now() - startTime;

    // Create results for each VC
    const vcResults: VcVerificationResult[] = conditions.map((vc) =>
      this.interpretResult(vc, z3Result, combinedSmtLib),
    );

    // Determine overall verdict
    const hasTimeout = z3Result.timedOut;
    const hasError = z3Result.verdict === 'error';
    const allVerified = vcResults.every((r) => r.status === 'verified');
    const anyFailed = vcResults.some((r) => r.status === 'failed');

    let overallVerdict: FormalVerificationResult['overallVerdict'];
    if (hasTimeout || hasError) {
      overallVerdict = 'partial';
    } else if (allVerified) {
      overallVerdict = 'valid';
    } else if (anyFailed) {
      overallVerdict = 'invalid';
    } else {
      overallVerdict = 'unknown';
    }

    const evidence: Evidence[] = [
      {
        type: 'verification',
        source: 'z3',
        content: z3Result.rawOutput.slice(0, 500),
      },
    ];

    return {
      overallVerdict,
      vcResults,
      smtLibUsed: combinedSmtLib,
      totalExecutionTimeMs,
      partialResultMetadata:
        hasTimeout || hasError
          ? {
              completedVcs: vcResults.filter((r) => r.status !== 'timeout' && r.status !== 'error')
                .length,
              totalVcs: conditions.length,
              unavailableChecks: hasTimeout ? ['timeout'] : ['z3_error'],
              reason: z3Result.errorMessage ?? 'Z3 execution incomplete',
            }
          : undefined,
      explanation: {
        summary: `Formal verification ${overallVerdict}: ${vcResults.filter((r) => r.status === 'verified').length}/${conditions.length} VCs passed`,
        reasoning: [
          `Executed Z3 on ${conditions.length} verification conditions`,
          `Total execution time: ${totalExecutionTimeMs}ms`,
          z3Result.verdict === 'unsat'
            ? 'All constraints are satisfiable (verified)'
            : z3Result.verdict === 'sat'
              ? 'Found satisfying assignment (potential issue)'
              : `Z3 returned: ${z3Result.verdict}`,
        ],
        evidence,
        relatedRequirements: [...new Set(conditions.flatMap((c) => c.requirementIds))],
      },
    };
  }

  /**
   * Interpret Z3 result for a single VC
   */
  private interpretResult(
    vc: VerificationCondition,
    z3Result: Z3Result,
    smtLib: string,
  ): VcVerificationResult {
    let status: VcVerificationResult['status'];
    let fixSuggestions: string[] | undefined;
    let counterExample: Record<string, unknown> | undefined;

    switch (z3Result.verdict) {
      case 'unsat':
        // unsat means the negation is unsatisfiable, so the property holds
        status = 'verified';
        break;
      case 'sat':
        // sat means found counter-example
        status = 'failed';
        counterExample = z3Result.model;
        fixSuggestions = this.generateFixSuggestions(vc, z3Result);
        break;
      case 'timeout':
        status = 'timeout';
        break;
      case 'error':
        status = 'error';
        break;
      default:
        status = 'unknown';
    }

    const evidence: Evidence[] = [
      {
        type: 'verification',
        source: 'z3',
        content: smtLib.slice(0, 200),
      },
    ];

    return {
      vcId: vc.id,
      status,
      z3Result,
      counterExample,
      fixSuggestions,
      explanation: {
        summary: `${vc.type} verification ${status}: ${vc.description}`,
        reasoning: [
          `VC type: ${vc.type}`,
          `Z3 verdict: ${z3Result.verdict}`,
          `Execution time: ${z3Result.executionTimeMs}ms`,
          counterExample ? `Counter-example found: ${JSON.stringify(counterExample)}` : '',
        ].filter(Boolean),
        evidence,
        relatedRequirements: vc.requirementIds,
      },
    };
  }

  /**
   * Generate fix suggestions based on counter-example
   */
  private generateFixSuggestions(vc: VerificationCondition, z3Result: Z3Result): string[] {
    const suggestions: string[] = [];

    if (z3Result.model) {
      suggestions.push(`Review values: ${JSON.stringify(z3Result.model)}`);
    }

    switch (vc.type) {
      case 'precondition':
        suggestions.push('Strengthen input validation');
        suggestions.push('Add guards to check preconditions');
        break;
      case 'postcondition':
        suggestions.push('Ensure return values meet specification');
        suggestions.push('Add assertions before return');
        break;
      case 'invariant':
        suggestions.push('Check that invariant is maintained across all operations');
        suggestions.push('Review state transitions');
        break;
      case 'boundary':
        suggestions.push('Add boundary checks for edge cases');
        suggestions.push('Validate input ranges');
        break;
    }

    return suggestions;
  }

  /**
   * Handle Z3 unavailable for single VC
   */
  private handleUnavailable(vc: VerificationCondition): VcVerificationResult {
    return {
      vcId: vc.id,
      status: 'error',
      z3Result: {
        verdict: 'error',
        rawOutput: '',
        executionTimeMs: 0,
        timedOut: false,
        errorMessage: 'Z3 is not available',
      },
      explanation: {
        summary: `Verification skipped: Z3 unavailable`,
        reasoning: [
          'Z3 theorem prover is not installed or not in PATH',
          `Fallback behavior: ${this.config.fallbackBehavior}`,
        ],
        evidence: [],
        relatedRequirements: vc.requirementIds,
      },
    };
  }

  /**
   * Handle Z3 unavailable for all VCs
   */
  private handleAllUnavailable(
    conditions: VerificationCondition[],
    smtLib: string,
  ): FormalVerificationResult {
    return {
      overallVerdict: 'partial',
      vcResults: conditions.map((vc) => this.handleUnavailable(vc)),
      smtLibUsed: smtLib,
      totalExecutionTimeMs: 0,
      partialResultMetadata: {
        completedVcs: 0,
        totalVcs: conditions.length,
        unavailableChecks: ['z3_unavailable'],
        reason: 'Z3 theorem prover is not available',
      },
      explanation: {
        summary: 'Formal verification skipped: Z3 unavailable',
        reasoning: [
          'Z3 theorem prover is not installed or not in PATH',
          'Install Z3 to enable formal verification',
          `Fallback behavior: ${this.config.fallbackBehavior}`,
        ],
        evidence: [],
        relatedRequirements: [...new Set(conditions.flatMap((c) => c.requirementIds))],
      },
    };
  }
}

/**
 * Create Z3 adapter
 */
export function createZ3Adapter(config?: Partial<Z3AdapterConfig>): Z3Adapter {
  return new Z3Adapter(config);
}

// ============================================================
// Pre/Post/Invariant Verifiers
// ============================================================

/**
 * Precondition verifier
 */
export class PreconditionVerifier {
  private readonly z3: Z3Adapter;

  constructor(z3Adapter?: Z3Adapter) {
    this.z3 = z3Adapter ?? new Z3Adapter();
  }

  /**
   * Verify preconditions
   */
  async verify(
    preconditions: string[],
    context: { variables: Array<{ name: string; type: string }> },
  ): Promise<FormalVerificationResult> {
    const conditions: VerificationCondition[] = preconditions.map((pre, idx) => ({
      id: `PRE-${idx + 1}`,
      type: 'precondition' as const,
      description: pre,
      smtExpression: pre,
      requirementIds: [],
      status: 'pending' as const,
      generatedAt: new Date().toISOString(),
    }));

    let smtLib = '(set-logic QF_LIA)\n';
    for (const v of context.variables) {
      const smtType = v.type === 'number' ? 'Int' : v.type === 'boolean' ? 'Bool' : 'Int';
      smtLib += `(declare-const ${v.name} ${smtType})\n`;
    }
    for (const pre of preconditions) {
      smtLib += `(assert ${pre})\n`;
    }
    smtLib += '(check-sat)\n';

    return this.z3.verifyAll(conditions, smtLib);
  }
}

/**
 * Postcondition verifier
 */
export class PostconditionVerifier {
  private readonly z3: Z3Adapter;

  constructor(z3Adapter?: Z3Adapter) {
    this.z3 = z3Adapter ?? new Z3Adapter();
  }

  /**
   * Verify postconditions given preconditions
   */
  async verify(
    preconditions: string[],
    postconditions: string[],
    context: { variables: Array<{ name: string; type: string }> },
  ): Promise<FormalVerificationResult> {
    const conditions: VerificationCondition[] = postconditions.map((post, idx) => ({
      id: `POST-${idx + 1}`,
      type: 'postcondition' as const,
      description: post,
      smtExpression: post,
      requirementIds: [],
      status: 'pending' as const,
      generatedAt: new Date().toISOString(),
    }));

    let smtLib = '(set-logic QF_LIA)\n';
    for (const v of context.variables) {
      const smtType = v.type === 'number' ? 'Int' : v.type === 'boolean' ? 'Bool' : 'Int';
      smtLib += `(declare-const ${v.name} ${smtType})\n`;
    }
    // Assume preconditions
    for (const pre of preconditions) {
      smtLib += `(assert ${pre})\n`;
    }
    // Assert postconditions
    for (const post of postconditions) {
      smtLib += `(assert ${post})\n`;
    }
    smtLib += '(check-sat)\n';

    return this.z3.verifyAll(conditions, smtLib);
  }
}

/**
 * Invariant verifier
 */
export class InvariantVerifier {
  private readonly z3: Z3Adapter;

  constructor(z3Adapter?: Z3Adapter) {
    this.z3 = z3Adapter ?? new Z3Adapter();
  }

  /**
   * Verify invariants hold
   */
  async verify(
    invariants: string[],
    context: { variables: Array<{ name: string; type: string }> },
  ): Promise<FormalVerificationResult> {
    const conditions: VerificationCondition[] = invariants.map((inv, idx) => ({
      id: `INV-${idx + 1}`,
      type: 'invariant' as const,
      description: inv,
      smtExpression: inv,
      requirementIds: [],
      status: 'pending' as const,
      generatedAt: new Date().toISOString(),
    }));

    let smtLib = '(set-logic QF_LIA)\n';
    for (const v of context.variables) {
      const smtType = v.type === 'number' ? 'Int' : v.type === 'boolean' ? 'Bool' : 'Int';
      smtLib += `(declare-const ${v.name} ${smtType})\n`;
    }
    for (const inv of invariants) {
      smtLib += `(assert ${inv})\n`;
    }
    smtLib += '(check-sat)\n';

    return this.z3.verifyAll(conditions, smtLib);
  }
}

/**
 * Create precondition verifier
 */
export function createPreconditionVerifier(z3Adapter?: Z3Adapter): PreconditionVerifier {
  return new PreconditionVerifier(z3Adapter);
}

/**
 * Create postcondition verifier
 */
export function createPostconditionVerifier(z3Adapter?: Z3Adapter): PostconditionVerifier {
  return new PostconditionVerifier(z3Adapter);
}

/**
 * Create invariant verifier
 */
export function createInvariantVerifier(z3Adapter?: Z3Adapter): InvariantVerifier {
  return new InvariantVerifier(z3Adapter);
}
