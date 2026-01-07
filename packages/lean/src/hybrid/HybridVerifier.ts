/**
 * @fileoverview Hybrid verifier combining runtime tests and formal verification
 * @module @nahisaho/musubix-lean/hybrid
 * @traceability REQ-LEAN-HYBRID-001 to REQ-LEAN-HYBRID-003
 */

import { Result, ok, err } from 'neverthrow';
import type {
  HybridVerificationResult,
  LeanTheorem,
  LeanConfig,
} from '../types.js';
import { LeanRunner } from '../infrastructure/LeanRunner.js';
import { LeanFileGenerator } from '../infrastructure/LeanFileGenerator.js';
import type { VerificationReporter } from '../reporting/VerificationReporter.js';
import type { TraceabilityManager } from '../traceability/TraceabilityManager.js';
import { LeanVerificationError } from '../errors.js';

/**
 * Runtime test result
 */
export interface RuntimeTestResult {
  functionId: string;
  passed: boolean;
  testCount: number;
  failedTests: string[];
  coverage: number;
  duration: number;
}

/**
 * Formal verification result
 */
export interface FormalVerificationResult {
  theoremId: string;
  proved: boolean;
  proof?: string;
  errors: string[];
  duration: number;
}

/**
 * Coverage metrics for hybrid verification
 */
export interface HybridCoverage {
  runtimeCoverage: number;
  formalCoverage: number;
  combinedCoverage: number;
  uncoveredPaths: string[];
}

/**
 * Hybrid verification strategy
 */
export type VerificationStrategy = 'runtime-first' | 'formal-first' | 'parallel' | 'adaptive';

/**
 * Combines runtime testing with formal proof verification
 * @traceability REQ-LEAN-HYBRID-001
 */
export class HybridVerifier {
  private runner: LeanRunner;
  private generator: LeanFileGenerator;
  private _reporter?: VerificationReporter;
  private traceability?: TraceabilityManager;
  private strategy: VerificationStrategy = 'runtime-first';

  constructor(config: Partial<LeanConfig> = {}) {
    this.runner = new LeanRunner(config);
    this.generator = new LeanFileGenerator(config);
  }

  /**
   * Set verification reporter
   */
  setReporter(reporter: VerificationReporter): void {
    this._reporter = reporter;
  }

  /**
   * Set traceability manager
   */
  setTraceabilityManager(manager: TraceabilityManager): void {
    this.traceability = manager;
  }

  /**
   * Set verification strategy
   */
  setStrategy(strategy: VerificationStrategy): void {
    this.strategy = strategy;
  }

  /**
   * Verify a function with hybrid approach
   * @traceability REQ-LEAN-HYBRID-002
   */
  async verify(
    functionId: string,
    runtimeTests: () => RuntimeTestResult,
    theorem: LeanTheorem
  ): Promise<Result<HybridVerificationResult, LeanVerificationError>> {
    try {
      let runtimeResult: RuntimeTestResult | undefined;
      let formalResult: FormalVerificationResult | undefined;

      switch (this.strategy) {
        case 'runtime-first':
          runtimeResult = runtimeTests();
          if (!runtimeResult.passed) {
            // Skip formal if runtime fails
            return ok(this.buildResult(functionId, runtimeResult, undefined));
          }
          formalResult = await this.runFormalVerification(theorem);
          break;

        case 'formal-first':
          formalResult = await this.runFormalVerification(theorem);
          if (!formalResult.proved) {
            // Skip runtime if formal fails
            return ok(this.buildResult(functionId, undefined, formalResult));
          }
          runtimeResult = runtimeTests();
          break;

        case 'parallel':
          // Run both in parallel
          const [runtime, formal] = await Promise.all([
            Promise.resolve(runtimeTests()),
            this.runFormalVerification(theorem),
          ]);
          runtimeResult = runtime;
          formalResult = formal;
          break;

        case 'adaptive':
          // Choose strategy based on theorem complexity
          if (this.isComplexTheorem(theorem)) {
            runtimeResult = runtimeTests();
            if (runtimeResult.passed) {
              formalResult = await this.runFormalVerification(theorem);
            }
          } else {
            formalResult = await this.runFormalVerification(theorem);
            runtimeResult = runtimeTests();
          }
          break;
      }

      const result = this.buildResult(functionId, runtimeResult, formalResult);

      // Record in traceability
      if (this.traceability) {
        this.traceability.createLink(functionId, theorem.id, 'theorem_to_code', result.coverage.combinedCoverage / 100);
      }

      return ok(result);
    } catch (error) {
      return err(
        new LeanVerificationError(
          `Hybrid verification failed: ${error instanceof Error ? error.message : String(error)}`
        )
      );
    }
  }

  /**
   * Run formal verification for a theorem
   */
  private async runFormalVerification(theorem: LeanTheorem): Promise<FormalVerificationResult> {
    const startTime = Date.now();

    try {
      // Generate Lean file
      const outputDir = process.cwd();
      const genResult = await this.generator.generate([theorem], {
        outputDir,
        includeImports: true,
        includeProofs: true,
      });

      // Type check with Lean
      const checkResult = await this.runner.typeCheck(genResult.path);

      return {
        theoremId: theorem.id,
        proved: checkResult.valid,
        proof: theorem.proof?.leanCode,
        errors: checkResult.errors,
        duration: Date.now() - startTime,
      };
    } catch (error) {
      return {
        theoremId: theorem.id,
        proved: false,
        errors: [error instanceof Error ? error.message : String(error)],
        duration: Date.now() - startTime,
      };
    }
  }

  /**
   * Build hybrid verification result
   */
  private buildResult(
    functionId: string,
    runtimeResult?: RuntimeTestResult,
    formalResult?: FormalVerificationResult
  ): HybridVerificationResult {
    const coverage = this.calculateCoverage(runtimeResult, formalResult);
    const combinedStatus = this.determineCombinedStatus(runtimeResult, formalResult);

    return {
      functionId,
      runtimeResult: runtimeResult
        ? {
            passed: runtimeResult.passed,
            testCount: runtimeResult.testCount,
            failedTests: runtimeResult.failedTests,
            coverage: runtimeResult.coverage,
            duration: runtimeResult.duration,
          }
        : undefined,
      formalResult: formalResult
        ? {
            proved: formalResult.proved,
            proof: formalResult.proof,
            errors: formalResult.errors,
            duration: formalResult.duration,
          }
        : undefined,
      combinedStatus,
      coverage,
    };
  }

  /**
   * Calculate combined coverage metrics
   * @traceability REQ-LEAN-HYBRID-003
   */
  private calculateCoverage(
    runtimeResult?: RuntimeTestResult,
    formalResult?: FormalVerificationResult
  ): HybridCoverage {
    const runtimeCoverage = runtimeResult?.coverage ?? 0;
    const formalCoverage = formalResult?.proved ? 100 : 0;

    // Combined coverage weights: formal proof is weighted higher
    const combinedCoverage = formalCoverage > 0
      ? Math.min(100, runtimeCoverage * 0.3 + formalCoverage * 0.7)
      : runtimeCoverage * 0.5;

    return {
      runtimeCoverage,
      formalCoverage,
      combinedCoverage,
      uncoveredPaths: [], // Would need path analysis to populate
    };
  }

  /**
   * Determine combined verification status
   */
  private determineCombinedStatus(
    runtimeResult?: RuntimeTestResult,
    formalResult?: FormalVerificationResult
  ): 'verified' | 'partial' | 'failed' | 'unknown' {
    if (!runtimeResult && !formalResult) {
      return 'unknown';
    }

    // Both passed
    if (runtimeResult?.passed && formalResult?.proved) {
      return 'verified';
    }

    // At least one passed
    if (runtimeResult?.passed || formalResult?.proved) {
      return 'partial';
    }

    // Both ran but failed
    if (runtimeResult && formalResult) {
      return 'failed';
    }

    // Only one ran
    return 'partial';
  }

  /**
   * Check if theorem is complex (heuristic)
   */
  private isComplexTheorem(theorem: LeanTheorem): boolean {
    const statement = theorem.statement;

    // Heuristics for complexity
    const hasQuantifiers = /forall|exists|∀|∃/.test(statement);
    const hasInduction = /induction|recursion/.test(statement);
    const nestedDepth = (statement.match(/\(/g) || []).length;

    return hasQuantifiers || hasInduction || nestedDepth > 5;
  }

  /**
   * Batch verify multiple functions
   */
  async verifyBatch(
    items: Array<{
      functionId: string;
      runtimeTests: () => RuntimeTestResult;
      theorem: LeanTheorem;
    }>
  ): Promise<Map<string, HybridVerificationResult>> {
    const results = new Map<string, HybridVerificationResult>();

    for (const item of items) {
      const result = await this.verify(item.functionId, item.runtimeTests, item.theorem);
      if (result.isOk()) {
        results.set(item.functionId, result.value);
      }
    }

    return results;
  }

  /**
   * Get verification statistics
   */
  getStatistics(
    results: Map<string, HybridVerificationResult>
  ): {
    total: number;
    verified: number;
    partial: number;
    failed: number;
    averageCoverage: number;
  } {
    const values = Array.from(results.values());
    const total = values.length;

    const verified = values.filter((r) => r.combinedStatus === 'verified').length;
    const partial = values.filter((r) => r.combinedStatus === 'partial').length;
    const failed = values.filter((r) => r.combinedStatus === 'failed').length;

    const avgCoverage =
      total > 0
        ? values.reduce((sum, r) => sum + r.coverage.combinedCoverage, 0) / total
        : 0;

    return {
      total,
      verified,
      partial,
      failed,
      averageCoverage: avgCoverage,
    };
  }
}
