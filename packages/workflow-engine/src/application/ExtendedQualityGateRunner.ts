/**
 * ExtendedQualityGateRunner - Application Service
 *
 * Runs extended quality gates with timing and context support.
 * Provides compatibility bridge to standard QualityGateRunner.
 *
 * @see TSK-FR-055 - ExtendedQualityGateRunner
 * @see REQ-FR-020〜023 - NonNegotiablesEngine
 * @see REQ-FR-040〜041 - TriageEngine
 * @trace DES-MUSUBIX-FR-001 Section 3.3.3
 */

import type { PhaseType } from '../domain/value-objects/index.js';
import type { QualityGateResult, QualityCheckResult } from '../domain/entities/QualityGate.js';
import type { QualityGateRunner } from './QualityGateRunner.js';
import {
  type ExtendedQualityGate,
  type GateTiming,
  type GateExecutionContext,
  toStandardGate,
  filterGatesByTiming,
  filterGatesByPhase,
} from '../domain/entities/ExtendedQualityGate.js';

/**
 * Extended gate run result
 */
export interface ExtendedGateRunResult {
  /** Phase that was checked */
  readonly phase: PhaseType;
  /** Timing that was checked (entry or exit) */
  readonly timing: GateTiming;
  /** Individual gate results */
  readonly results: readonly QualityGateResult[];
  /** Whether all gates passed */
  readonly allPassed: boolean;
  /** Whether all mandatory gates passed */
  readonly mandatoryPassed: boolean;
  /** Human-readable summary */
  readonly summary: string;
  /** Total execution duration in ms */
  readonly duration: number;
}

/**
 * Extended gate runner configuration
 */
export interface ExtendedQualityGateRunnerConfig {
  /** Timeout for individual gate execution (ms) */
  gateTimeout?: number;
  /** Continue running gates after failure */
  continueOnFailure?: boolean;
}

/**
 * Extended Quality Gate Runner
 *
 * Manages and executes extended quality gates with timing and context support.
 * Can bridge to standard QualityGateRunner for backward compatibility.
 *
 * @example
 * ```typescript
 * const runner = new ExtendedQualityGateRunner();
 *
 * runner.registerExtendedGate(triageGate);
 * runner.registerExtendedGate(nonNegotiablesGate);
 *
 * const context = { workflowId, phase: 'design', artifacts, services };
 * const result = await runner.runExtendedGates('design', 'exit', context);
 *
 * if (!result.mandatoryPassed) {
 *   console.error('Phase transition blocked:', result.summary);
 * }
 * ```
 *
 * @trace DES-MUSUBIX-FR-001 Section 3.3.3
 */
export class ExtendedQualityGateRunner {
  private gates: Map<PhaseType, ExtendedQualityGate[]> = new Map();
  private readonly config: Required<ExtendedQualityGateRunnerConfig>;

  constructor(config: ExtendedQualityGateRunnerConfig = {}) {
    this.config = {
      gateTimeout: config.gateTimeout ?? 30000,
      continueOnFailure: config.continueOnFailure ?? true,
    };
  }

  /**
   * Register an extended quality gate
   *
   * @param gate - Extended gate to register
   */
  registerExtendedGate(gate: ExtendedQualityGate): void {
    const phaseGates = this.gates.get(gate.phase) ?? [];
    phaseGates.push(gate);
    this.gates.set(gate.phase, phaseGates);
  }

  /**
   * Get all extended gates for a phase
   *
   * @param phase - Phase type
   * @returns Registered extended gates
   */
  getExtendedGates(phase: PhaseType): readonly ExtendedQualityGate[] {
    return this.gates.get(phase) ?? [];
  }

  /**
   * Run extended gates for a phase and timing
   *
   * @param phase - Phase type
   * @param timing - Gate timing (entry or exit)
   * @param context - Execution context
   * @returns Gate run result
   */
  async runExtendedGates(
    phase: PhaseType,
    timing: GateTiming,
    context: GateExecutionContext
  ): Promise<ExtendedGateRunResult> {
    const startTime = Date.now();
    const allGates = this.gates.get(phase) ?? [];
    const targetGates = filterGatesByTiming(allGates, timing);
    const results: QualityGateResult[] = [];

    for (const gate of targetGates) {
      const result = await this.executeGate(gate, context);
      results.push(result);

      if (!result.passed && !this.config.continueOnFailure) {
        break;
      }
    }

    const duration = Date.now() - startTime;
    const aggregated = this.aggregateResults(results, targetGates);

    return Object.freeze({
      phase,
      timing,
      results,
      allPassed: aggregated.allPassed,
      mandatoryPassed: aggregated.mandatoryPassed,
      summary: aggregated.summary,
      duration,
    });
  }

  /**
   * Register all extended gates to a standard QualityGateRunner
   *
   * This provides backward compatibility with existing infrastructure.
   *
   * @param standardRunner - Standard quality gate runner
   * @param contextProvider - Function that provides execution context
   */
  registerToStandardRunner(
    standardRunner: QualityGateRunner,
    contextProvider: () => GateExecutionContext
  ): void {
    for (const [_phase, gates] of this.gates) {
      for (const gate of gates) {
        const standardGate = toStandardGate(gate, contextProvider);
        standardRunner.registerGate(standardGate);
      }
    }
  }

  /**
   * Execute a single extended gate
   */
  private async executeGate(
    gate: ExtendedQualityGate,
    context: GateExecutionContext
  ): Promise<QualityGateResult> {
    const startTime = Date.now();

    try {
      const result = await this.executeWithTimeout(gate, context);
      const duration = Date.now() - startTime;

      return Object.freeze({
        gateId: gate.id,
        gateName: gate.name,
        results: [result],
        passed: result.passed,
        executedAt: new Date(),
        duration,
      });
    } catch (error) {
      const duration = Date.now() - startTime;
      const errorMessage = error instanceof Error ? error.message : String(error);

      return Object.freeze({
        gateId: gate.id,
        gateName: gate.name,
        results: [
          {
            passed: false,
            message: `Gate execution failed: ${errorMessage}`,
            severity: 'error' as const,
          },
        ],
        passed: false,
        executedAt: new Date(),
        duration,
      });
    }
  }

  /**
   * Execute gate with timeout
   */
  private async executeWithTimeout(
    gate: ExtendedQualityGate,
    context: GateExecutionContext
  ): Promise<QualityCheckResult> {
    return new Promise<QualityCheckResult>((resolve, reject) => {
      const timeout = setTimeout(() => {
        reject(new Error(`Gate '${gate.name}' timed out after ${this.config.gateTimeout}ms`));
      }, this.config.gateTimeout);

      gate
        .check(context)
        .then((result) => {
          clearTimeout(timeout);
          resolve(result);
        })
        .catch((error) => {
          clearTimeout(timeout);
          reject(error);
        });
    });
  }

  /**
   * Aggregate results from multiple gates
   */
  private aggregateResults(
    results: readonly QualityGateResult[],
    gates: readonly ExtendedQualityGate[]
  ): {
    allPassed: boolean;
    mandatoryPassed: boolean;
    summary: string;
  } {
    if (results.length === 0) {
      return {
        allPassed: true,
        mandatoryPassed: true,
        summary: 'No gates to run',
      };
    }

    const allPassed = results.every((r) => r.passed);

    // Check mandatory gates only
    const mandatoryGates = gates.filter((g) => g.mandatory);
    const mandatoryResults = results.filter((r) =>
      mandatoryGates.some((g) => g.id === r.gateId)
    );
    const mandatoryPassed = mandatoryResults.every((r) => r.passed);

    const passedCount = results.filter((r) => r.passed).length;
    const summary = `${passedCount}/${results.length} gates passed`;

    return {
      allPassed,
      mandatoryPassed,
      summary,
    };
  }
}

/**
 * Create a pre-configured ExtendedQualityGateRunner instance
 *
 * @param config - Optional configuration
 * @returns ExtendedQualityGateRunner instance
 */
export function createExtendedQualityGateRunner(
  config?: ExtendedQualityGateRunnerConfig
): ExtendedQualityGateRunner {
  return new ExtendedQualityGateRunner(config);
}
