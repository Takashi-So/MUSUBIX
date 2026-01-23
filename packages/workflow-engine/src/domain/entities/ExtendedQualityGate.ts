/**
 * ExtendedQualityGate Entity
 *
 * Extended quality gate with timing and context support for FastRender features.
 * Provides compatibility with existing QualityGate interface via toStandardGate().
 *
 * @see TSK-FR-053 - ExtendedQualityGate型定義
 * @see TSK-FR-054 - toStandardGate関数
 * @see REQ-FR-020〜023 - NonNegotiablesEngine
 * @see REQ-FR-040〜041 - TriageEngine
 * @see REQ-FR-080〜082 - EvidenceLevelValidator
 * @trace DES-MUSUBIX-FR-001 Section 3.3
 */

import type { PhaseType } from '../value-objects/index.js';
import type { QualityGate, QualityCheckResult, PhaseArtifact } from './index.js';

// ============================================================================
// Service Interfaces (forward declarations for dependency injection)
// ============================================================================

/**
 * Triage Engine interface
 * @see REQ-FR-040〜041 - TriageEngine
 */
export interface ITriageEngine {
  checkPriorityBlocking(): Promise<QualityCheckResult>;
}

/**
 * Non-Negotiables Engine interface
 * @see REQ-FR-020〜023 - NonNegotiablesEngine
 */
export interface INonNegotiablesEngine {
  validateDesignArtifacts(artifacts: readonly PhaseArtifact[]): Promise<{
    passed: boolean;
    violations: readonly { rule: string; message: string }[];
  }>;
  validateImplementation(changedFiles: readonly string[]): Promise<{
    passed: boolean;
    violations: readonly { rule: string; message: string }[];
  }>;
}

/**
 * Evidence Level Validator interface
 * @see REQ-FR-080〜082 - EvidenceLevelValidator
 */
export interface IEvidenceLevelValidator {
  validateEvidence(artifacts: readonly PhaseArtifact[]): Promise<QualityCheckResult>;
}

/**
 * Balance Rule Engine interface
 * @see REQ-FR-001〜003 - BalanceRuleEngine
 */
export interface IBalanceRuleEngine {
  evaluateBalance(tasks: readonly unknown[]): Promise<QualityCheckResult>;
}

/**
 * Test Placement Validator interface
 * @see REQ-FR-070〜071 - TestPlacementValidator
 */
export interface ITestPlacementValidator {
  validatePlacement(changedFiles: readonly string[]): Promise<QualityCheckResult>;
}

// ============================================================================
// Types
// ============================================================================

/**
 * Gate execution timing
 * - 'entry': Executed at phase start (ENTRY_GATE layer)
 * - 'exit': Executed at phase completion (EXIT_GATE layer)
 *
 * @trace DES-MUSUBIX-FR-001 Section 3.3.1
 */
export type GateTiming = 'entry' | 'exit';

/**
 * Services available to gates for dependency injection
 *
 * @trace DES-MUSUBIX-FR-001 Section 3.3.1
 */
export interface GateServices {
  readonly triageEngine?: ITriageEngine;
  readonly nonNegotiablesEngine?: INonNegotiablesEngine;
  readonly evidenceLevelValidator?: IEvidenceLevelValidator;
  readonly balanceRuleEngine?: IBalanceRuleEngine;
  readonly testPlacementValidator?: ITestPlacementValidator;
}

/**
 * Task type for completion phase validation
 */
export interface Task {
  readonly id: string;
  readonly title: string;
  readonly status?: string;
}

/**
 * Gate execution context
 * Provides runtime information to extended quality gates
 *
 * @trace DES-MUSUBIX-FR-001 Section 3.3.1
 */
export interface GateExecutionContext {
  /** Workflow ID */
  readonly workflowId: string;
  /** Current phase */
  readonly phase: PhaseType;
  /** Phase artifacts */
  readonly artifacts: readonly PhaseArtifact[];
  /** Changed files (for Phase 4) */
  readonly changedFiles?: readonly string[];
  /** Tasks (for Phase 5) */
  readonly tasks?: readonly Task[];
  /** Service dependencies */
  readonly services: GateServices;
}

/**
 * Extended quality check function type
 * Takes execution context as parameter
 */
export type ExtendedQualityCheckFn = (
  context: GateExecutionContext
) => Promise<QualityCheckResult>;

/**
 * Extended Quality Gate interface
 * Adds timing and context-aware check function to base QualityGate
 *
 * @trace DES-MUSUBIX-FR-001 Section 3.3.1
 */
export interface ExtendedQualityGate {
  /** Gate ID */
  readonly id: string;
  /** Gate name */
  readonly name: string;
  /** Target phase */
  readonly phase: PhaseType;
  /** Description */
  readonly description: string;
  /** Mandatory flag */
  readonly mandatory: boolean;
  /** Execution timing (entry: phase start, exit: phase completion) */
  readonly timing: GateTiming;
  /** Context-aware check function */
  readonly check: ExtendedQualityCheckFn;
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create an extended quality gate
 *
 * @param params - Gate parameters
 * @returns Immutable ExtendedQualityGate
 *
 * @example
 * ```typescript
 * const gate = createExtendedGate({
 *   id: 'gate-triage-requirements',
 *   name: 'Requirements Triage',
 *   phase: 'requirements',
 *   description: 'Block new requirements if P0/P1 tasks are unresolved',
 *   timing: 'entry',
 *   check: async (ctx) => ctx.services.triageEngine?.checkPriorityBlocking()
 *     ?? { passed: true, message: 'No triage engine', severity: 'info' },
 * });
 * ```
 *
 * @trace DES-MUSUBIX-FR-001 Section 3.3.1
 */
export function createExtendedGate(params: {
  id: string;
  name: string;
  phase: PhaseType;
  description: string;
  mandatory?: boolean;
  timing: GateTiming;
  check: ExtendedQualityCheckFn;
}): ExtendedQualityGate {
  return Object.freeze({
    id: params.id,
    name: params.name,
    phase: params.phase,
    description: params.description,
    mandatory: params.mandatory ?? true,
    timing: params.timing,
    check: params.check,
  });
}

// ============================================================================
// Conversion Functions
// ============================================================================

/**
 * Convert an extended gate to a standard QualityGate
 *
 * This maintains backward compatibility with existing QualityGateRunner.
 * The context provider is called at check execution time.
 *
 * @param extended - Extended quality gate
 * @param contextProvider - Function that provides execution context
 * @returns Standard QualityGate compatible with QualityGateRunner
 *
 * @example
 * ```typescript
 * const standardGate = toStandardGate(extendedGate, () => ({
 *   workflowId: workflow.id,
 *   phase: workflow.currentPhase,
 *   artifacts: workflow.artifacts,
 *   services: { triageEngine },
 * }));
 *
 * runner.registerGate(standardGate);
 * ```
 *
 * @trace DES-MUSUBIX-FR-001 Section 3.3.1
 */
export function toStandardGate(
  extended: ExtendedQualityGate,
  contextProvider: () => GateExecutionContext
): QualityGate {
  return Object.freeze({
    id: extended.id,
    name: extended.name,
    phase: extended.phase,
    description: extended.description,
    mandatory: extended.mandatory,
    check: async (): Promise<QualityCheckResult> => {
      const context = contextProvider();
      return extended.check(context);
    },
  });
}

// ============================================================================
// Type Guards
// ============================================================================

/**
 * Check if gate is an entry gate
 *
 * @param gate - Extended quality gate
 * @returns true if gate timing is 'entry'
 */
export function isEntryGate(gate: ExtendedQualityGate): boolean {
  return gate.timing === 'entry';
}

/**
 * Check if gate is an exit gate
 *
 * @param gate - Extended quality gate
 * @returns true if gate timing is 'exit'
 */
export function isExitGate(gate: ExtendedQualityGate): boolean {
  return gate.timing === 'exit';
}

/**
 * Filter gates by timing
 *
 * @param gates - Array of extended gates
 * @param timing - Target timing
 * @returns Filtered gates
 */
export function filterGatesByTiming(
  gates: readonly ExtendedQualityGate[],
  timing: GateTiming
): readonly ExtendedQualityGate[] {
  return gates.filter((gate) => gate.timing === timing);
}

/**
 * Filter gates by phase
 *
 * @param gates - Array of extended gates
 * @param phase - Target phase
 * @returns Filtered gates
 */
export function filterGatesByPhase(
  gates: readonly ExtendedQualityGate[],
  phase: PhaseType
): readonly ExtendedQualityGate[] {
  return gates.filter((gate) => gate.phase === phase);
}
