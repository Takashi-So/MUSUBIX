/**
 * QualityGate Entity
 * 
 * Represents a quality gate that must pass before phase transition
 * 
 * @see REQ-ORCH-003 - Quality Gate Integration
 * @see DES-ORCH-003 - QualityGateRunner
 */

import type { PhaseType } from '../value-objects/index.js';

/**
 * Quality gate check function type
 */
export type QualityCheckFn = () => Promise<QualityCheckResult>;

/**
 * Quality check result
 */
export interface QualityCheckResult {
  readonly passed: boolean;
  readonly message: string;
  readonly details?: string;
  readonly severity: 'error' | 'warning' | 'info';
}

/**
 * Quality gate definition
 */
export interface QualityGate {
  readonly id: string;
  readonly name: string;
  readonly phase: PhaseType;
  readonly description: string;
  readonly mandatory: boolean;
  readonly check: QualityCheckFn;
}

/**
 * Quality gate execution result
 */
export interface QualityGateResult {
  readonly gateId: string;
  readonly gateName: string;
  readonly results: QualityCheckResult[];
  readonly passed: boolean;
  readonly executedAt: Date;
  readonly duration: number; // ms
}

/**
 * Create a quality gate
 * 
 * @param params - Gate parameters
 * @returns QualityGate
 */
export function createQualityGate(params: {
  id: string;
  name: string;
  phase: PhaseType;
  description: string;
  mandatory?: boolean;
  check: QualityCheckFn;
}): QualityGate {
  return Object.freeze({
    id: params.id,
    name: params.name,
    phase: params.phase,
    description: params.description,
    mandatory: params.mandatory ?? true,
    check: params.check,
  });
}

/**
 * Execute a quality gate
 * 
 * @param gate - Quality gate to execute
 * @returns Execution result
 */
export async function executeQualityGate(gate: QualityGate): Promise<QualityGateResult> {
  const startTime = Date.now();
  
  try {
    const result = await gate.check();
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
      results: [{
        passed: false,
        message: `Gate execution failed: ${errorMessage}`,
        severity: 'error' as const,
      }],
      passed: false,
      executedAt: new Date(),
      duration,
    });
  }
}

/**
 * Aggregate quality gate results
 * 
 * @param results - Array of gate results
 * @returns Aggregated status
 */
export function aggregateGateResults(results: QualityGateResult[]): {
  allPassed: boolean;
  mandatoryPassed: boolean;
  summary: string;
} {
  const mandatoryResults = results; // All results are from mandatory gates
  const allPassed = results.every(r => r.passed);
  const mandatoryPassed = mandatoryResults.every(r => r.passed);
  
  const passedCount = results.filter(r => r.passed).length;
  const summary = `${passedCount}/${results.length} gates passed`;
  
  return {
    allPassed,
    mandatoryPassed,
    summary,
  };
}

// Pre-defined quality gates for each phase
export const PHASE_QUALITY_GATES: ReadonlyMap<PhaseType, readonly string[]> = new Map([
  ['requirements', [
    'EARS形式の検証',
    '優先度設定の確認',
    '既存要件との整合性',
  ]],
  ['design', [
    'トレーサビリティ (REQ → DES)',
    '型整合性',
    '設計パターン適用',
  ]],
  ['task-breakdown', [
    'トレーサビリティ (DES → TSK)',
    'タスクサイズの適切性',
    '依存関係の妥当性',
  ]],
  ['implementation', [
    'ユニットテスト合格',
    '型チェック合格',
    'リントエラーなし',
  ]],
  ['completion', [
    'CHANGELOG更新',
    'ドキュメント更新',
    'コミット準備完了',
  ]],
]);

/**
 * Get quality gate checks for a phase
 * 
 * @param phase - Phase type
 * @returns Gate check names
 */
export function getPhaseGateChecks(phase: PhaseType): readonly string[] {
  return PHASE_QUALITY_GATES.get(phase) ?? [];
}
