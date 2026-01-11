/**
 * PhaseType Value Object
 * 
 * Represents the workflow phase type
 * 
 * @see REQ-ORCH-001 - Phase Transition
 * @see DES-ORCH-001 - PhaseController
 */

/**
 * Phase type enum
 */
export type PhaseType =
  | 'requirements'    // Phase 1
  | 'design'          // Phase 2
  | 'task-breakdown'  // Phase 3
  | 'implementation'  // Phase 4
  | 'completion';     // Phase 5

/**
 * Phase metadata
 */
export interface PhaseMetadata {
  readonly type: PhaseType;
  readonly number: number;
  readonly label: string;
  readonly description: string;
}

/**
 * Phase definitions
 */
export const PHASES: ReadonlyMap<PhaseType, PhaseMetadata> = new Map([
  ['requirements', {
    type: 'requirements',
    number: 1,
    label: 'Phase 1: 要件定義',
    description: 'EARS形式で要件を定義',
  }],
  ['design', {
    type: 'design',
    number: 2,
    label: 'Phase 2: 設計',
    description: 'C4モデルで設計を作成',
  }],
  ['task-breakdown', {
    type: 'task-breakdown',
    number: 3,
    label: 'Phase 3: タスク分解',
    description: '設計からタスクを分解',
  }],
  ['implementation', {
    type: 'implementation',
    number: 4,
    label: 'Phase 4: 実装',
    description: 'タスクに基づいて実装',
  }],
  ['completion', {
    type: 'completion',
    number: 5,
    label: 'Phase 5: 完了',
    description: 'ドキュメント更新・コミット',
  }],
]);

/**
 * Valid phase transitions
 * NOTE: Phase 2 → Phase 4 direct transition is PROHIBITED
 */
export const VALID_TRANSITIONS: ReadonlyMap<PhaseType, readonly PhaseType[]> = new Map([
  ['requirements', ['design']],
  ['design', ['task-breakdown']],        // Phase 2 can ONLY go to Phase 3
  ['task-breakdown', ['implementation']], // Phase 3 → Phase 4
  ['implementation', ['completion']],
  ['completion', []],
]);

/**
 * Get phase metadata
 * 
 * @param type - Phase type
 * @returns Phase metadata
 */
export function getPhaseMetadata(type: PhaseType): PhaseMetadata {
  const metadata = PHASES.get(type);
  if (!metadata) {
    throw new Error(`Invalid phase type: ${type}`);
  }
  return metadata;
}

/**
 * Get valid transitions from a phase
 * 
 * @param from - Source phase
 * @returns Valid target phases
 */
export function getValidTransitions(from: PhaseType): readonly PhaseType[] {
  return VALID_TRANSITIONS.get(from) ?? [];
}

/**
 * Check if transition is valid
 * 
 * @param from - Source phase
 * @param to - Target phase
 * @returns true if valid
 */
export function isValidTransition(from: PhaseType, to: PhaseType): boolean {
  const validTargets = VALID_TRANSITIONS.get(from);
  return validTargets?.includes(to) ?? false;
}

/**
 * Get phase number
 * 
 * @param type - Phase type
 * @returns Phase number (1-5)
 */
export function getPhaseNumber(type: PhaseType): number {
  return getPhaseMetadata(type).number;
}

/**
 * Get all phase types in order
 * 
 * @returns Ordered phase types
 */
export function getAllPhases(): PhaseType[] {
  return ['requirements', 'design', 'task-breakdown', 'implementation', 'completion'];
}
