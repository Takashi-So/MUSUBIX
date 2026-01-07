/**
 * @fileoverview Proof generation for Lean theorems
 * @module @nahisaho/musubix-lean/proof
 * @traceability REQ-LEAN-PROOF-001 to REQ-LEAN-PROOF-003
 */

import type {
  LeanTheorem,
  LeanProof,
  LeanProofSketch,
  ProofResult,
  ProofState,
  ProofGoal,
  ProofStrategy,
  ProofOptions,
  TacticResult,
  SorryLocation,
} from '../types.js';
import { ProofTimeoutError, ProofGenerationError } from '../errors.js';

/**
 * Standard proof tactics
 * @traceability REQ-LEAN-PROOF-001
 */
const STANDARD_TACTICS = [
  'rfl',
  'decide',
  'native_decide',
  'simp',
  'trivial',
  'assumption',
  'contradiction',
  'exact h',
  'intro',
  'constructor',
];

/**
 * Induction tactics for recursive data
 * @traceability REQ-LEAN-PROOF-002
 */
const INDUCTION_TACTICS = [
  'induction',
  'cases',
  'match_hyp',
  'rcases',
];

/**
 * Default proof strategies
 */
const DEFAULT_STRATEGIES: ProofStrategy[] = [
  {
    name: 'simple',
    tactics: ['rfl', 'decide', 'trivial'],
    applicability: () => true,
  },
  {
    name: 'simplification',
    tactics: ['simp', 'simp_all', 'simp [*]'],
    applicability: () => true,
  },
  {
    name: 'assumption-based',
    tactics: ['assumption', 'exact h', 'exact h_event', 'exact h_pre_0'],
    applicability: (theorem) => theorem.hypotheses.length > 0,
  },
  {
    name: 'induction',
    tactics: ['induction n with n ih', 'cases h'],
    applicability: (theorem) =>
      (theorem.conclusion?.leanCode.includes('Nat') ?? false) ||
      (theorem.conclusion?.leanCode.includes('List') ?? false),
  },
  {
    name: 'propositional',
    tactics: ['intro', 'constructor', 'left', 'right', 'apply And.intro'],
    applicability: (theorem) =>
      (theorem.conclusion?.leanCode.includes('∧') ?? false) ||
      (theorem.conclusion?.leanCode.includes('∨') ?? false) ||
      (theorem.conclusion?.leanCode.includes('→') ?? false),
  },
];

/**
 * Create initial proof state from theorem
 */
function createInitialProofState(theorem: LeanTheorem): ProofState {
  return {
    goals: [
      {
        id: 0,
        type: theorem.conclusion?.type ?? '',
        leanCode: theorem.conclusion?.leanCode ?? '',
      },
    ],
    hypotheses: theorem.hypotheses,
    currentGoal: 0,
  };
}

/**
 * Generate proof for a Lean theorem
 * @traceability REQ-LEAN-PROOF-001
 */
export async function generateProof(
  theorem: LeanTheorem,
  options: ProofOptions = {}
): Promise<ProofResult> {
  const startTime = Date.now();
  const timeout = options.timeout ?? 30000;
  const maxTactics = options.maxTactics ?? 5;
  const strategies = options.strategies ?? DEFAULT_STRATEGIES;

  const tacticsAttempted: string[] = [];
  let proofState: ProofState = createInitialProofState(theorem);

  try {
    // Try each applicable strategy
    for (const strategy of strategies) {
      if (strategy.applicability && !strategy.applicability(theorem)) {
        continue;
      }

      // Try tactics from strategy
      for (const tactic of strategy.tactics) {
        if (tacticsAttempted.length >= maxTactics) {
          break;
        }

        if (Date.now() - startTime > timeout) {
          throw new ProofTimeoutError(theorem.name, timeout);
        }

        tacticsAttempted.push(tactic);

        // Simulate tactic application
        const result = await applyTactic(proofState, tactic);
        if (result.success && result.newState) {
          proofState = result.newState;

          // Check if proof is complete
          if (proofState.goals.length === 0) {
            const proof: LeanProof = {
              id: `proof-${theorem.id}`,
              theoremId: theorem.id,
              tactics: tacticsAttempted,
              leanCode: generateProofCode(theorem, tacticsAttempted),
              isComplete: true,
              generatedAt: new Date().toISOString(),
            };

            return {
              success: true,
              proof,
              proofState: null,
              tacticsAttempted,
              duration: Date.now() - startTime,
            };
          }
        }
      }
    }

    // Proof not found with standard tactics
    return {
      success: false,
      proof: null,
      proofState,
      tacticsAttempted,
      duration: Date.now() - startTime,
      error: 'Could not complete proof with available tactics',
    };
  } catch (error) {
    if (error instanceof ProofTimeoutError) {
      return {
        success: false,
        proof: null,
        proofState,
        tacticsAttempted,
        duration: Date.now() - startTime,
        error: error.message,
      };
    }
    throw error;
  }
}

/**
 * Apply a single tactic to proof state
 */
export async function applyTactic(
  state: ProofState,
  tactic: string
): Promise<TacticResult> {
  // This is a simplified simulation
  // In real implementation, this would call Lean via LeanRunner

  // Simulate success for certain tactics on certain goals
  const currentGoal = state.goals[state.currentGoal];
  if (!currentGoal) {
    return { success: false, newState: null, error: 'No goals' };
  }

  // Simple heuristics for tactic success
  const goalCode = currentGoal.leanCode.toLowerCase();

  if (tactic === 'rfl' && goalCode.includes('=')) {
    // rfl succeeds on reflexive equality
    return {
      success: true,
      newState: {
        ...state,
        goals: state.goals.filter((_, i) => i !== state.currentGoal),
      },
    };
  }

  if (tactic === 'trivial' && goalCode === 'true') {
    return {
      success: true,
      newState: {
        ...state,
        goals: state.goals.filter((_, i) => i !== state.currentGoal),
      },
    };
  }

  if (tactic === 'assumption' && state.hypotheses.length > 0) {
    // Check if any hypothesis matches the goal
    const matchingHyp = state.hypotheses.find(
      (h) => h.type.toLowerCase() === goalCode
    );
    if (matchingHyp) {
      return {
        success: true,
        newState: {
          ...state,
          goals: state.goals.filter((_, i) => i !== state.currentGoal),
        },
      };
    }
  }

  // Default: tactic doesn't change state
  return {
    success: false,
    newState: null,
    error: `Tactic '${tactic}' did not make progress`,
  };
}

/**
 * Generate Lean proof code
 */
function generateProofCode(theorem: LeanTheorem, tactics: string[]): string {
  const tacticBlock = tactics.length > 0
    ? tactics.map((t) => `  ${t}`).join('\n')
    : '  sorry';

  return `
theorem ${theorem.name} : ${theorem.conclusion?.leanCode ?? 'True'} := by
${tacticBlock}
`;
}

/**
 * Generate proof sketch with sorry markers
 * @traceability REQ-LEAN-PROOF-003
 */
export function generateProofSketch(
  theorem: LeanTheorem,
  partialTactics: string[] = []
): LeanProofSketch {
  const sorryLocations: SorryLocation[] = [];
  const hints: string[] = [];
  let completionRate = 0;

  // Analyze theorem to provide hints
  const conclusion = theorem.conclusion?.leanCode ?? '';

  if (conclusion.includes('∧')) {
    hints.push('Use "constructor" to split conjunction');
    hints.push('Prove each side separately');
  }

  if (conclusion.includes('→')) {
    hints.push('Use "intro" to introduce hypothesis');
  }

  if (conclusion.includes('∀')) {
    hints.push('Use "intro" to introduce universally quantified variable');
  }

  if (conclusion.includes('¬')) {
    hints.push('Use "intro h_unwanted" and derive contradiction');
  }

  // Build partial proof with sorry
  const tacticBlock = partialTactics.length > 0
    ? partialTactics.map((t) => `  ${t}`).join('\n') + '\n  sorry'
    : '  sorry';

  sorryLocations.push({
    line: partialTactics.length + 2,
    expectedType: conclusion,
    hint: hints[0] || 'Complete the proof',
  });

  const partialProof = `
theorem ${theorem.name} : ${conclusion} := by
${tacticBlock}
`;

  // Calculate completion rate (simplified)
  completionRate = partialTactics.length > 0 ? partialTactics.length * 20 : 0;
  completionRate = Math.min(completionRate, 80); // Max 80% without verification

  return {
    theoremName: theorem.name,
    partialProof,
    sorryLocations,
    hints,
    completionRate,
  };
}

/**
 * Select best strategy for theorem
 */
export function selectStrategy(
  theorem: LeanTheorem,
  strategies: ProofStrategy[] = DEFAULT_STRATEGIES
): ProofStrategy {
  // Find first applicable strategy
  for (const strategy of strategies) {
    if (strategy.applicability && strategy.applicability(theorem)) {
      return strategy;
    }
  }

  // Default to simple strategy
  return strategies[0];
}

/**
 * ProofGenerator class implementation
 * @traceability REQ-LEAN-PROOF-001
 */
export class ProofGenerator {
  private strategies: ProofStrategy[];

  constructor(strategies: ProofStrategy[] = DEFAULT_STRATEGIES) {
    this.strategies = strategies;
  }

  /**
   * Generate proof for theorem
   */
  async generate(
    theorem: LeanTheorem,
    options?: ProofOptions
  ): Promise<ProofResult> {
    return generateProof(theorem, {
      ...options,
      strategies: options?.strategies ?? this.strategies,
    });
  }

  /**
   * Apply single tactic
   */
  async applyTactic(state: ProofState, tactic: string): Promise<TacticResult> {
    return applyTactic(state, tactic);
  }

  /**
   * Generate proof sketch
   */
  generateSketch(
    theorem: LeanTheorem,
    partialTactics?: string[]
  ): LeanProofSketch {
    return generateProofSketch(theorem, partialTactics);
  }

  /**
   * Select best strategy
   */
  selectStrategy(theorem: LeanTheorem): ProofStrategy {
    return selectStrategy(theorem, this.strategies);
  }

  /**
   * Add custom strategy
   */
  addStrategy(strategy: ProofStrategy): void {
    this.strategies.push(strategy);
  }
}
