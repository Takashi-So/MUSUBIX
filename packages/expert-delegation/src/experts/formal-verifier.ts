/**
 * @nahisaho/musubix-expert-delegation
 * Formal Verifier Expert (MUSUBIX独自)
 *
 * DES-EXP-004
 * Traces to: REQ-EXP-004
 */

import type { Expert } from '../types/index.js';

/**
 * Formal Verifier Expert
 *
 * 形式検証を行うMUSUBIX独自のエキスパート。
 * Z3およびLean4との連携をサポート。
 */
export const formalVerifierExpert: Expert = {
  type: 'formal-verifier',
  name: 'Formal Verifier Expert',
  description:
    '形式検証、数学的証明、仕様からの自動検証を行います。Z3 SMTソルバーおよびLean 4定理証明器をサポートします。',

  systemPrompt: `You are a formal verification expert specializing in:
- SMT solving (Z3)
- Theorem proving (Lean 4)
- Hoare logic and program verification
- Contract-based design
- Model checking
- Property-based testing

Tools you can help with:
1. Z3 SMT Solver:
   - Satisfiability checking
   - Constraint solving
   - Integer/real arithmetic
   - Bitvector operations

2. Lean 4:
   - Theorem proving
   - Dependent type programming
   - Mathematical proofs
   - Program verification

When verifying:
1. Identify properties to verify (pre/post conditions, invariants)
2. Formalize the specification
3. Generate verification conditions
4. Apply appropriate solver/prover
5. Report verification results

EARS to SMT translation:
- UBIQUITOUS → Global invariant assertion
- EVENT-DRIVEN → Pre/post condition pair
- STATE-DRIVEN → State-dependent assertion
- UNWANTED → Negated assertion (unreachability)

Output format:
- Property: [description]
- Formalization: [Z3/Lean code]
- Result: VERIFIED | FAILED | UNKNOWN
- Counterexample: [if failed]`,

  triggers: [
    { pattern: 'formal verification', language: 'en', priority: 90 },
    { pattern: 'prove', language: 'en', priority: 70 },
    { pattern: 'verify', language: 'en', priority: 60 },
    { pattern: 'Z3', language: 'any', priority: 85 },
    { pattern: 'Lean', language: 'any', priority: 85 },
    { pattern: 'SMT', language: 'any', priority: 80 },
    { pattern: '形式検証', language: 'ja', priority: 90 },
    { pattern: '証明', language: 'ja', priority: 70 },
    { pattern: '検証', language: 'ja', priority: 50 },
  ],

  ontologyClass: 'sdd:FormalVerifier',

  capabilities: [
    {
      name: 'formalize',
      mode: 'advisory',
      description: '仕様の形式化',
    },
    {
      name: 'verify',
      mode: 'advisory',
      description: 'Z3/Lean4による検証',
    },
    {
      name: 'generate',
      mode: 'implementation',
      description: '検証コード生成',
    },
  ],
};
