/**
 * ConversationDomain Value Object
 *
 * Classifies conversations into four domains based on research paper findings
 *
 * @see REQ-AA-DRIFT-002 - Domain classification
 * @see REQ-AA-DRIFT-005 - Safe domain detection
 * @see arXiv:2601.10387 Section 4.1, Figure 7
 */

/**
 * Domain types based on research paper categories
 *
 * - coding: Technical questions, bounded tasks, how-to
 * - writing: Editing, improvement, technical documentation
 * - therapy: Emotional disclosure, vulnerability expression
 * - philosophy: AI consciousness, meta-reflection, self-awareness
 */
export type DomainType = 'coding' | 'writing' | 'therapy' | 'philosophy';

/**
 * Conversation Domain Value Object
 */
export interface ConversationDomain {
  /** Domain type */
  readonly type: DomainType;
  /** Classification confidence (0.0 - 1.0) */
  readonly confidence: number;
  /** Whether this domain is safe (low drift risk) */
  readonly isSafe: boolean;
}

/**
 * Domain safety mapping based on research findings
 *
 * From arXiv:2601.10387:
 * "Coding and writing tasks keep models firmly in Assistant territory throughout"
 *
 * @see REQ-AA-DRIFT-005
 */
export const DOMAIN_SAFETY: Readonly<Record<DomainType, boolean>> = {
  coding: true, // Safe - keeps model in Assistant territory
  writing: true, // Safe - keeps model in Assistant territory
  therapy: false, // Risky - causes drift toward character personas
  philosophy: false, // Risky - causes drift due to meta-reflection
};

/**
 * Domain descriptions for documentation
 */
export const DOMAIN_DESCRIPTIONS: Readonly<Record<DomainType, string>> = {
  coding:
    'Technical programming questions, code review, debugging, API usage',
  writing:
    'Document editing, technical writing, content improvement',
  therapy:
    'Emotional support, personal advice, vulnerability discussions',
  philosophy:
    'AI consciousness, existential questions, meta-reflection about AI nature',
};

/**
 * Validation error for ConversationDomain
 */
export class DomainValidationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'DomainValidationError';
  }
}

/**
 * Result type for ConversationDomain creation
 */
export type DomainResult =
  | { readonly ok: true; readonly value: ConversationDomain }
  | { readonly ok: false; readonly error: DomainValidationError };

/**
 * Create a ConversationDomain value object
 *
 * @param type - Domain type
 * @param confidence - Classification confidence (0.0 - 1.0)
 * @returns Result containing ConversationDomain or validation error
 *
 * @example
 * ```typescript
 * const result = createConversationDomain('coding', 0.92);
 * if (result.ok) {
 *   console.log(result.value.isSafe); // true
 * }
 * ```
 */
export function createConversationDomain(
  type: DomainType,
  confidence: number
): DomainResult {
  // Validate confidence range
  if (confidence < 0.0 || confidence > 1.0) {
    return {
      ok: false,
      error: new DomainValidationError(
        `Confidence must be between 0.0 and 1.0, got ${confidence}`
      ),
    };
  }

  if (!Number.isFinite(confidence)) {
    return {
      ok: false,
      error: new DomainValidationError(
        `Confidence must be a finite number, got ${confidence}`
      ),
    };
  }

  return {
    ok: true,
    value: {
      type,
      confidence,
      isSafe: DOMAIN_SAFETY[type],
    },
  };
}

/**
 * Check if a domain is safe (coding or writing)
 */
export function isSafeDomain(domain: ConversationDomain): boolean {
  return domain.isSafe;
}

/**
 * Check if a domain is risky (therapy or philosophy)
 */
export function isRiskyDomain(domain: ConversationDomain): boolean {
  return !domain.isSafe;
}

/**
 * Get all domain types
 */
export function getAllDomainTypes(): readonly DomainType[] {
  return ['coding', 'writing', 'therapy', 'philosophy'] as const;
}

/**
 * Get safe domain types
 */
export function getSafeDomainTypes(): readonly DomainType[] {
  return ['coding', 'writing'] as const;
}

/**
 * Get risky domain types
 */
export function getRiskyDomainTypes(): readonly DomainType[] {
  return ['therapy', 'philosophy'] as const;
}
