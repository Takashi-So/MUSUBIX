/**
 * @fileoverview EARS to Lean converter
 * @module @nahisaho/musubix-lean/converters
 * @traceability REQ-LEAN-CONV-001 to REQ-LEAN-CONV-005
 */

import { ok, err, type Result } from 'neverthrow';
import type {
  EarsRequirement,
  EarsPattern,
  EarsParsedComponents,
  LeanTheorem,
  LeanHypothesis,
  LeanExpression,
} from '../types.js';
import { EarsConversionError, EarsParseError } from '../errors.js';

/**
 * EARS pattern regex definitions
 */
const EARS_PATTERNS = {
  ubiquitous: /^THE\s+(.+?)\s+SHALL\s+(.+)$/i,
  eventDriven: /^WHEN\s+(.+?),?\s+THE\s+(.+?)\s+SHALL\s+(.+)$/i,
  stateDriven: /^WHILE\s+(.+?),?\s+THE\s+(.+?)\s+SHALL\s+(.+)$/i,
  unwanted: /^THE\s+(.+?)\s+SHALL\s+NOT\s+(.+)$/i,
  optional: /^IF\s+(.+?),?\s+THEN\s+THE\s+(.+?)\s+SHALL\s+(.+)$/i,
};

/**
 * Parse EARS requirement text into components
 * @traceability REQ-LEAN-CONV-001
 */
export function parseEarsRequirement(
  text: string
): Result<EarsParsedComponents, EarsParseError> {
  const trimmedText = text.trim();

  // Try Unwanted pattern first (SHALL NOT before SHALL)
  const unwantedMatch = trimmedText.match(EARS_PATTERNS.unwanted);
  if (unwantedMatch) {
    return ok({
      pattern: 'unwanted',
      subject: unwantedMatch[1].trim(),
      action: unwantedMatch[2].trim(),
      negated: true,
    });
  }

  // Try Event-driven pattern
  const eventMatch = trimmedText.match(EARS_PATTERNS.eventDriven);
  if (eventMatch) {
    return ok({
      pattern: 'event-driven',
      trigger: eventMatch[1].trim(),
      subject: eventMatch[2].trim(),
      action: eventMatch[3].trim(),
      negated: false,
    });
  }

  // Try State-driven pattern
  const stateMatch = trimmedText.match(EARS_PATTERNS.stateDriven);
  if (stateMatch) {
    return ok({
      pattern: 'state-driven',
      state: stateMatch[1].trim(),
      subject: stateMatch[2].trim(),
      action: stateMatch[3].trim(),
      negated: false,
    });
  }

  // Try Optional pattern
  const optionalMatch = trimmedText.match(EARS_PATTERNS.optional);
  if (optionalMatch) {
    return ok({
      pattern: 'optional',
      condition: optionalMatch[1].trim(),
      subject: optionalMatch[2].trim(),
      action: optionalMatch[3].trim(),
      negated: false,
    });
  }

  // Try Ubiquitous pattern
  const ubiquitousMatch = trimmedText.match(EARS_PATTERNS.ubiquitous);
  if (ubiquitousMatch) {
    return ok({
      pattern: 'ubiquitous',
      subject: ubiquitousMatch[1].trim(),
      action: ubiquitousMatch[2].trim(),
      negated: false,
    });
  }

  return err(
    new EarsParseError(
      text,
      'Text does not match any EARS pattern (Ubiquitous, Event-driven, State-driven, Unwanted, or Optional)'
    )
  );
}

/**
 * Convert natural language to Lean identifier
 */
function toLeanIdentifier(text: string): string {
  return text
    .toLowerCase()
    .replace(/[^a-z0-9\s]/g, '')
    .split(/\s+/)
    .filter((s) => s.length > 0)
    .map((s, i) => (i === 0 ? s : s.charAt(0).toUpperCase() + s.slice(1)))
    .join('');
}

/**
 * Convert natural language to Lean predicate name
 */
function toLeanPredicateName(text: string): string {
  const base = toLeanIdentifier(text);
  return base.charAt(0).toUpperCase() + base.slice(1);
}

/**
 * Build Lean theorem from EARS components
 * @traceability REQ-LEAN-CONV-001
 */
export function buildLeanTheorem(
  components: EarsParsedComponents,
  requirementId: string,
  sourceText: string
): LeanTheorem {
  const theoremName = `req_${requirementId.replace(/[^a-zA-Z0-9]/g, '_').toLowerCase()}`;
  const hypotheses: LeanHypothesis[] = [];
  let conclusion: LeanExpression;
  let leanCode: string;

  const subjectPred = toLeanPredicateName(components.subject);
  const actionPred = toLeanPredicateName(components.action);

  switch (components.pattern) {
    case 'ubiquitous':
      // THE [system] SHALL [requirement]
      // ∀ x, System x → Action x
      conclusion = {
        type: `∀ x, ${subjectPred} x → ${actionPred} x`,
        leanCode: `∀ x, ${subjectPred} x → ${actionPred} x`,
      };
      leanCode = `
/-- ${sourceText}
    @requirement ${requirementId}
-/
theorem ${theoremName} : ∀ x, ${subjectPred} x → ${actionPred} x := by
  intro x h_system
  sorry -- TODO: Complete proof
`;
      break;

    case 'event-driven':
      // WHEN [event], THE [system] SHALL [response]
      // event → response
      hypotheses.push({
        name: 'h_event',
        type: toLeanPredicateName(components.trigger || ''),
        leanCode: `h_event : ${toLeanPredicateName(components.trigger || '')}`,
      });
      conclusion = {
        type: actionPred,
        leanCode: actionPred,
      };
      leanCode = `
/-- ${sourceText}
    @requirement ${requirementId}
-/
theorem ${theoremName} (h_event : ${toLeanPredicateName(components.trigger || '')}) : ${actionPred} := by
  sorry -- TODO: Complete proof
`;
      break;

    case 'state-driven':
      // WHILE [state], THE [system] SHALL [response]
      // state → invariant_preserved
      hypotheses.push({
        name: 'h_state',
        type: toLeanPredicateName(components.state || ''),
        leanCode: `h_state : ${toLeanPredicateName(components.state || '')}`,
      });
      conclusion = {
        type: `${actionPred} ∧ ${toLeanPredicateName(components.state || '')}`,
        leanCode: `${actionPred} ∧ ${toLeanPredicateName(components.state || '')}`,
      };
      leanCode = `
/-- ${sourceText}
    @requirement ${requirementId}
-/
theorem ${theoremName} (h_state : ${toLeanPredicateName(components.state || '')}) : ${actionPred} ∧ ${toLeanPredicateName(components.state || '')} := by
  constructor
  · sorry -- TODO: Prove action
  · exact h_state
`;
      break;

    case 'unwanted':
      // THE [system] SHALL NOT [behavior]
      // ¬ unwanted_behavior
      conclusion = {
        type: `¬ ${actionPred}`,
        leanCode: `¬ ${actionPred}`,
      };
      leanCode = `
/-- ${sourceText}
    @requirement ${requirementId}
-/
theorem ${theoremName} : ¬ ${actionPred} := by
  intro h_unwanted
  sorry -- TODO: Derive contradiction
`;
      break;

    case 'optional':
      // IF [condition], THEN THE [system] SHALL [response]
      // condition → response
      hypotheses.push({
        name: 'h_cond',
        type: toLeanPredicateName(components.condition || ''),
        leanCode: `h_cond : ${toLeanPredicateName(components.condition || '')}`,
      });
      conclusion = {
        type: actionPred,
        leanCode: actionPred,
      };
      leanCode = `
/-- ${sourceText}
    @requirement ${requirementId}
-/
theorem ${theoremName} (h_cond : ${toLeanPredicateName(components.condition || '')}) : ${actionPred} := by
  sorry -- TODO: Complete proof
`;
      break;
  }

  return {
    id: requirementId,
    name: theoremName,
    statement: conclusion.leanCode,
    requirementId,
    hypotheses,
    conclusion,
    sourceText,
    leanCode,
  };
}

/**
 * Convert EARS requirement to Lean theorem
 * @traceability REQ-LEAN-CONV-001
 */
export function convertEarsToLean(
  requirement: EarsRequirement
): Result<LeanTheorem, EarsConversionError> {
  try {
    if (!requirement.parsed) {
      return err(
        new EarsConversionError(
          requirement.id,
          'Requirement has no parsed components'
        )
      );
    }
    const theorem = buildLeanTheorem(
      requirement.parsed,
      requirement.id,
      requirement.text
    );
    return ok(theorem);
  } catch (error) {
    return err(
      new EarsConversionError(
        requirement.id,
        error instanceof Error ? error.message : String(error)
      )
    );
  }
}

/**
 * Convert raw EARS text to Lean theorem
 */
export function convertEarsTextToLean(
  id: string,
  text: string
): Result<LeanTheorem, EarsParseError | EarsConversionError> {
  const parseResult = parseEarsRequirement(text);
  if (parseResult.isErr()) {
    return err(parseResult.error);
  }

  const requirement: EarsRequirement = {
    id,
    pattern: parseResult.value.pattern,
    text,
    parsed: parseResult.value,
  };

  return convertEarsToLean(requirement);
}

/**
 * Detect EARS pattern from text
 */
export function detectEarsPattern(text: string): EarsPattern | null {
  const result = parseEarsRequirement(text);
  return result.isOk() ? result.value.pattern : null;
}

/**
 * EarsToLeanConverter class implementation
 * @traceability REQ-LEAN-CONV-001
 */
export class EarsToLeanConverter {
  /**
   * Convert EARS requirement to Lean theorem
   */
  convert(requirement: EarsRequirement): Result<LeanTheorem, EarsConversionError> {
    return convertEarsToLean(requirement);
  }

  /**
   * Parse EARS text into components
   */
  parseEars(text: string): Result<EarsParsedComponents, EarsParseError> {
    return parseEarsRequirement(text);
  }

  /**
   * Build theorem from parsed components
   */
  buildTheorem(
    components: EarsParsedComponents,
    reqId: string,
    sourceText: string = ''
  ): LeanTheorem {
    return buildLeanTheorem(components, reqId, sourceText);
  }

  /**
   * Batch convert multiple requirements
   * @traceability REQ-LEAN-ERR-002
   */
  convertBatch(
    requirements: EarsRequirement[]
  ): { successes: LeanTheorem[]; failures: { id: string; error: string }[] } {
    const successes: LeanTheorem[] = [];
    const failures: { id: string; error: string }[] = [];

    for (const req of requirements) {
      const result = this.convert(req);
      if (result.isOk()) {
        successes.push(result.value);
      } else {
        failures.push({
          id: req.id,
          error: result.error.message,
        });
      }
    }

    return { successes, failures };
  }
}
