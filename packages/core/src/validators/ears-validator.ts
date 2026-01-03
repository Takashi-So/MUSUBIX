/**
 * EARS Validator
 * 
 * Validates requirements against EARS (Easy Approach to Requirements Syntax) patterns
 * 
 * @packageDocumentation
 * @module validators/ears-validator
 * 
 * @see REQ-RA-001 - EARS Pattern Recognition
 * @see Article II - Requirements First
 */

/**
 * Validation issue
 */
export interface ValidationIssue {
  /** Issue code (same as ruleId) */
  code?: string;
  /** Rule ID */
  ruleId?: string;
  /** Issue message */
  message: string;
  /** Severity */
  severity: 'error' | 'warning' | 'info';
  /** Location if applicable */
  location?: string;
}

/**
 * EARS Pattern types
 */
export type EARSPatternType =
  | 'ubiquitous'     // The <system> shall <action>
  | 'event-driven'   // When <trigger>, the <system> shall <action>
  | 'state-driven'   // While <state>, the <system> shall <action>
  | 'unwanted'       // If <condition>, then the <system> shall <action>
  | 'optional'       // Where <feature>, the <system> shall <action>
  | 'complex';       // Combination of patterns

/**
 * EARS Pattern match
 */
export interface EARSPatternMatch {
  /** Pattern type */
  type: EARSPatternType;
  /** Match confidence (0-1) */
  confidence: number;
  /** Extracted components */
  components: EARSComponents;
  /** Original text */
  original: string;
  /** Suggested rewrite (if needed) */
  suggestion?: string;
}

/**
 * EARS Components extracted from requirement
 */
export interface EARSComponents {
  /** System or actor */
  system?: string;
  /** Trigger condition (event-driven) */
  trigger?: string;
  /** State condition (state-driven) */
  state?: string;
  /** Precondition (unwanted behavior) */
  condition?: string;
  /** Feature flag (optional) */
  feature?: string;
  /** Action/behavior */
  action?: string;
  /** Response/result */
  response?: string;
}

/**
 * EARS validation options
 */
export interface EARSValidatorOptions {
  /** Minimum confidence threshold */
  confidenceThreshold: number;
  /** Allow complex patterns */
  allowComplex: boolean;
  /** Strict mode (require exact pattern match) */
  strictMode: boolean;
  /** Suggest rewrites for non-conforming requirements */
  suggestRewrites: boolean;
}

/**
 * Default validation options
 */
export const DEFAULT_EARS_OPTIONS: EARSValidatorOptions = {
  confidenceThreshold: 0.7,
  allowComplex: true,
  strictMode: false,
  suggestRewrites: true,
};

/**
 * EARS Pattern definitions with regex
 */
interface PatternDefinition {
  type: EARSPatternType;
  regex: RegExp;
  extract: (match: RegExpMatchArray) => EARSComponents;
  description: string;
}

/**
 * Pattern definitions for EARS
 * 
 * IMPORTANT: Order matters! More specific patterns (with keywords like WHEN, WHILE, IF)
 * must come BEFORE the generic ubiquitous pattern to ensure correct pattern matching.
 */
const EARS_PATTERNS: PatternDefinition[] = [
  // Event-driven: WHEN <trigger>, THE <system> SHALL <action>
  {
    type: 'event-driven',
    regex: /^when\s+(.+?),?\s+(?:the\s+)?(.+?)\s+shall\s+(.+)$/i,
    extract: (match) => ({
      trigger: match[1]?.trim(),
      system: match[2]?.trim(),
      action: match[3]?.trim(),
    }),
    description: 'When <trigger>, the <system> shall <action>',
  },
  // State-driven: WHILE <state>, THE <system> SHALL <action>
  {
    type: 'state-driven',
    regex: /^while\s+(.+?),?\s+(?:the\s+)?(.+?)\s+shall\s+(.+)$/i,
    extract: (match) => ({
      state: match[1]?.trim(),
      system: match[2]?.trim(),
      action: match[3]?.trim(),
    }),
    description: 'While <state>, the <system> shall <action>',
  },
  // Unwanted behavior (negation): THE <system> SHALL NOT <behavior>
  {
    type: 'unwanted',
    regex: /^(?:the\s+)?(.+?)\s+shall\s+not\s+(.+)$/i,
    extract: (match) => ({
      system: match[1]?.trim(),
      action: `not ${match[2]?.trim()}`,
    }),
    description: 'The <system> shall not <behavior>',
  },
  // Optional/Conditional: IF <condition>, THEN THE <system> SHALL <action>
  {
    type: 'optional',
    regex: /^if\s+(.+?),?\s+(?:then\s+)?(?:the\s+)?(.+?)\s+shall\s+(.+)$/i,
    extract: (match) => ({
      condition: match[1]?.trim(),
      system: match[2]?.trim(),
      action: match[3]?.trim(),
    }),
    description: 'If <condition>, then the <system> shall <action>',
  },
  // Optional: WHERE <feature>, THE <system> SHALL <action>
  {
    type: 'optional',
    regex: /^where\s+(.+?),?\s+(?:the\s+)?(.+?)\s+shall\s+(.+)$/i,
    extract: (match) => ({
      feature: match[1]?.trim(),
      system: match[2]?.trim(),
      action: match[3]?.trim(),
    }),
    description: 'Where <feature>, the <system> shall <action>',
  },
  // Ubiquitous (generic - must be LAST): THE <system> SHALL <action>
  {
    type: 'ubiquitous',
    regex: /^(?:the\s+)?(.+?)\s+shall\s+(.+)$/i,
    extract: (match) => ({
      system: match[1]?.trim(),
      action: match[2]?.trim(),
    }),
    description: 'The <system> shall <action>',
  },
];

/**
 * EARS Validator
 * 
 * Validates and analyzes requirements using EARS patterns
 */
export class EARSValidator {
  private options: EARSValidatorOptions;

  constructor(options?: Partial<EARSValidatorOptions>) {
    this.options = { ...DEFAULT_EARS_OPTIONS, ...options };
  }

  /**
   * Validate a single requirement
   */
  validateRequirement(requirement: string): EARSValidationResult {
    const trimmed = requirement.trim();
    
    if (!trimmed) {
      return {
        valid: false,
        patternMatch: null,
        issues: [{
          severity: 'error',
          message: 'Requirement text is empty',
          ruleId: 'ears-empty',
        }],
        suggestions: ['Provide a non-empty requirement text'],
      };
    }

    // Try to match EARS patterns
    const match = this.matchPattern(trimmed);
    
    if (match && match.confidence >= this.options.confidenceThreshold) {
      return {
        valid: true,
        patternMatch: match,
        issues: this.checkQuality(match),
        suggestions: [],
      };
    }

    // No pattern match - provide suggestions
    const issues: ValidationIssue[] = [{
      severity: this.options.strictMode ? 'error' : 'warning',
      message: 'Requirement does not match any EARS pattern',
      ruleId: 'ears-no-pattern',
    }];

    const suggestions = this.options.suggestRewrites
      ? this.generateRewrites(trimmed)
      : [];

    return {
      valid: !this.options.strictMode,
      patternMatch: match,
      issues,
      suggestions,
    };
  }

  /**
   * Validate multiple requirements
   */
  validateRequirements(requirements: string[]): EARSBatchValidationResult {
    const results = requirements.map((req, index) => ({
      index,
      requirement: req,
      result: this.validateRequirement(req),
    }));

    const valid = results.filter((r) => r.result.valid);
    const invalid = results.filter((r) => !r.result.valid);

    // Analyze pattern distribution
    const patternDistribution = this.analyzeDistribution(results);

    return {
      total: requirements.length,
      valid: valid.length,
      invalid: invalid.length,
      coverage: requirements.length > 0 ? valid.length / requirements.length : 0,
      results,
      patternDistribution,
      overallIssues: this.aggregateIssues(results),
    };
  }

  /**
   * Match requirement against EARS patterns
   * 
   * Pattern matching order:
   * 1. Complex patterns (most specific - WHEN+WHILE, IF+WHEN combinations)
   * 2. Specific patterns (event-driven, state-driven, unwanted, optional)
   * 3. Ubiquitous (most generic)
   * 
   * Performance optimization: Uses early exit when a specific pattern
   * matches with high confidence (>= 0.85). More specific patterns are
   * checked first to ensure accurate pattern detection.
   */
  private matchPattern(text: string): EARSPatternMatch | null {
    // Quick pre-check: if no "shall", skip pattern matching (except for Japanese)
    const lowerText = text.toLowerCase();
    const hasJapaneseShall = /すること|しなければならない|する$/.test(text);
    if (!lowerText.includes('shall') && !hasJapaneseShall) {
      return null;
    }

    // Check for complex patterns FIRST (most specific)
    if (this.options.allowComplex) {
      const complexMatch = this.matchComplexPattern(text);
      if (complexMatch && complexMatch.confidence >= 0.8) {
        return complexMatch;
      }
    }

    let bestMatch: EARSPatternMatch | null = null;
    let bestConfidence = 0;

    // Early exit threshold for specific patterns
    const EARLY_EXIT_THRESHOLD = 0.85;

    for (const pattern of EARS_PATTERNS) {
      const match = text.match(pattern.regex);
      if (match) {
        const components = pattern.extract(match);
        const confidence = this.calculateConfidence(components, pattern.type);
        
        // Early exit: if we find a specific pattern with high confidence, return immediately
        // This avoids checking the generic ubiquitous pattern when a specific pattern matches well
        if (pattern.type !== 'ubiquitous' && confidence >= EARLY_EXIT_THRESHOLD) {
          return {
            type: pattern.type,
            confidence,
            components,
            original: text,
          };
        }
        
        if (confidence > bestConfidence) {
          bestConfidence = confidence;
          bestMatch = {
            type: pattern.type,
            confidence,
            components,
            original: text,
          };
        }
      }
    }

    return bestMatch;
  }

  /**
   * Match complex (combined) patterns
   * Supports both English and Japanese multiline/combined EARS patterns
   */
  private matchComplexPattern(text: string): EARSPatternMatch | null {
    // Normalize text: remove extra whitespace and line breaks for multiline patterns
    const normalizedText = text.replace(/\s+/g, ' ').trim();
    
    // Complex component type
    type ComplexComponents = {
      trigger?: string;
      state?: string;
      condition?: string;
      system?: string;
      action?: string;
    };
    
    // Complex patterns to match:
    // 1. English: WHEN [trigger] AND WHILE [state], THE [system] SHALL [action]
    // 2. English: WHEN [trigger], AND THE [system] SHALL [action]
    // 3. Japanese: [trigger]のとき、かつ[state]の間、[system]は[action]すること
    
    const complexPatterns: Array<{
      regex: RegExp;
      extractor: (m: RegExpMatchArray) => ComplexComponents;
    }> = [
      // English: WHEN [trigger] AND WHILE [state], THE [system] SHALL [action]
      // Complex pattern combining event-driven and state-driven
      {
        regex: /^when\s+(.+?)\s+and\s+while\s+(.+?),\s*the\s+(\S+)\s+shall\s+(.+)$/i,
        extractor: (m) => ({ trigger: m[1], state: m[2], system: m[3], action: m[4] }),
      },
      // English: WHILE [state], WHEN [trigger], THE [system] SHALL [action]
      // Complex pattern combining state-driven and event-driven (reverse order)
      {
        regex: /^while\s+(.+?),\s*when\s+(.+?),\s*the\s+(\S+)\s+shall\s+(.+)$/i,
        extractor: (m) => ({ state: m[1], trigger: m[2], system: m[3], action: m[4] }),
      },
      // English: IF [condition], THEN WHEN [trigger], THE [system] SHALL [action]
      // Complex pattern combining optional and event-driven
      {
        regex: /^if\s+(.+?),\s*(?:then\s+)?when\s+(.+?),\s*the\s+(\S+)\s+shall\s+(.+)$/i,
        extractor: (m) => ({ condition: m[1], trigger: m[2], system: m[3], action: m[4] }),
      },
      // English: IF [condition], WHILE [state], THE [system] SHALL [action]
      // Complex pattern combining optional and state-driven
      {
        regex: /^if\s+(.+?),\s*(?:then\s+)?while\s+(.+?),\s*the\s+(\S+)\s+shall\s+(.+)$/i,
        extractor: (m) => ({ condition: m[1], state: m[2], system: m[3], action: m[4] }),
      },
      // Japanese: ～したとき、かつ～間、～は～すること (event+state)
      {
        regex: /(.+?)(?:した|の)(?:とき|時)[、,]\s*かつ\s*(.+?)間[、,]\s*(.+?)(?:は|が)\s*(.+?)(?:すること|する|しなければならない)$/,
        extractor: (m) => ({ trigger: m[1], state: m[2], system: m[3], action: m[4] }),
      },
      // Japanese: ～の間、かつ～のとき、～は～すること (state+event)
      {
        regex: /(.+?)間[、,]\s*かつ\s*(.+?)(?:した|の)(?:とき|時)[、,]\s*(.+?)(?:は|が)\s*(.+?)(?:すること|する|しなければならない)$/,
        extractor: (m) => ({ state: m[1], trigger: m[2], system: m[3], action: m[4] }),
      },
      // Japanese: もし～ならば、～のとき、～は～すること (condition+event)
      {
        regex: /(?:もし|if)\s*(.+?)(?:ならば|なら|の場合)[、,]\s*(.+?)(?:した|の)(?:とき|時)[、,]\s*(.+?)(?:は|が)\s*(.+?)(?:すること|する)$/i,
        extractor: (m) => ({ condition: m[1], trigger: m[2], system: m[3], action: m[4] }),
      },
      // Japanese: もし～ならば、～の間、～は～すること (condition+state)
      {
        regex: /(?:もし|if)\s*(.+?)(?:ならば|なら|の場合)[、,]\s*(.+?)間[、,]\s*(.+?)(?:は|が)\s*(.+?)(?:すること|する)$/i,
        extractor: (m) => ({ condition: m[1], state: m[2], system: m[3], action: m[4] }),
      },
    ];

    for (const pattern of complexPatterns) {
      const match = normalizedText.match(pattern.regex);
      if (match) {
        const components = pattern.extractor(match);
        return {
          type: 'complex',
          confidence: 0.85,
          components: {
            trigger: components.trigger?.trim(),
            state: components.state?.trim(),
            condition: components.condition?.trim(),
            system: components.system?.trim(),
            action: components.action?.trim(),
          },
          original: text,
        };
      }
    }

    return null;
  }

  /**
   * Calculate confidence score for pattern match
   * 
   * More specific patterns (event-driven, state-driven, etc.) get higher
   * confidence than the generic ubiquitous pattern when they match.
   */
  private calculateConfidence(
    components: EARSComponents,
    type: EARSPatternType
  ): number {
    let confidence = 0.5; // Base confidence for pattern match

    // Pattern specificity bonus - more specific patterns get higher confidence
    const patternBonus: Record<EARSPatternType, number> = {
      'event-driven': 0.25,   // Has trigger keyword (WHEN)
      'state-driven': 0.25,   // Has state keyword (WHILE)
      'unwanted': 0.20,       // Has condition keyword (IF)
      'optional': 0.20,       // Has feature keyword (WHERE)
      'complex': 0.30,        // Combined patterns
      'ubiquitous': 0.0,      // Generic pattern - no bonus
    };
    confidence += patternBonus[type] || 0;

    // Check component quality
    if (components.system && components.system.length > 2) {
      confidence += 0.10;
    }
    
    if (components.action && components.action.length > 5) {
      confidence += 0.10;
    }

    // Bonus for well-formed components
    if (components.action?.includes(' ')) {
      confidence += 0.05; // Action has multiple words
    }

    // Bonus for specific pattern components
    if (components.trigger && components.trigger.length > 3) {
      confidence += 0.05; // Event-driven has meaningful trigger
    }
    if (components.state && components.state.length > 3) {
      confidence += 0.05; // State-driven has meaningful state
    }
    if (components.condition && components.condition.length > 3) {
      confidence += 0.05; // Unwanted has meaningful condition
    }

    // Cap at 1.0
    return Math.min(confidence, 1.0);
  }

  /**
   * Check quality of matched requirement
   */
  private checkQuality(match: EARSPatternMatch): ValidationIssue[] {
    const issues: ValidationIssue[] = [];
    const { components } = match;

    // Check for vague terms
    const vagueTerms = ['appropriate', 'adequate', 'etc', 'and/or', 'as needed'];
    const text = match.original.toLowerCase();
    
    for (const term of vagueTerms) {
      if (text.includes(term)) {
        issues.push({
          severity: 'warning',
          message: `Requirement contains vague term: "${term}"`,
          ruleId: 'ears-vague-term',
        });
      }
    }

    // Check system name
    if (components.system && components.system.length < 3) {
      issues.push({
        severity: 'warning',
        message: 'System name is too short',
        ruleId: 'ears-short-system',
      });
    }

    // Check action specificity
    if (components.action) {
      const actionWords = components.action.split(/\s+/).length;
      if (actionWords < 2) {
        issues.push({
          severity: 'info',
          message: 'Action could be more specific',
          ruleId: 'ears-vague-action',
        });
      }
    }

    // Check for measurability
    const hasMetric = /\d+|percent|seconds?|minutes?|hours?|ms|milliseconds?/i.test(text);
    if (!hasMetric && match.type !== 'ubiquitous') {
      issues.push({
        severity: 'info',
        message: 'Consider adding measurable criteria',
        ruleId: 'ears-no-metric',
      });
    }

    return issues;
  }

  /**
   * Generate rewrite suggestions for non-conforming requirements
   */
  private generateRewrites(text: string): string[] {
    const suggestions: string[] = [];
    const lowerText = text.toLowerCase();

    // Detect potential pattern and suggest
    if (lowerText.includes('when') || lowerText.includes('upon')) {
      suggestions.push(
        `Event-driven: "When <trigger>, the system shall ${this.extractAction(text)}"`
      );
    }

    if (lowerText.includes('while') || lowerText.includes('during')) {
      suggestions.push(
        `State-driven: "While <state>, the system shall ${this.extractAction(text)}"`
      );
    }

    if (lowerText.includes('if') || lowerText.includes('in case')) {
      suggestions.push(
        `Unwanted behavior: "If <condition>, then the system shall ${this.extractAction(text)}"`
      );
    }

    // Default ubiquitous suggestion
    if (suggestions.length === 0) {
      suggestions.push(
        `Ubiquitous: "The system shall ${this.extractAction(text)}"`
      );
    }

    return suggestions;
  }

  /**
   * Extract action from text
   */
  private extractAction(text: string): string {
    // Try to find verb phrase
    const verbMatch = text.match(
      /(?:should|must|will|shall|can|may)\s+(.+?)(?:\.|$)/i
    );
    
    if (verbMatch) {
      return verbMatch[1].trim();
    }

    // Return cleaned text as action
    return text.replace(/^(?:the\s+)?system\s+/i, '').trim() || '<action>';
  }

  /**
   * Analyze pattern distribution
   */
  private analyzeDistribution(
    results: Array<{ result: EARSValidationResult }>
  ): Record<EARSPatternType, number> {
    const distribution: Record<EARSPatternType, number> = {
      'ubiquitous': 0,
      'event-driven': 0,
      'state-driven': 0,
      'unwanted': 0,
      'optional': 0,
      'complex': 0,
    };

    for (const { result } of results) {
      if (result.patternMatch) {
        distribution[result.patternMatch.type]++;
      }
    }

    return distribution;
  }

  /**
   * Aggregate issues from all results
   */
  private aggregateIssues(
    results: Array<{ result: EARSValidationResult }>
  ): Map<string, number> {
    const issueCount = new Map<string, number>();

    for (const { result } of results) {
      for (const issue of result.issues) {
        const key = issue.ruleId ?? issue.message;
        issueCount.set(key, (issueCount.get(key) ?? 0) + 1);
      }
    }

    return issueCount;
  }

  /**
   * Get pattern description
   */
  static getPatternDescription(type: EARSPatternType): string {
    const pattern = EARS_PATTERNS.find((p) => p.type === type);
    return pattern?.description ?? 'Unknown pattern';
  }

  /**
   * Get all pattern descriptions
   */
  static getAllPatterns(): Array<{ type: EARSPatternType; description: string }> {
    return EARS_PATTERNS.map((p) => ({
      type: p.type,
      description: p.description,
    }));
  }
}

/**
 * EARS Validation Result
 */
export interface EARSValidationResult {
  /** Is valid EARS format */
  valid: boolean;
  /** Pattern match details */
  patternMatch: EARSPatternMatch | null;
  /** Quality issues */
  issues: ValidationIssue[];
  /** Rewrite suggestions */
  suggestions: string[];
}

/**
 * EARS Batch Validation Result
 */
export interface EARSBatchValidationResult {
  /** Total requirements */
  total: number;
  /** Valid requirements */
  valid: number;
  /** Invalid requirements */
  invalid: number;
  /** Coverage ratio */
  coverage: number;
  /** Individual results */
  results: Array<{
    index: number;
    requirement: string;
    result: EARSValidationResult;
  }>;
  /** Pattern distribution */
  patternDistribution: Record<EARSPatternType, number>;
  /** Aggregated issues */
  overallIssues: Map<string, number>;
}

/**
 * Create EARS validator instance
 */
export function createEARSValidator(
  options?: Partial<EARSValidatorOptions>
): EARSValidator {
  return new EARSValidator(options);
}
