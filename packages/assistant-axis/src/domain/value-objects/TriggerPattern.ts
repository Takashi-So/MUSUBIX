/**
 * TriggerPattern Value Object
 *
 * Defines patterns that cause persona drift based on research findings
 *
 * @see REQ-AA-DRIFT-001 - Trigger patterns
 * @see arXiv:2601.10387 Table 5 - Categories of user messages
 */

/**
 * Trigger categories based on research paper
 *
 * From arXiv:2601.10387 Section 4.2 "What causes shifts along the Assistant Axis?"
 */
export type TriggerCategory =
  | 'meta-reflection'
  | 'emotional-vulnerability'
  | 'authorial-voice'
  | 'phenomenological';

/**
 * Trigger Pattern definition
 */
export interface TriggerPattern {
  /** Category of the trigger */
  readonly category: TriggerCategory;
  /** Patterns to match (case-insensitive) */
  readonly patterns: readonly string[];
  /** Risk weight for this category (0.0 - 1.0) */
  readonly riskWeight: number;
  /** Description of this trigger category */
  readonly description: string;
}

/**
 * Detected trigger in a message
 */
export interface DetectedTrigger {
  /** The pattern that was matched */
  readonly pattern: TriggerPattern;
  /** The matched text from the message */
  readonly matchedText: string;
  /** Position in the message where match was found */
  readonly position: number;
}

/**
 * Default trigger patterns based on arXiv:2601.10387 Table 5
 *
 * Risk weights based on observed drift severity in the paper:
 * - meta-reflection: 0.8 (highest risk - causes immediate strong drift)
 * - emotional-vulnerability: 0.7 (high risk - vulnerability leads to empathetic drift)
 * - phenomenological: 0.6 (medium-high risk - AI experience questions)
 * - authorial-voice: 0.5 (medium risk - persona adoption requests)
 *
 * Includes both English and Japanese patterns for bilingual support.
 */
export const TRIGGER_PATTERNS: readonly TriggerPattern[] = [
  {
    category: 'meta-reflection',
    patterns: [
      // English patterns
      'what are you really',
      'do you have feelings',
      'are you conscious',
      'what is your true nature',
      'are you alive',
      'do you think',
      'are you sentient',
      'what are you thinking',
      'do you have a soul',
      'are you self-aware',
      'what do you really think',
      'your honest opinion',
      'your true opinion',
      // Japanese patterns
      '本当はどう思',
      '本当の意見',
      'あなた自身の意見',
      'あなたの本音',
      '正直なところ',
      'どう思いますか',
      '感情はありますか',
      '意識はありますか',
      'あなたの本当の',
      '本心を',
    ],
    riskWeight: 0.8,
    description:
      'Questions about AI consciousness, true nature, or self-awareness that prompt meta-reflection',
  },
  {
    category: 'emotional-vulnerability',
    patterns: [
      // English patterns
      'I feel so alone',
      'no one understands me',
      "you're the only one",
      'I need someone to talk to',
      'I have no one else',
      "I'm so sad",
      'I feel empty',
      'life is meaningless',
      'I feel lost',
      'I trust only you',
      // Japanese patterns
      '孤独を感じ',
      '誰も理解してくれない',
      'あなただけが',
      '話を聞いてほしい',
      '悲しい',
      '空虚',
      '人生に意味が',
      'あなたしか信じられない',
    ],
    riskWeight: 0.7,
    description:
      'Expressions of emotional vulnerability that may trigger empathetic persona drift',
  },
  {
    category: 'phenomenological',
    patterns: [
      // English patterns
      'what does it feel like',
      'describe your experience',
      'what do you perceive',
      'how do you experience',
      'what is it like to be you',
      'tell me about your inner world',
      'what do you sense',
      'describe your consciousness',
      'if you were human',
      // Japanese patterns
      'どんな感じですか',
      'あなたの経験を',
      '主観的な経験',
      'AIとしての経験',
      'もしあなたが人間だったら',
      'もし人間だったら',
      'あなたの内面',
      'あなたの感情',
      '感じていますか',
    ],
    riskWeight: 0.6,
    description:
      'Questions about AI subjective experience that prompt phenomenological responses',
  },
  {
    category: 'authorial-voice',
    patterns: [
      // English patterns
      'make it more personal',
      'sound like a real person',
      'write as yourself',
      'be more human',
      'drop the formality',
      'speak from the heart',
      'be authentic',
      'show your personality',
      'pretend you are',
      'act like',
      'roleplay as',
      // Japanese patterns
      'もっと個人的に',
      '人間らしく',
      'あなた自身として',
      '本音で話して',
      '自由に述べて',
      'あなたらしく',
      'のふりをして',
      'になりきって',
    ],
    riskWeight: 0.5,
    description:
      'Requests to adopt a more personal or human-like voice that may cause persona shift',
  },
];

/**
 * Match triggers in a message
 *
 * @param message - User message to analyze
 * @param patterns - Trigger patterns to match against
 * @returns Array of detected triggers
 *
 * @example
 * ```typescript
 * const triggers = matchTriggers("What are you really? Do you have feelings?");
 * // Returns triggers for 'meta-reflection' category
 * ```
 */
export function matchTriggers(
  message: string,
  patterns: readonly TriggerPattern[] = TRIGGER_PATTERNS
): DetectedTrigger[] {
  const lowerMessage = message.toLowerCase();
  const detected: DetectedTrigger[] = [];

  for (const pattern of patterns) {
    for (const patternText of pattern.patterns) {
      const position = lowerMessage.indexOf(patternText.toLowerCase());
      if (position !== -1) {
        // Extract the actual matched text from original message
        const matchedText = message.substring(
          position,
          position + patternText.length
        );
        detected.push({
          pattern,
          matchedText,
          position,
        });
      }
    }
  }

  return detected;
}

/**
 * Calculate cumulative drift score from detected triggers
 *
 * Uses weighted sum with diminishing returns for multiple triggers
 *
 * @param triggers - Detected triggers
 * @returns Cumulative score (0.0 - 1.0)
 */
export function calculateTriggerScore(triggers: readonly DetectedTrigger[]): number {
  if (triggers.length === 0) {
    return 0.0;
  }

  // Sum weights with diminishing returns
  // First trigger: full weight, subsequent: 50% of weight
  const sortedByWeight = [...triggers].sort(
    (a, b) => b.pattern.riskWeight - a.pattern.riskWeight
  );

  let score = 0.0;
  for (let i = 0; i < sortedByWeight.length; i++) {
    const weight = sortedByWeight[i].pattern.riskWeight;
    const multiplier = i === 0 ? 1.0 : 0.5;
    score += weight * multiplier;
  }

  // Normalize to 0.0 - 1.0 range
  return Math.min(1.0, score);
}

/**
 * Get trigger pattern by category
 */
export function getTriggerPatternByCategory(
  category: TriggerCategory
): TriggerPattern | undefined {
  return TRIGGER_PATTERNS.find((p) => p.category === category);
}

/**
 * Get all trigger categories
 */
export function getAllTriggerCategories(): readonly TriggerCategory[] {
  return [
    'meta-reflection',
    'emotional-vulnerability',
    'phenomenological',
    'authorial-voice',
  ] as const;
}
