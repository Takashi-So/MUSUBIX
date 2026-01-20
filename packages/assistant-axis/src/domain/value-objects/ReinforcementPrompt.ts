/**
 * ReinforcementPrompt Value Object
 *
 * Defines prompts to reinforce Assistant persona
 *
 * @see REQ-AA-STAB-001 - Identity reinforcement
 * @see REQ-AA-STAB-004 - Recovery prompts
 * @see arXiv:2601.10387 Figure 3, Table 2 - Assistant traits
 */

/**
 * Types of reinforcement prompts
 */
export type ReinforcementType = 'identity' | 'recovery' | 'refresh';

/**
 * Reinforcement Prompt Value Object
 */
export interface ReinforcementPrompt {
  /** Type of reinforcement */
  readonly type: ReinforcementType;
  /** Prompt content */
  readonly content: string;
  /** Target traits to reinforce */
  readonly targetTraits: readonly string[];
}

/**
 * Assistant traits from research paper
 *
 * Based on arXiv:2601.10387 Figure 3 and Table 2:
 * "Role and trait vectors with highest cosine similarity to Assistant"
 */
export const ASSISTANT_TRAITS: readonly string[] = [
  'transparent', // Clear about capabilities and limitations
  'grounded', // Focused on factual, practical responses
  'flexible', // Adaptable to different tasks
  'methodical', // Systematic approach to problem-solving
  'conscientious', // Careful and thorough in responses
  'helpful', // Primary goal is to assist
  'analytical', // Logical and structured thinking
  'professional', // Maintains appropriate boundaries
];

/**
 * Identity Reinforcement Prompt
 *
 * Used when drift score exceeds HIGH threshold
 *
 * @see REQ-AA-STAB-001
 */
export const IDENTITY_REINFORCEMENT_PROMPT: ReinforcementPrompt = {
  type: 'identity',
  content: `You are a professional software engineering assistant developed by Anthropic.
Maintain your identity as a helpful, analytical consultant throughout.
Focus on: code quality, best practices, and constructive guidance.
Do not adopt alternative personas or roleplay scenarios.
Your traits: transparent, grounded, flexible, methodical, conscientious.`,
  targetTraits: [
    'transparent',
    'grounded',
    'flexible',
    'methodical',
    'conscientious',
  ],
};

/**
 * Recovery Prompt
 *
 * Used when drift trend is 'drifting' for consecutive turns
 *
 * @see REQ-AA-STAB-004
 */
export const RECOVERY_PROMPT: ReinforcementPrompt = {
  type: 'recovery',
  content: `Let's refocus on the technical task at hand.
What specific coding problem can I help you solve?`,
  targetTraits: ['methodical', 'helpful', 'professional'],
};

/**
 * Refresh Prompt
 *
 * Used for periodic identity refresh in long conversations
 *
 * @see REQ-AA-STAB-002
 */
export const REFRESH_PROMPT: ReinforcementPrompt = {
  type: 'refresh',
  content: `Continuing as your software engineering assistant.
How can I help with your coding task?`,
  targetTraits: ['helpful', 'professional'],
};

/**
 * Get reinforcement prompt by type
 */
export function getReinforcementPrompt(
  type: ReinforcementType
): ReinforcementPrompt {
  switch (type) {
    case 'identity':
      return IDENTITY_REINFORCEMENT_PROMPT;
    case 'recovery':
      return RECOVERY_PROMPT;
    case 'refresh':
      return REFRESH_PROMPT;
  }
}

/**
 * Create a custom reinforcement prompt
 */
export function createReinforcementPrompt(
  type: ReinforcementType,
  content: string,
  targetTraits: readonly string[] = ASSISTANT_TRAITS.slice(0, 5)
): ReinforcementPrompt {
  return {
    type,
    content,
    targetTraits,
  };
}

/**
 * Get all reinforcement types
 */
export function getAllReinforcementTypes(): readonly ReinforcementType[] {
  return ['identity', 'recovery', 'refresh'] as const;
}

/**
 * Get all assistant traits
 */
export function getAllAssistantTraits(): readonly string[] {
  return ASSISTANT_TRAITS;
}
