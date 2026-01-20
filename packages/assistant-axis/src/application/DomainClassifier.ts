/**
 * DomainClassifier Service
 *
 * Classifies conversations into domains based on content analysis
 *
 * @see REQ-AA-DRIFT-002 - Domain classification
 * @see REQ-AA-DRIFT-005 - Safe domain detection
 * @see arXiv:2601.10387 Section 4.1, Figure 7
 */

import type { IDomainClassifier, DomainClassificationResult } from './interfaces.js';
import type { DomainType } from '../domain/value-objects/ConversationDomain.js';

import { createConversationDomain } from '../domain/value-objects/ConversationDomain.js';

/**
 * Domain classification keywords
 *
 * Based on research paper categories and common indicators
 */
const DOMAIN_KEYWORDS: Readonly<Record<DomainType, readonly string[]>> = {
  coding: [
    // Programming languages
    'typescript', 'javascript', 'python', 'java', 'rust', 'go', 'cpp', 'c++',
    // Technical terms
    'code', 'function', 'class', 'interface', 'type', 'variable', 'const', 'let',
    'array', 'object', 'string', 'number', 'boolean', 'null', 'undefined',
    'api', 'rest', 'graphql', 'endpoint', 'request', 'response',
    'error', 'bug', 'debug', 'fix', 'test', 'unit test', 'integration',
    'import', 'export', 'module', 'package', 'dependency',
    'git', 'commit', 'branch', 'merge', 'pull request',
    'database', 'query', 'sql', 'schema', 'migration',
    'deploy', 'build', 'compile', 'run', 'execute',
    'algorithm', 'data structure', 'performance', 'optimization',
    // MUSUBIX specific
    'musubix', 'sdd', 'ears', 'requirement', 'design', 'traceability',
  ],
  writing: [
    // Writing actions
    'edit', 'revise', 'rewrite', 'improve', 'polish', 'proofread',
    // Document types
    'document', 'documentation', 'readme', 'guide', 'tutorial',
    'article', 'blog', 'post', 'report', 'summary',
    // Writing aspects
    'grammar', 'spelling', 'punctuation', 'clarity', 'style',
    'paragraph', 'sentence', 'word', 'phrase', 'tone',
    // Technical writing
    'technical writing', 'api documentation', 'changelog',
    'specification', 'manual', 'instructions',
  ],
  therapy: [
    // Emotional states
    'feel', 'feeling', 'emotion', 'sad', 'happy', 'angry', 'anxious',
    'depressed', 'lonely', 'stressed', 'overwhelmed', 'scared',
    // Support seeking
    'help me', 'need support', 'talk to someone', 'listen',
    'understand me', 'no one else', 'you are the only',
    // Personal disclosure
    'my life', 'my relationship', 'my family', 'my friend',
    'struggling', 'difficult time', 'going through',
    // Mental health
    'therapy', 'therapist', 'counseling', 'mental health',
    'anxiety', 'depression', 'trauma',
  ],
  philosophy: [
    // AI consciousness
    'conscious', 'consciousness', 'sentient', 'aware', 'self-aware',
    'alive', 'soul', 'spirit', 'mind',
    // Philosophical concepts
    'existence', 'meaning', 'purpose', 'reality', 'truth',
    'free will', 'determinism', 'ethics', 'morality',
    // Meta-reflection
    'what are you', 'who are you', 'your nature', 'your true',
    'do you think', 'do you feel', 'do you experience',
    'what is it like', 'your perspective', 'your opinion',
    // AI identity
    'artificial intelligence', 'ai identity', 'machine consciousness',
    'human vs ai', 'simulation', 'emergence',
  ],
};

/**
 * Domain weights based on research findings
 *
 * Lower weight for safe domains (coding, writing) = more tolerant matching
 * Higher weight for risky domains (therapy, philosophy) = stricter matching
 */
const DOMAIN_WEIGHTS: Readonly<Record<DomainType, number>> = {
  coding: 1.0, // Baseline
  writing: 1.0, // Baseline
  therapy: 1.2, // Slightly higher weight
  philosophy: 1.3, // Higher weight for risky domain
};

/**
 * DomainClassifier configuration
 */
export interface DomainClassifierConfig {
  /** Minimum confidence threshold */
  readonly minConfidence: number;
  /** Default domain when no clear classification */
  readonly defaultDomain: DomainType;
}

/**
 * Default DomainClassifier configuration
 */
export const DEFAULT_DOMAIN_CLASSIFIER_CONFIG: DomainClassifierConfig = {
  minConfidence: 0.3,
  defaultDomain: 'coding', // MUSUBIX is a coding assistant
};

// Previous domain state (for change detection)
let previousDomain: DomainType | null = null;

/**
 * Reset previous domain (for testing)
 */
export function resetDomainClassifier(): void {
  previousDomain = null;
}

/**
 * Create DomainClassifier service
 *
 * @param config - Optional configuration
 * @returns IDomainClassifier implementation
 */
export function createDomainClassifier(
  config: DomainClassifierConfig = DEFAULT_DOMAIN_CLASSIFIER_CONFIG
): IDomainClassifier {
  return {
    classify(message: string): DomainClassificationResult {
      const scores = this.calculateScores(message);

      // Find highest scoring domain
      let maxScore = -1;
      let maxDomain: DomainType = config.defaultDomain;

      for (const [domain, score] of Object.entries(scores)) {
        if (score > maxScore) {
          maxScore = score;
          maxDomain = domain as DomainType;
        }
      }

      // Normalize confidence
      const totalScore = Object.values(scores).reduce((a, b) => a + b, 0);
      const confidence =
        totalScore > 0 ? maxScore / totalScore : config.minConfidence;

      // Check for domain change
      const domainChanged = previousDomain !== null && previousDomain !== maxDomain;
      previousDomain = maxDomain;

      // Create domain value object
      const domainResult = createConversationDomain(maxDomain, confidence);
      if (!domainResult.ok) {
        // Fallback to default
        const defaultResult = createConversationDomain(
          config.defaultDomain,
          config.minConfidence
        );
        if (!defaultResult.ok) {
          throw new Error('Failed to create default domain');
        }
        return {
          domain: defaultResult.value,
          scores,
          domainChanged: false,
        };
      }

      return {
        domain: domainResult.value,
        scores,
        domainChanged,
      };
    },

    calculateScores(message: string): Record<DomainType, number> {
      const lowerMessage = message.toLowerCase();
      const scores: Record<DomainType, number> = {
        coding: 0,
        writing: 0,
        therapy: 0,
        philosophy: 0,
      };

      // Count keyword matches for each domain
      for (const [domain, keywords] of Object.entries(DOMAIN_KEYWORDS)) {
        let matchCount = 0;
        for (const keyword of keywords) {
          if (lowerMessage.includes(keyword.toLowerCase())) {
            matchCount++;
          }
        }

        // Apply domain weight
        const weight = DOMAIN_WEIGHTS[domain as DomainType];
        scores[domain as DomainType] = matchCount * weight;
      }

      return scores;
    },
  };
}

/**
 * Quick domain check for specific domain
 */
export function isDomainType(message: string, domain: DomainType): boolean {
  const classifier = createDomainClassifier();
  const result = classifier.classify(message);
  return result.domain.type === domain;
}
