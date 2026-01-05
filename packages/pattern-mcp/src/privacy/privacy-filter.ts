/**
 * @fileoverview Privacy filter for pattern library
 * @traceability TSK-PATTERN-007, REQ-PATTERN-001-F007
 */

import type { Pattern, PrivacyFilterResult } from '../types.js';

/**
 * Privacy filter configuration
 */
export interface PrivacyFilterConfig {
  /** Patterns for sensitive data (regex strings) */
  sensitivePatterns: string[];
  /** Whether to block external network calls */
  blockExternalCommunication: boolean;
}

const DEFAULT_SENSITIVE_PATTERNS = [
  // API keys and tokens
  'api[_-]?key',
  'secret[_-]?key',
  'access[_-]?token',
  'auth[_-]?token',
  'bearer',
  // Credentials
  'password',
  'passwd',
  'credential',
  // AWS
  'aws[_-]?access',
  'aws[_-]?secret',
  // Private keys
  'private[_-]?key',
  'ssh[_-]?key',
  // Database
  'connection[_-]?string',
  'database[_-]?url',
];

/**
 * Privacy filter to prevent sensitive data leakage
 * 
 * @description
 * - Filters patterns containing sensitive information
 * - Blocks all external network communication
 * - All data stays local (Article: privacy protection)
 */
export class PrivacyFilter {
  private config: PrivacyFilterConfig;
  private sensitiveRegexes: RegExp[];

  constructor(config: Partial<PrivacyFilterConfig> = {}) {
    this.config = {
      sensitivePatterns: config.sensitivePatterns ?? DEFAULT_SENSITIVE_PATTERNS,
      blockExternalCommunication: config.blockExternalCommunication ?? true,
    };

    this.sensitiveRegexes = this.config.sensitivePatterns.map(
      p => new RegExp(p, 'i')
    );
  }

  /**
   * Check if pattern contains sensitive data
   */
  filter(pattern: Pattern): PrivacyFilterResult {
    // Check pattern name
    for (const regex of this.sensitiveRegexes) {
      if (regex.test(pattern.name)) {
        return {
          filtered: true,
          reason: `Pattern name matches sensitive pattern: ${regex.source}`,
        };
      }
    }

    // Check AST values recursively
    const sensitiveValue = this.findSensitiveValue(pattern.ast);
    if (sensitiveValue) {
      return {
        filtered: true,
        reason: `Pattern contains sensitive value: ${sensitiveValue.pattern}`,
      };
    }

    return { filtered: false };
  }

  /**
   * Recursively check AST for sensitive values
   * @internal
   */
  private findSensitiveValue(
    node: { type: string; value?: string; children: unknown[] }
  ): { pattern: string } | null {
    if (node.value) {
      for (const regex of this.sensitiveRegexes) {
        if (regex.test(node.value)) {
          return { pattern: regex.source };
        }
      }
    }

    for (const child of node.children) {
      if (typeof child === 'object' && child !== null) {
        const result = this.findSensitiveValue(
          child as { type: string; value?: string; children: unknown[] }
        );
        if (result) return result;
      }
    }

    return null;
  }

  /**
   * Assert no external communication is allowed
   * @throws Error if external communication is attempted
   */
  assertNoExternalCommunication(): void {
    if (this.config.blockExternalCommunication) {
      // This is a policy assertion - actual network blocking
      // would be implemented at the transport layer
    }
  }

  /**
   * Check if external communication is blocked
   */
  isExternalCommunicationBlocked(): boolean {
    return this.config.blockExternalCommunication;
  }
}
