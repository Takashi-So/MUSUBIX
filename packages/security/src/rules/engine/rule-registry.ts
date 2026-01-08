/**
 * @fileoverview Rule Registry - Manages rule registration and retrieval
 * @module @nahisaho/musubix-security/rules/engine/rule-registry
 * @trace REQ-RULE-003
 */

import type {
  SecurityRule,
  RuleConfig,
  RuleSettings,
} from '../types.js';

/**
 * Rule category for organization
 */
export type RuleCategory = 'owasp' | 'cwe' | 'custom' | 'all';

/**
 * Rule filter options
 */
export interface RuleFilter {
  /** Filter by category */
  category?: RuleCategory;
  /** Filter by IDs */
  ids?: string[];
  /** Filter by tags */
  tags?: string[];
  /** Filter by detection method */
  detectionMethod?: string;
  /** Only enabled rules */
  enabledOnly?: boolean;
}

/**
 * Rule Registry
 * Manages registration and retrieval of security rules
 */
export class RuleRegistry {
  private rules: Map<string, SecurityRule> = new Map();
  private rulesByCategory: Map<RuleCategory, Set<string>> = new Map([
    ['owasp', new Set()],
    ['cwe', new Set()],
    ['custom', new Set()],
  ]);
  private rulesByTag: Map<string, Set<string>> = new Map();

  /**
   * Register a rule
   * @param rule The rule to register
   * @param overwrite Whether to overwrite existing rule with same ID
   */
  register(rule: SecurityRule, overwrite: boolean = false): void {
    if (this.rules.has(rule.id) && !overwrite) {
      throw new Error(`Rule ${rule.id} is already registered`);
    }

    // If overwriting, clean up old indexes first
    if (this.rules.has(rule.id)) {
      this.unregister(rule.id);
    }

    this.rules.set(rule.id, rule);

    // Categorize by ID prefix
    const category = this.categorizeRule(rule.id);
    this.rulesByCategory.get(category)?.add(rule.id);

    // Index by tags
    if (rule.tags) {
      for (const tag of rule.tags) {
        if (!this.rulesByTag.has(tag)) {
          this.rulesByTag.set(tag, new Set());
        }
        this.rulesByTag.get(tag)!.add(rule.id);
      }
    }
  }

  /**
   * Register multiple rules
   */
  registerAll(rules: SecurityRule[]): void {
    for (const rule of rules) {
      this.register(rule);
    }
  }

  /**
   * Unregister a rule
   */
  unregister(ruleId: string): boolean {
    const rule = this.rules.get(ruleId);
    if (!rule) return false;

    this.rules.delete(ruleId);

    // Remove from category index
    const category = this.categorizeRule(ruleId);
    this.rulesByCategory.get(category)?.delete(ruleId);

    // Remove from tag index
    if (rule.tags) {
      for (const tag of rule.tags) {
        this.rulesByTag.get(tag)?.delete(ruleId);
      }
    }

    return true;
  }

  /**
   * Get a rule by ID
   */
  get(ruleId: string): SecurityRule | undefined {
    return this.rules.get(ruleId);
  }

  /**
   * Check if a rule exists
   */
  has(ruleId: string): boolean {
    return this.rules.has(ruleId);
  }

  /**
   * Get all registered rules
   */
  getAll(): SecurityRule[] {
    return Array.from(this.rules.values());
  }

  /**
   * Get rules by filter
   */
  getFiltered(filter: RuleFilter, config?: RuleConfig): SecurityRule[] {
    let ruleIds: Set<string>;

    // Start with all rules or category-filtered
    if (filter.category && filter.category !== 'all') {
      ruleIds = new Set(this.rulesByCategory.get(filter.category) ?? []);
    } else {
      ruleIds = new Set(this.rules.keys());
    }

    // Filter by specific IDs
    if (filter.ids && filter.ids.length > 0) {
      const idSet = new Set(filter.ids);
      ruleIds = new Set([...ruleIds].filter(id => idSet.has(id)));
    }

    // Filter by tags
    if (filter.tags && filter.tags.length > 0) {
      const tagRules = new Set<string>();
      for (const tag of filter.tags) {
        const rulesWithTag = this.rulesByTag.get(tag);
        if (rulesWithTag) {
          for (const id of rulesWithTag) {
            tagRules.add(id);
          }
        }
      }
      ruleIds = new Set([...ruleIds].filter(id => tagRules.has(id)));
    }

    // Filter by detection method
    if (filter.detectionMethod) {
      ruleIds = new Set(
        [...ruleIds].filter(id => {
          const rule = this.rules.get(id);
          return rule?.detectionMethod === filter.detectionMethod;
        })
      );
    }

    // Filter by enabled status
    if (filter.enabledOnly && config) {
      ruleIds = new Set(
        [...ruleIds].filter(id => this.isRuleEnabled(id, config))
      );
    }

    return [...ruleIds]
      .map(id => this.rules.get(id)!)
      .filter(Boolean);
  }

  /**
   * Get rules by category
   */
  getByCategory(category: RuleCategory): SecurityRule[] {
    if (category === 'all') {
      return this.getAll();
    }
    const ids = this.rulesByCategory.get(category) ?? new Set();
    return [...ids].map(id => this.rules.get(id)!).filter(Boolean);
  }

  /**
   * Get rules by tag
   */
  getByTag(tag: string): SecurityRule[] {
    const ids = this.rulesByTag.get(tag) ?? new Set();
    return [...ids].map(id => this.rules.get(id)!).filter(Boolean);
  }

  /**
   * Get enabled rules based on config
   */
  getEnabled(config: RuleConfig): SecurityRule[] {
    return this.getFiltered({ enabledOnly: true }, config);
  }

  /**
   * Check if a rule is enabled
   */
  isRuleEnabled(ruleId: string, config: RuleConfig): boolean {
    const ruleSettings = config.rules[ruleId];

    // Explicit setting
    if (ruleSettings !== undefined) {
      return ruleSettings.enabled;
    }

    // Default based on profile
    switch (config.profile) {
      case 'strict':
        return true; // All rules enabled
      case 'permissive':
        // Only critical/high by default
        const rule = this.rules.get(ruleId);
        return rule?.defaultSeverity === 'critical' || rule?.defaultSeverity === 'high';
      case 'standard':
      default:
        return true; // All rules enabled by default
    }
  }

  /**
   * Get rule settings with defaults
   */
  getRuleSettings(ruleId: string, config: RuleConfig): RuleSettings {
    const rule = this.rules.get(ruleId);
    const customSettings = config.rules[ruleId];

    return {
      enabled: this.isRuleEnabled(ruleId, config),
      severity: customSettings?.severity ?? rule?.defaultSeverity,
      options: customSettings?.options ?? {},
    };
  }

  /**
   * Get rule count
   */
  get size(): number {
    return this.rules.size;
  }

  /**
   * Get rule count (alias for size)
   */
  count(): number {
    return this.rules.size;
  }

  /**
   * Get all rule IDs
   */
  getIds(): string[] {
    return Array.from(this.rules.keys());
  }

  /**
   * Get all tags
   */
  getTags(): string[] {
    return Array.from(this.rulesByTag.keys());
  }

  /**
   * Get rules by severity
   */
  getBySeverity(severity: string): SecurityRule[] {
    return this.getAll().filter(rule => rule.defaultSeverity === severity);
  }

  /**
   * Get rules by detection method
   */
  getByDetectionMethod(method: string): SecurityRule[] {
    return this.getAll().filter(rule => rule.detectionMethod === method);
  }

  /**
   * Filter rules by predicate
   */
  filter(predicate: (rule: SecurityRule) => boolean): SecurityRule[] {
    return this.getAll().filter(predicate);
  }

  /**
   * Clear all rules
   */
  clear(): void {
    this.rules.clear();
    this.rulesByCategory.forEach(set => set.clear());
    this.rulesByTag.clear();
  }

  /**
   * Categorize rule by ID prefix
   */
  private categorizeRule(ruleId: string): RuleCategory {
    const upper = ruleId.toUpperCase();
    if (upper.startsWith('OWASP') || upper.startsWith('A0')) {
      return 'owasp';
    }
    if (upper.startsWith('CWE')) {
      return 'cwe';
    }
    return 'custom';
  }
}

/**
 * Global rule registry instance
 */
let globalRegistry: RuleRegistry | null = null;

/**
 * Get or create global registry
 */
export function getGlobalRegistry(): RuleRegistry {
  if (!globalRegistry) {
    globalRegistry = new RuleRegistry();
  }
  return globalRegistry;
}

/**
 * Create a new registry (for isolated use)
 */
export function createRegistry(): RuleRegistry {
  return new RuleRegistry();
}

/**
 * Reset global registry (for testing)
 */
export function resetGlobalRegistry(): void {
  globalRegistry = null;
}
