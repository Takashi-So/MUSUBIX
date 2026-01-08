/**
 * @fileoverview Rule Profiles
 * @module @nahisaho/musubix-security/rules/config/profiles
 * @trace TSK-RULE-002
 */

import type { RuleSeverity } from '../types.js';

/**
 * Profile definition
 */
export interface RuleProfile {
  /** Profile name */
  name: string;
  /** Profile description */
  description: string;
  /** Rules included in this profile */
  rules: ProfileRuleConfig[];
  /** Severity threshold for this profile */
  severityThreshold: RuleSeverity;
  /** Whether to enable taint analysis */
  enableTaintAnalysis: boolean;
  /** Whether to enable DFG analysis */
  enableDFG: boolean;
}

/**
 * Rule configuration in profile
 */
export interface ProfileRuleConfig {
  /** Rule ID */
  id: string;
  /** Whether enabled (default: true) */
  enabled?: boolean;
  /** Severity override */
  severity?: RuleSeverity;
}

/**
 * Minimal profile - Essential security checks only
 * Best for: Quick scans, CI pipelines with time constraints
 */
export const PROFILE_MINIMAL: RuleProfile = {
  name: 'minimal',
  description: 'Essential security checks - critical and high severity only',
  severityThreshold: 'high',
  enableTaintAnalysis: false,
  enableDFG: false,
  rules: [
    // OWASP Top 10 - Critical
    { id: 'owasp-a01-broken-access-control' },
    { id: 'owasp-a03-injection' },
    { id: 'owasp-a07-auth-failures' },
    // CWE Top 25 - Critical
    { id: 'cwe-79-xss' },
    { id: 'cwe-89-sql-injection' },
    { id: 'cwe-78-os-command-injection' },
    { id: 'cwe-22-path-traversal' },
    { id: 'cwe-798-hardcoded-credentials' },
    { id: 'cwe-287-improper-authentication' },
  ],
};

/**
 * Standard profile - Balanced security coverage
 * Best for: Regular development, PR checks
 */
export const PROFILE_STANDARD: RuleProfile = {
  name: 'standard',
  description: 'Balanced security coverage - OWASP Top 10 + CWE Top 25',
  severityThreshold: 'medium',
  enableTaintAnalysis: true,
  enableDFG: false,
  rules: [
    // All OWASP Top 10
    { id: 'owasp-a01-broken-access-control' },
    { id: 'owasp-a02-cryptographic-failures' },
    { id: 'owasp-a03-injection' },
    { id: 'owasp-a04-insecure-design' },
    { id: 'owasp-a05-security-misconfiguration' },
    { id: 'owasp-a06-vulnerable-components' },
    { id: 'owasp-a07-auth-failures' },
    { id: 'owasp-a08-integrity-failures' },
    { id: 'owasp-a09-logging-failures' },
    { id: 'owasp-a10-ssrf' },
    // CWE Top 25
    { id: 'cwe-787-out-of-bounds-write' },
    { id: 'cwe-79-xss' },
    { id: 'cwe-89-sql-injection' },
    { id: 'cwe-416-use-after-free' },
    { id: 'cwe-78-os-command-injection' },
    { id: 'cwe-20-improper-input-validation' },
    { id: 'cwe-125-out-of-bounds-read' },
    { id: 'cwe-22-path-traversal' },
    { id: 'cwe-352-csrf' },
    { id: 'cwe-434-file-upload' },
    { id: 'cwe-862-missing-authorization' },
    { id: 'cwe-476-null-pointer' },
    { id: 'cwe-287-improper-authentication' },
    { id: 'cwe-190-integer-overflow' },
    { id: 'cwe-502-deserialization' },
    { id: 'cwe-77-command-injection' },
    { id: 'cwe-119-buffer-overflow' },
    { id: 'cwe-798-hardcoded-credentials' },
    { id: 'cwe-918-ssrf' },
    { id: 'cwe-306-missing-auth-critical' },
    { id: 'cwe-362-race-condition' },
    { id: 'cwe-269-improper-privilege' },
    { id: 'cwe-94-code-injection' },
    { id: 'cwe-863-incorrect-authorization' },
    { id: 'cwe-276-incorrect-permissions' },
  ],
};

/**
 * Strict profile - Comprehensive security analysis
 * Best for: Security audits, pre-release checks
 */
export const PROFILE_STRICT: RuleProfile = {
  name: 'strict',
  description: 'Comprehensive security analysis - all rules enabled',
  severityThreshold: 'info',
  enableTaintAnalysis: true,
  enableDFG: true,
  rules: [
    // All rules from standard profile
    ...PROFILE_STANDARD.rules,
    // Additional low-priority rules
    { id: 'cwe-200-information-exposure' },
    { id: 'cwe-611-xxe' },
    { id: 'cwe-1321-prototype-pollution' },
    { id: 'cwe-400-uncontrolled-resource' },
    { id: 'cwe-601-open-redirect' },
    { id: 'cwe-522-weak-credentials' },
    { id: 'cwe-732-incorrect-permission' },
    { id: 'cwe-295-improper-cert-validation' },
    { id: 'cwe-327-broken-crypto' },
    { id: 'cwe-330-insufficient-randomness' },
  ],
};

/**
 * OWASP-only profile - OWASP Top 10 focus
 */
export const PROFILE_OWASP: RuleProfile = {
  name: 'owasp',
  description: 'OWASP Top 10 2021 focused analysis',
  severityThreshold: 'medium',
  enableTaintAnalysis: true,
  enableDFG: false,
  rules: [
    { id: 'owasp-a01-broken-access-control' },
    { id: 'owasp-a02-cryptographic-failures' },
    { id: 'owasp-a03-injection' },
    { id: 'owasp-a04-insecure-design' },
    { id: 'owasp-a05-security-misconfiguration' },
    { id: 'owasp-a06-vulnerable-components' },
    { id: 'owasp-a07-auth-failures' },
    { id: 'owasp-a08-integrity-failures' },
    { id: 'owasp-a09-logging-failures' },
    { id: 'owasp-a10-ssrf' },
  ],
};

/**
 * CWE-only profile - CWE Top 25 focus
 */
export const PROFILE_CWE: RuleProfile = {
  name: 'cwe',
  description: 'CWE Top 25 2023 focused analysis',
  severityThreshold: 'medium',
  enableTaintAnalysis: true,
  enableDFG: false,
  rules: [
    { id: 'cwe-787-out-of-bounds-write' },
    { id: 'cwe-79-xss' },
    { id: 'cwe-89-sql-injection' },
    { id: 'cwe-416-use-after-free' },
    { id: 'cwe-78-os-command-injection' },
    { id: 'cwe-20-improper-input-validation' },
    { id: 'cwe-125-out-of-bounds-read' },
    { id: 'cwe-22-path-traversal' },
    { id: 'cwe-352-csrf' },
    { id: 'cwe-434-file-upload' },
    { id: 'cwe-862-missing-authorization' },
    { id: 'cwe-476-null-pointer' },
    { id: 'cwe-287-improper-authentication' },
    { id: 'cwe-190-integer-overflow' },
    { id: 'cwe-502-deserialization' },
    { id: 'cwe-77-command-injection' },
    { id: 'cwe-119-buffer-overflow' },
    { id: 'cwe-798-hardcoded-credentials' },
    { id: 'cwe-918-ssrf' },
    { id: 'cwe-306-missing-auth-critical' },
    { id: 'cwe-362-race-condition' },
    { id: 'cwe-269-improper-privilege' },
    { id: 'cwe-94-code-injection' },
    { id: 'cwe-863-incorrect-authorization' },
    { id: 'cwe-276-incorrect-permissions' },
  ],
};

/**
 * All available profiles
 */
export const PROFILES: Record<string, RuleProfile> = {
  minimal: PROFILE_MINIMAL,
  standard: PROFILE_STANDARD,
  strict: PROFILE_STRICT,
  owasp: PROFILE_OWASP,
  cwe: PROFILE_CWE,
};

/**
 * Get profile by name
 */
export function getProfile(name: string): RuleProfile | undefined {
  return PROFILES[name.toLowerCase()];
}

/**
 * Get all profile names
 */
export function getProfileNames(): string[] {
  return Object.keys(PROFILES);
}

/**
 * Check if profile exists
 */
export function hasProfile(name: string): boolean {
  return name.toLowerCase() in PROFILES;
}

/**
 * Get rule IDs from profile
 */
export function getProfileRuleIds(profileName: string): string[] {
  const profile = getProfile(profileName);
  if (!profile) return [];
  return profile.rules.map(r => r.id);
}

/**
 * Merge profile with custom config
 */
export function mergeProfileConfig(
  profileName: string,
  customRules: Record<string, { enabled?: boolean; severity?: RuleSeverity }> = {}
): ProfileRuleConfig[] {
  const profile = getProfile(profileName);
  if (!profile) return [];

  const merged = new Map<string, ProfileRuleConfig>();

  // Add profile rules
  for (const rule of profile.rules) {
    merged.set(rule.id, { ...rule });
  }

  // Apply custom overrides
  for (const [ruleId, config] of Object.entries(customRules)) {
    const existing = merged.get(ruleId);
    if (existing) {
      merged.set(ruleId, { ...existing, ...config });
    } else if (config.enabled !== false) {
      merged.set(ruleId, { id: ruleId, ...config });
    }
  }

  return Array.from(merged.values());
}
