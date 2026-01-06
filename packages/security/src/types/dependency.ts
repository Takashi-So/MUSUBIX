/**
 * @fileoverview Dependency audit type definitions
 * @module @nahisaho/musubix-security/types/dependency
 * @trace REQ-SEC-DEP-001, REQ-SEC-DEP-002, REQ-SEC-DEP-003
 */

import type { Severity } from './vulnerability.js';

/**
 * Dependency type
 */
export type DependencyType = 'production' | 'development' | 'optional' | 'peer';

/**
 * Vulnerability source database
 */
export type VulnerabilitySource =
  | 'npm-audit' // npm audit
  | 'github-advisories' // GitHub Security Advisories
  | 'osv' // Open Source Vulnerabilities
  | 'snyk' // Snyk vulnerability database
  | 'nvd'; // National Vulnerability Database

/**
 * Vulnerable dependency
 * @trace REQ-SEC-DEP-001
 */
export interface VulnerableDependency {
  /** Package name */
  name: string;
  /** Installed version */
  installedVersion: string;
  /** Dependency type */
  type: DependencyType;
  /** Whether this is a direct dependency */
  isDirect: boolean;
  /** Dependency path (for transitive deps) */
  dependencyPath: string[];
  /** Known vulnerabilities */
  vulnerabilities: DependencyVulnerability[];
  /** Highest severity among vulnerabilities */
  highestSeverity: Severity;
  /** Fix available */
  fixAvailable: boolean;
}

/**
 * Vulnerability in a dependency
 */
export interface DependencyVulnerability {
  /** Vulnerability ID (CVE, GHSA, etc.) */
  id: string;
  /** CVE ID if available */
  cve?: string;
  /** GitHub Security Advisory ID */
  ghsa?: string;
  /** CWE identifiers */
  cwes: string[];
  /** Severity level */
  severity: Severity;
  /** CVSS score (0.0 - 10.0) */
  cvssScore?: number;
  /** CVSS vector string */
  cvssVector?: string;
  /** Title */
  title: string;
  /** Description */
  description: string;
  /** Affected version range */
  affectedVersions: string;
  /** Patched version (if available) */
  patchedVersion?: string;
  /** Vulnerability source */
  source: VulnerabilitySource;
  /** URL to advisory */
  url?: string;
  /** Publication date */
  publishedAt?: Date;
  /** Whether exploit is known */
  exploitAvailable?: boolean;
}

/**
 * Upgrade suggestion
 * @trace REQ-SEC-DEP-002
 */
export interface UpgradeSuggestion {
  /** Package name */
  packageName: string;
  /** Current version */
  currentVersion: string;
  /** Suggested version */
  suggestedVersion: string;
  /** Upgrade type */
  upgradeType: 'patch' | 'minor' | 'major';
  /** Whether this is a breaking change */
  breaking: boolean;
  /** Vulnerabilities fixed by this upgrade */
  fixesVulnerabilities: string[];
  /** Required peer dependency updates */
  peerUpdates?: {
    name: string;
    version: string;
  }[];
  /** Changelog URL */
  changelogUrl?: string;
  /** Release notes summary */
  releaseNotes?: string;
  /** Confidence in upgrade safety */
  confidence: number;
}

/**
 * Audit result
 * @trace REQ-SEC-DEP-001
 */
export interface AuditResult {
  /** Vulnerable dependencies found */
  vulnerableDependencies: VulnerableDependency[];
  /** Upgrade suggestions */
  upgradeSuggestions: UpgradeSuggestion[];
  /** Total dependencies scanned */
  totalDependencies: number;
  /** Direct dependencies scanned */
  directDependencies: number;
  /** Transitive dependencies scanned */
  transitiveDependencies: number;
  /** Audit duration in milliseconds */
  duration: number;
  /** Audit timestamp */
  timestamp: Date;
  /** Package manager detected */
  packageManager: 'npm' | 'yarn' | 'pnpm';
  /** Lock file path */
  lockFilePath?: string;
  /** Summary */
  summary: {
    critical: number;
    high: number;
    medium: number;
    low: number;
    total: number;
    fixable: number;
    breaking: number;
  };
}

/**
 * Audit options
 */
export interface AuditOptions {
  /** Include development dependencies */
  includeDevDependencies?: boolean;
  /** Minimum severity to report */
  minSeverity?: Severity;
  /** Vulnerability sources to check */
  sources?: VulnerabilitySource[];
  /** Ignore specific vulnerabilities by ID */
  ignoreVulnerabilities?: string[];
  /** Ignore specific packages */
  ignorePackages?: string[];
  /** Maximum depth for transitive dependencies */
  maxDepth?: number;
  /** Generate upgrade suggestions */
  suggestUpgrades?: boolean;
  /** Check for breaking changes */
  checkBreaking?: boolean;
  /** Custom registry URL */
  registryUrl?: string;
}

/**
 * SBOM (Software Bill of Materials) entry
 * @trace REQ-SEC-DEP-003
 */
export interface SBOMEntry {
  /** Package name */
  name: string;
  /** Package version */
  version: string;
  /** Package description */
  description?: string;
  /** License identifier (SPDX) */
  license?: string;
  /** Package author */
  author?: string;
  /** Package homepage */
  homepage?: string;
  /** Package repository URL */
  repository?: string;
  /** Dependency type */
  type: DependencyType;
  /** Whether this is a direct dependency */
  isDirect: boolean;
  /** Integrity hash (SHA-512) */
  integrity?: string;
  /** PURL (Package URL) */
  purl: string;
  /** CPE (Common Platform Enumeration) if available */
  cpe?: string;
  /** Known vulnerabilities count */
  vulnerabilityCount: number;
  /** Highest vulnerability severity */
  highestSeverity?: Severity;
}

/**
 * SBOM document
 * @trace REQ-SEC-DEP-003
 */
export interface SBOM {
  /** SBOM format version */
  formatVersion: string;
  /** SBOM spec (CycloneDX, SPDX) */
  spec: 'cyclonedx' | 'spdx';
  /** Project name */
  projectName: string;
  /** Project version */
  projectVersion: string;
  /** Generation timestamp */
  generatedAt: Date;
  /** Generator tool info */
  generator: {
    name: string;
    version: string;
  };
  /** All components */
  components: SBOMEntry[];
  /** Summary */
  summary: {
    totalComponents: number;
    directDependencies: number;
    transitiveDependencies: number;
    uniqueLicenses: string[];
    vulnerableComponents: number;
  };
}

/**
 * SBOM generation options
 */
export interface SBOMOptions {
  /** Output format */
  format: 'cyclonedx' | 'spdx';
  /** Include development dependencies */
  includeDevDependencies?: boolean;
  /** Include vulnerability data */
  includeVulnerabilities?: boolean;
  /** Include license data */
  includeLicenses?: boolean;
  /** Output file path */
  outputPath?: string;
}

/**
 * License compliance check result
 */
export interface LicenseCheckResult {
  /** Package name */
  packageName: string;
  /** Package version */
  version: string;
  /** Detected license */
  license: string;
  /** License category */
  category: 'permissive' | 'copyleft' | 'proprietary' | 'unknown';
  /** Whether license is approved */
  approved: boolean;
  /** Compliance issues */
  issues: string[];
}

/**
 * License policy
 */
export interface LicensePolicy {
  /** Allowed licenses */
  allowed: string[];
  /** Denied licenses */
  denied: string[];
  /** Require explicit approval for */
  requireApproval: string[];
}
