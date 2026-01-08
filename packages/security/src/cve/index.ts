/**
 * @fileoverview CVE module exports
 * @module @nahisaho/musubix-security/cve
 * @trace REQ-CVE-001
 */

export {
  NVDClient,
  NVDAPIError,
} from './nvd-client.js';

export type {
  NVDClientOptions,
  CVESearchResult,
} from './nvd-client.js';

export {
  RateLimiter,
  RateLimiterPool,
  withRateLimit,
} from './rate-limiter.js';

export type {
  RateLimiterOptions,
  RateLimitStatus,
} from './rate-limiter.js';

export {
  CPEMatcher,
  createCPESearchQuery,
  extractPackageFromCPE,
} from './cpe-matcher.js';

export type {
  CPEComponents,
  VersionRange,
  CPEMatch,
  VulnerabilityMatch,
} from './cpe-matcher.js';

export {
  DependencyParser,
  resolveVersionSpecifier,
  filterDependenciesForScanning,
  getUniquePackages,
} from './dependency-parser.js';

export type {
  DependencyType,
  ParsedDependency,
  PackageJson,
  PackageLockJson,
  PackageLockEntry,
  LegacyLockEntry,
  DependencyParserOptions,
  ParseResult,
} from './dependency-parser.js';

export {
  VulnerabilityScanner,
  scanProjectForVulnerabilities,
} from './vulnerability-scanner.js';

export type {
  VulnerabilityScannerOptions,
  ScanProgress,
  DetectedVulnerability,
  ScanResult,
} from './vulnerability-scanner.js';

export {
  CVECache,
  createMemoryCache,
  getDefaultCache,
  closeDefaultCache,
} from './cve-cache.js';

export type {
  CVECacheOptions,
  CacheEntry,
  CacheStats,
} from './cve-cache.js';

export {
  ReportGenerator,
  generateReport,
  generateReportToFile,
  getFormatFromExtension,
} from './report-generator.js';

export type {
  ReportFormat,
  ReportOptions,
  SARIFReport,
} from './report-generator.js';
