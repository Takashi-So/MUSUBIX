/**
 * @fileoverview MUSUBIX Security Package - Main Entry Point
 * @module @nahisaho/musubix-security
 * @version 1.8.0
 * 
 * Static analysis and vulnerability detection for TypeScript/JavaScript applications.
 * 
 * Features:
 * - Vulnerability scanning (SQL Injection, XSS, Command Injection, etc.)
 * - Taint analysis (data flow tracking)
 * - Secret detection (API keys, passwords, tokens)
 * - Dependency auditing (npm audit integration)
 * - Fix generation and verification
 * - Multiple report formats (JSON, SARIF, Markdown, HTML)
 * 
 * @example
 * ```typescript
 * import { runSecurityScan, createSecurityService } from '@nahisaho/musubix-security';
 * 
 * // Quick scan
 * const result = await runSecurityScan('./src');
 * console.log(`Found ${result.summary.totalVulnerabilities} vulnerabilities`);
 * 
 * // Full service usage
 * const service = createSecurityService();
 * const scanResult = await service.scan({
 *   target: './src',
 *   vulnerabilities: true,
 *   taint: true,
 *   secrets: true,
 *   dependencies: true,
 *   generateFixes: true,
 * });
 * ```
 */

// ============================================================================
// Types
// ============================================================================

export {
  // Vulnerability types
  type Vulnerability,
  type SourceLocation,
  type ScanResult,
  type SecurityRule,
  type Severity,
  type OWASPCategory,
  
  // Taint analysis types
  type TaintSource,
  type TaintSink,
  type TaintPath,
  type TaintResult,
  type SanitizerDefinition,
  BUILTIN_SANITIZERS,
  
  // Fix types
  type Fix,
  type CodeEdit,
  type ImportEdit,
  type VerificationResult,
  type VerificationStatus,
  type ApplyResult,
  type FixBatch,
  type FixStrategy,
  
  // Secret types
  type Secret,
  type SecretPattern,
  type SecretScanResult,
  BUILTIN_SECRET_PATTERNS,
  
  // Dependency types
  type AuditResult,
  type VulnerableDependency,
  type DependencyVulnerability,
  type SBOM,
  type SBOMEntry,
  type LicensePolicy,
  
  // Config types
  type SecurityConfig,
  type ReportConfig,
  type CacheConfig,
  type CIConfig,
  DEFAULT_CONFIG,
} from './types/index.js';

// ============================================================================
// Analysis
// ============================================================================

export {
  VulnerabilityScanner,
  TaintAnalyzer,
  SecretDetector,
  DependencyAuditor,
} from './analysis/index.js';

// ============================================================================
// Infrastructure
// ============================================================================

export {
  ASTParser,
  FileScanner,
  loadConfig,
  loadConfigSync,
  MemoryCache,
  FileCache,
  NoopCache,
  cacheKey,
  contentHash,
  type ICache,
} from './infrastructure/index.js';

// ============================================================================
// Services
// ============================================================================

export {
  // Main service
  SecurityService,
  createSecurityService,
  scanForVulnerabilities,
  runSecurityScan,
  type ScanOptions,
  type CompleteScanResult,
  
  // Fix services
  FixGenerator,
  createFixGenerator,
  FixVerifier,
  createFixVerifier,
  type VerificationOptions,
  
  // Report services
  ReportGenerator,
  createReportGenerator,
  type ReportFormat,
  type CombinedResults,
  type ReportMetadata,
} from './services/index.js';

// ============================================================================
// CLI
// ============================================================================

export { createSecurityCLI, runCLI } from './cli/index.js';

// ============================================================================
// MCP
// ============================================================================

export {
  SecurityMCPServer,
  startMCPServer,
  runMCPServer,
  SecurityToolHandler,
  createToolHandler,
  getToolSchemas,
  SECURITY_TOOLS,
  type ToolSchema,
  type ToolResult,
} from './mcp/index.js';
