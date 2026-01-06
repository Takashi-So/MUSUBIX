/**
 * @fileoverview Services module entry point
 * @module @nahisaho/musubix-security/services
 */

// Fix generator
export {
  FixGenerator,
  createFixGenerator,
} from './fix-generator.js';

// Fix verifier
export {
  FixVerifier,
  createFixVerifier,
  type VerificationOptions,
} from './fix-verifier.js';

// Report generator
export {
  ReportGenerator,
  createReportGenerator,
  type ReportFormat,
  type CombinedResults,
  type ReportMetadata,
} from './report-generator.js';

// Security service (main facade)
export {
  SecurityService,
  createSecurityService,
  scanForVulnerabilities,
  runSecurityScan,
  type ScanOptions,
  type CompleteScanResult,
} from './security-service.js';
