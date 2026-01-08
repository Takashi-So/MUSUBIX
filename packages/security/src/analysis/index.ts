/**
 * @fileoverview Analysis module entry point
 * @module @nahisaho/musubix-security/analysis
 */

export {
  VulnerabilityScanner,
  createVulnerabilityScanner,
  resetVulnCounter,
} from './vulnerability-scanner.js';

export {
  TaintAnalyzer,
  createTaintAnalyzer,
  resetTaintCounters,
} from './taint-analyzer.js';

export {
  EnhancedTaintAnalyzer,
  createEnhancedTaintAnalyzer,
  type EnhancedTaintOptions,
  type EnhancedTaintResult,
} from './enhanced-taint-analyzer.js';

export {
  SecretDetector,
  createSecretDetector,
  resetSecretCounter,
} from './secret-detector.js';

export {
  DependencyAuditor,
  createDependencyAuditor,
} from './dependency-auditor.js';
