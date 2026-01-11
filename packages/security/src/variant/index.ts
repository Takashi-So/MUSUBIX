/**
 * @fileoverview Variant Analysis Module
 * @module @nahisaho/musubix-security/variant
 * @trace TSK-027, REQ-SEC-VARIANT-001
 */

// Model management
export {
  VulnerabilityModelManager,
  createModelManager,
  VULNERABILITY_MODELS,
  CWE_DATABASE,
} from './model.js';

// Vulnerability detection
export {
  VulnerabilityDetector,
  createDetector,
} from './detector.js';

// Security scanning
export {
  SecurityScanner,
  createScanner,
  scan,
  scanFile,
} from './scanner.js';

// SARIF reporting
export {
  SARIFGenerator,
  createSARIFGenerator,
  generateSARIF,
  exportSARIF,
} from './sarif.js';

// Re-export types
export type {
  VulnerabilityModel,
  SourcePattern,
  SinkPattern,
  SanitizerPattern,
  VulnerabilityCategory,
  VulnerabilityFinding,
  TaintFlow,
  FlowStep,
  ScanConfig,
  ScanResult,
  ScanProgress,
  ScanPhase,
  DetectorOptions,
  DetectorResult,
  SARIFReport,
  SARIFRun,
  SARIFResult,
  SARIFRule,
} from '../types/variant.js';
