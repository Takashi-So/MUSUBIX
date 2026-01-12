/**
 * @fileoverview Variant Analysis Module
 * @module @nahisaho/musubix-security/variant
 * @trace TSK-027, REQ-SEC-VARIANT-001
 */

// Model management
export {
  VulnerabilityModelManager,
  createModelManager,
  defaultModelManager,
  CWE_DATABASE,
} from './model.js';

// Vulnerability detection
export {
  TaintDetector,
  createDetector,
  type DetectorOptions,
  type DetectorResult,
} from './detector.js';

// Security scanning
export {
  SecurityScanner,
  createScanner,
  type ScannerOptions,
  type ScanProgress,
} from './scanner.js';

// SARIF reporting
export {
  SARIFGenerator,
  createSARIFGenerator,
  generateSARIF,
  generateSARIFFromFindings,
} from './sarif.js';

import { generateSARIF as _generateSARIF } from './sarif.js';

/**
 * Export SARIF report as JSON string
 */
export function exportSARIF(scanResult: import('../types/variant.js').ScanResult): string {
  const report = _generateSARIF(scanResult);
  return JSON.stringify(report, null, 2);
}

// Re-export types
export type {
  VulnerabilityModel,
  SourcePattern,
  SinkPattern,
  SanitizerPattern,
  VulnerabilityCategory,
  VulnerabilitySeverity,
  VulnerabilityFinding,
  TaintPathInfo,
  TaintNode,
  ScanConfig,
  ScanResult,
  SARIFReport,
  SARIFRun,
  SARIFResult,
  SARIFRule,
  SARIFLocation,
  SARIFCodeFlow,
} from '../types/variant.js';
