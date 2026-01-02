/**
 * Traceability Module
 * 
 * @packageDocumentation
 * @module traceability
 */

export {
  TraceabilityManager,
  createTraceabilityManager,
  type TraceLinkType,
  type TraceableArtifact,
  type ArtifactStatus,
  type TraceLink,
  type MatrixEntry,
  type TraceabilityGap,
  type TraceabilityReport,
  type CoverageStats,
  type TraceabilityConfig,
  DEFAULT_TRACEABILITY_CONFIG,
} from './manager.js';

// Note: ArtifactType is exported from types module

export {
  ImpactAnalyzer,
  createImpactAnalyzer,
  type ChangeType,
  type ChangeProposal,
  type ImpactSeverity,
  type ImpactedArtifact,
  type ImpactAnalysisResult,
  type ImpactSummary,
  type RiskAssessment,
  type RiskFactor,
  type ImpactAnalyzerConfig,
  DEFAULT_IMPACT_CONFIG,
} from './impact.js';
