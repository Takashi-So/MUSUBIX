/**
 * @fileoverview Intelligence layer components (Neuro-Symbolic)
 * @module @nahisaho/musubix-security/intelligence
 * @trace DES-SEC2-INT-001, DES-SEC2-INT-002, DES-SEC2-INT-003
 */

// Neuro-Symbolic Core
export {
  NeuroSymbolicCore,
  createNeuroSymbolicCore,
  StubLLMAnalyzer,
  StubKnowledgeQuery,
} from './neuro-symbolic-core.js';

// Threat Intelligence
export {
  ThreatIntelligence,
  createThreatIntelligence,
  quickIOCCheck,
  enrichWithThreatIntel,
  isCVEActivelyExploited,
  type IOCType,
  type ThreatSeverity,
  type ThreatConfidence,
  type IOC,
  type ThreatFeed,
  type ThreatMatch,
  type ThreatContext,
  type ThreatInfo,
  type ThreatIntelligenceOptions,
} from './threat-intelligence.js';

// Attack Pattern Matcher
export {
  AttackPatternMatcher,
  createAttackPatternMatcher,
  quickPatternMatch,
  mapToMitre,
  getMitreTechnique,
  type MitreTactic,
  type MitrePlatform,
  type MitreTechnique,
  type AttackPattern,
  type PatternMatch,
  type AttackChain,
  type AttackPatternMatcherOptions,
} from './attack-pattern-matcher.js';

// Risk Scorer
export {
  RiskScorer,
  createRiskScorer,
  calculateCVSS,
  quickRiskScore,
  scoreVulnerabilities,
  type AttackVector,
  type AttackComplexity,
  type PrivilegesRequired,
  type UserInteraction,
  type Scope,
  type Impact,
  type CVSSMetrics,
  type CVSSScore,
  type BusinessImpactCategory,
  type BusinessImpact,
  type AssetClassification,
  type RiskFactor,
  type RiskScore,
  type RiskSummary,
  type RiskScorerOptions,
} from './risk-scorer.js';

// Security Analytics
export {
  SecurityAnalytics,
  createSecurityAnalytics,
  generateDashboard,
  type TimePeriod,
  type MetricType,
  type SecurityMetric,
  type SecurityTrend,
  type VulnerabilityStats,
  type SecurityScorecard,
  type SecurityDashboard,
  type AnalyticsReport,
  type AnalyticsEvent,
  type SecurityAnalyticsOptions,
} from './security-analytics.js';

// Predictive Analyzer
export {
  PredictiveAnalyzer,
  createPredictiveAnalyzer,
  projectRisk,
  predictVulnerabilities,
  detectAnomalies,
  type PredictionConfidence,
  type RiskProjection,
  type VulnerabilityPrediction,
  type SecurityAnomaly,
  type ProactiveAlert,
  type SecurityForecast,
  type HistoricalDataPoint,
  type PredictiveAnalyzerOptions,
} from './predictive-analyzer.js';
