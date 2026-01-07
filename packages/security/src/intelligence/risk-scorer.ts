/**
 * @fileoverview Comprehensive Risk Scorer
 * @module @nahisaho/musubix-security/intelligence/risk-scorer
 * 
 * Provides comprehensive risk scoring, CVSS calculation,
 * business impact assessment, and risk prioritization.
 */

import type { Vulnerability } from '../types/index.js';
import type { ThreatContext } from './threat-intelligence.js';
import type { AttackChain, PatternMatch } from './attack-pattern-matcher.js';

// ============================================================================
// Types
// ============================================================================

/**
 * CVSS v3.1 Attack Vector
 */
export type AttackVector = 'network' | 'adjacent' | 'local' | 'physical';

/**
 * CVSS v3.1 Attack Complexity
 */
export type AttackComplexity = 'low' | 'high';

/**
 * CVSS v3.1 Privileges Required
 */
export type PrivilegesRequired = 'none' | 'low' | 'high';

/**
 * CVSS v3.1 User Interaction
 */
export type UserInteraction = 'none' | 'required';

/**
 * CVSS v3.1 Scope
 */
export type Scope = 'unchanged' | 'changed';

/**
 * CVSS v3.1 Impact
 */
export type Impact = 'none' | 'low' | 'high';

/**
 * CVSS v3.1 Metrics
 */
export interface CVSSMetrics {
  /** Attack Vector */
  attackVector: AttackVector;
  /** Attack Complexity */
  attackComplexity: AttackComplexity;
  /** Privileges Required */
  privilegesRequired: PrivilegesRequired;
  /** User Interaction */
  userInteraction: UserInteraction;
  /** Scope */
  scope: Scope;
  /** Confidentiality Impact */
  confidentialityImpact: Impact;
  /** Integrity Impact */
  integrityImpact: Impact;
  /** Availability Impact */
  availabilityImpact: Impact;
}

/**
 * CVSS Score Result
 */
export interface CVSSScore {
  /** Base score (0-10) */
  baseScore: number;
  /** Severity rating */
  severity: 'none' | 'low' | 'medium' | 'high' | 'critical';
  /** Vector string */
  vectorString: string;
  /** Component scores */
  components: {
    exploitability: number;
    impact: number;
  };
  /** Metrics used */
  metrics: CVSSMetrics;
}

/**
 * Business impact category
 */
export type BusinessImpactCategory =
  | 'financial'
  | 'reputation'
  | 'operational'
  | 'compliance'
  | 'safety'
  | 'privacy';

/**
 * Business impact assessment
 */
export interface BusinessImpact {
  /** Impact category */
  category: BusinessImpactCategory;
  /** Impact level (0-100) */
  level: number;
  /** Description */
  description: string;
  /** Potential loss estimate */
  potentialLoss?: {
    min: number;
    max: number;
    currency: string;
  };
}

/**
 * Asset classification
 */
export interface AssetClassification {
  /** Asset type */
  type: 'data' | 'system' | 'network' | 'application' | 'personnel';
  /** Criticality (0-100) */
  criticality: number;
  /** Data classification */
  dataClassification: 'public' | 'internal' | 'confidential' | 'restricted';
  /** Compliance requirements */
  complianceRequirements: string[];
}

/**
 * Risk factor
 */
export interface RiskFactor {
  /** Factor name */
  name: string;
  /** Factor weight (0-1) */
  weight: number;
  /** Factor score (0-100) */
  score: number;
  /** Description */
  description: string;
  /** Evidence */
  evidence?: string[];
}

/**
 * Risk score result
 */
export interface RiskScore {
  /** Overall risk score (0-100) */
  overallScore: number;
  /** Risk level */
  riskLevel: 'critical' | 'high' | 'medium' | 'low' | 'informational';
  /** CVSS score */
  cvssScore: CVSSScore;
  /** Business impact scores */
  businessImpacts: BusinessImpact[];
  /** Contributing factors */
  factors: RiskFactor[];
  /** Asset context */
  assetContext?: AssetClassification;
  /** Threat context */
  threatContext?: Partial<ThreatContext>;
  /** Confidence (0-1) */
  confidence: number;
  /** Recommendations ordered by priority */
  recommendations: string[];
  /** Time to remediate estimate */
  remediationTimeEstimate: {
    min: number;
    max: number;
    unit: 'hours' | 'days' | 'weeks';
  };
}

/**
 * Aggregated risk summary
 */
export interface RiskSummary {
  /** Total vulnerabilities */
  totalVulnerabilities: number;
  /** Average risk score */
  averageRiskScore: number;
  /** Risk distribution */
  distribution: {
    critical: number;
    high: number;
    medium: number;
    low: number;
    informational: number;
  };
  /** Top risks */
  topRisks: {
    vulnerability: Vulnerability;
    riskScore: RiskScore;
  }[];
  /** Total business impact */
  totalBusinessImpact: {
    category: BusinessImpactCategory;
    totalScore: number;
  }[];
  /** Overall security posture (0-100) */
  securityPosture: number;
  /** Trend indicator */
  trend: 'improving' | 'stable' | 'declining';
}

/**
 * Risk Scorer options
 */
export interface RiskScorerOptions {
  /** Asset classification for context */
  assetClassification?: AssetClassification;
  /** Business impact weights */
  businessImpactWeights?: Partial<Record<BusinessImpactCategory, number>>;
  /** Custom risk factors */
  customFactors?: RiskFactor[];
  /** Enable threat context enrichment */
  enableThreatEnrichment?: boolean;
  /** Organization risk tolerance (0-100) */
  riskTolerance?: number;
}

// ============================================================================
// CVSS Constants
// ============================================================================

const CVSS_WEIGHTS = {
  attackVector: { network: 0.85, adjacent: 0.62, local: 0.55, physical: 0.2 },
  attackComplexity: { low: 0.77, high: 0.44 },
  privilegesRequired: {
    unchanged: { none: 0.85, low: 0.62, high: 0.27 },
    changed: { none: 0.85, low: 0.68, high: 0.5 },
  },
  userInteraction: { none: 0.85, required: 0.62 },
  impact: { none: 0, low: 0.22, high: 0.56 },
};

// Vulnerability type to CVSS metrics mapping
const VULN_TYPE_CVSS_MAP: Record<string, Partial<CVSSMetrics>> = {
  'xss': {
    attackVector: 'network',
    attackComplexity: 'low',
    privilegesRequired: 'none',
    userInteraction: 'required',
    scope: 'changed',
    confidentialityImpact: 'low',
    integrityImpact: 'low',
    availabilityImpact: 'none',
  },
  'sql-injection': {
    attackVector: 'network',
    attackComplexity: 'low',
    privilegesRequired: 'none',
    userInteraction: 'none',
    scope: 'unchanged',
    confidentialityImpact: 'high',
    integrityImpact: 'high',
    availabilityImpact: 'high',
  },
  'command-injection': {
    attackVector: 'network',
    attackComplexity: 'low',
    privilegesRequired: 'low',
    userInteraction: 'none',
    scope: 'changed',
    confidentialityImpact: 'high',
    integrityImpact: 'high',
    availabilityImpact: 'high',
  },
  'path-traversal': {
    attackVector: 'network',
    attackComplexity: 'low',
    privilegesRequired: 'none',
    userInteraction: 'none',
    scope: 'unchanged',
    confidentialityImpact: 'high',
    integrityImpact: 'low',
    availabilityImpact: 'none',
  },
  'ssrf': {
    attackVector: 'network',
    attackComplexity: 'low',
    privilegesRequired: 'none',
    userInteraction: 'none',
    scope: 'changed',
    confidentialityImpact: 'low',
    integrityImpact: 'low',
    availabilityImpact: 'low',
  },
  'hardcoded-secret': {
    attackVector: 'local',
    attackComplexity: 'low',
    privilegesRequired: 'none',
    userInteraction: 'none',
    scope: 'unchanged',
    confidentialityImpact: 'high',
    integrityImpact: 'high',
    availabilityImpact: 'none',
  },
  'weak-crypto': {
    attackVector: 'network',
    attackComplexity: 'high',
    privilegesRequired: 'none',
    userInteraction: 'none',
    scope: 'unchanged',
    confidentialityImpact: 'high',
    integrityImpact: 'none',
    availabilityImpact: 'none',
  },
  'prototype-pollution': {
    attackVector: 'network',
    attackComplexity: 'low',
    privilegesRequired: 'none',
    userInteraction: 'none',
    scope: 'unchanged',
    confidentialityImpact: 'low',
    integrityImpact: 'low',
    availabilityImpact: 'low',
  },
};

// Default business impact weights
const DEFAULT_BUSINESS_IMPACT_WEIGHTS: Record<BusinessImpactCategory, number> = {
  financial: 0.25,
  reputation: 0.2,
  operational: 0.2,
  compliance: 0.15,
  safety: 0.1,
  privacy: 0.1,
};

// ============================================================================
// RiskScorer Class
// ============================================================================

/**
 * Comprehensive Risk Scorer
 */
export class RiskScorer {
  private options: Required<RiskScorerOptions>;

  constructor(options: RiskScorerOptions = {}) {
    this.options = {
      assetClassification: options.assetClassification ?? {
        type: 'application',
        criticality: 50,
        dataClassification: 'internal',
        complianceRequirements: [],
      },
      businessImpactWeights: {
        ...DEFAULT_BUSINESS_IMPACT_WEIGHTS,
        ...options.businessImpactWeights,
      },
      customFactors: options.customFactors ?? [],
      enableThreatEnrichment: options.enableThreatEnrichment ?? true,
      riskTolerance: options.riskTolerance ?? 50,
    };
  }

  /**
   * Calculate CVSS score for a vulnerability
   */
  calculateCVSS(vulnerability: Vulnerability): CVSSScore {
    // Get base metrics from vulnerability type mapping
    const baseMetrics = VULN_TYPE_CVSS_MAP[vulnerability.type] ?? {};
    
    // Apply defaults
    const metrics: CVSSMetrics = {
      attackVector: baseMetrics.attackVector ?? 'network',
      attackComplexity: baseMetrics.attackComplexity ?? 'low',
      privilegesRequired: baseMetrics.privilegesRequired ?? 'none',
      userInteraction: baseMetrics.userInteraction ?? 'none',
      scope: baseMetrics.scope ?? 'unchanged',
      confidentialityImpact: baseMetrics.confidentialityImpact ?? 'low',
      integrityImpact: baseMetrics.integrityImpact ?? 'low',
      availabilityImpact: baseMetrics.availabilityImpact ?? 'low',
    };

    // Adjust based on vulnerability severity
    if (vulnerability.severity === 'critical') {
      metrics.confidentialityImpact = 'high';
      metrics.integrityImpact = 'high';
      metrics.availabilityImpact = 'high';
    } else if (vulnerability.severity === 'high') {
      metrics.confidentialityImpact = 'high';
      metrics.integrityImpact = 'high';
    }

    // Calculate exploitability score
    const exploitability = this.calculateExploitability(metrics);
    
    // Calculate impact score
    const impact = this.calculateImpact(metrics);

    // Calculate base score
    let baseScore: number;
    if (impact <= 0) {
      baseScore = 0;
    } else if (metrics.scope === 'unchanged') {
      baseScore = Math.min(10, 1.08 * (impact + exploitability));
    } else {
      baseScore = Math.min(10, 1.08 * (impact + exploitability));
    }

    // Round to one decimal
    baseScore = Math.round(baseScore * 10) / 10;

    // Determine severity
    const severity = this.cvssToSeverity(baseScore);

    // Generate vector string
    const vectorString = this.generateVectorString(metrics);

    return {
      baseScore,
      severity,
      vectorString,
      components: {
        exploitability,
        impact,
      },
      metrics,
    };
  }

  /**
   * Calculate exploitability component
   */
  private calculateExploitability(metrics: CVSSMetrics): number {
    const av = CVSS_WEIGHTS.attackVector[metrics.attackVector];
    const ac = CVSS_WEIGHTS.attackComplexity[metrics.attackComplexity];
    const pr = CVSS_WEIGHTS.privilegesRequired[metrics.scope][metrics.privilegesRequired];
    const ui = CVSS_WEIGHTS.userInteraction[metrics.userInteraction];

    return 8.22 * av * ac * pr * ui;
  }

  /**
   * Calculate impact component
   */
  private calculateImpact(metrics: CVSSMetrics): number {
    const isc = this.calculateISC(metrics);

    if (metrics.scope === 'unchanged') {
      return 6.42 * isc;
    } else {
      return 7.52 * (isc - 0.029) - 3.25 * Math.pow(isc - 0.02, 15);
    }
  }

  /**
   * Calculate Impact Sub-Component
   */
  private calculateISC(metrics: CVSSMetrics): number {
    const c = CVSS_WEIGHTS.impact[metrics.confidentialityImpact];
    const i = CVSS_WEIGHTS.impact[metrics.integrityImpact];
    const a = CVSS_WEIGHTS.impact[metrics.availabilityImpact];

    return 1 - (1 - c) * (1 - i) * (1 - a);
  }

  /**
   * Convert CVSS score to severity rating
   */
  private cvssToSeverity(score: number): CVSSScore['severity'] {
    if (score === 0) return 'none';
    if (score < 4) return 'low';
    if (score < 7) return 'medium';
    if (score < 9) return 'high';
    return 'critical';
  }

  /**
   * Generate CVSS vector string
   */
  private generateVectorString(metrics: CVSSMetrics): string {
    const avMap = { network: 'N', adjacent: 'A', local: 'L', physical: 'P' };
    const acMap = { low: 'L', high: 'H' };
    const prMap = { none: 'N', low: 'L', high: 'H' };
    const uiMap = { none: 'N', required: 'R' };
    const sMap = { unchanged: 'U', changed: 'C' };
    const impactMap = { none: 'N', low: 'L', high: 'H' };

    return `CVSS:3.1/AV:${avMap[metrics.attackVector]}/AC:${acMap[metrics.attackComplexity]}/PR:${prMap[metrics.privilegesRequired]}/UI:${uiMap[metrics.userInteraction]}/S:${sMap[metrics.scope]}/C:${impactMap[metrics.confidentialityImpact]}/I:${impactMap[metrics.integrityImpact]}/A:${impactMap[metrics.availabilityImpact]}`;
  }

  /**
   * Assess business impact
   */
  assessBusinessImpact(vulnerability: Vulnerability): BusinessImpact[] {
    const impacts: BusinessImpact[] = [];
    const asset = this.options.assetClassification;

    // Financial impact
    const financialLevel = this.calculateFinancialImpact(vulnerability, asset);
    impacts.push({
      category: 'financial',
      level: financialLevel,
      description: this.getFinancialDescription(vulnerability, financialLevel),
      potentialLoss: this.estimatePotentialLoss(vulnerability, financialLevel),
    });

    // Reputation impact
    const reputationLevel = this.calculateReputationImpact(vulnerability, asset);
    impacts.push({
      category: 'reputation',
      level: reputationLevel,
      description: this.getReputationDescription(vulnerability, reputationLevel),
    });

    // Operational impact
    const operationalLevel = this.calculateOperationalImpact(vulnerability, asset);
    impacts.push({
      category: 'operational',
      level: operationalLevel,
      description: this.getOperationalDescription(vulnerability, operationalLevel),
    });

    // Compliance impact
    if (asset.complianceRequirements.length > 0) {
      const complianceLevel = this.calculateComplianceImpact(vulnerability, asset);
      impacts.push({
        category: 'compliance',
        level: complianceLevel,
        description: this.getComplianceDescription(vulnerability, complianceLevel, asset),
      });
    }

    // Privacy impact
    if (vulnerability.type.includes('injection') || vulnerability.type === 'path-traversal') {
      const privacyLevel = this.calculatePrivacyImpact(vulnerability, asset);
      impacts.push({
        category: 'privacy',
        level: privacyLevel,
        description: this.getPrivacyDescription(vulnerability, privacyLevel),
      });
    }

    return impacts;
  }

  /**
   * Calculate financial impact level
   */
  private calculateFinancialImpact(
    vulnerability: Vulnerability,
    asset: AssetClassification
  ): number {
    let base = 30;

    // Adjust based on severity
    const severityMultiplier = {
      critical: 2.5,
      high: 2.0,
      medium: 1.5,
      low: 1.0,
      info: 0.5,
    }[vulnerability.severity];

    base *= severityMultiplier;

    // Adjust based on asset criticality
    base *= (asset.criticality / 50);

    // Adjust based on data classification
    const classificationMultiplier = {
      public: 0.5,
      internal: 1.0,
      confidential: 1.5,
      restricted: 2.0,
    }[asset.dataClassification];

    base *= classificationMultiplier;

    return Math.min(100, Math.round(base));
  }

  /**
   * Get financial impact description
   */
  private getFinancialDescription(
    vulnerability: Vulnerability,
    level: number
  ): string {
    if (level >= 80) {
      return `Critical financial exposure. ${vulnerability.type} could lead to significant monetary losses.`;
    } else if (level >= 60) {
      return `High financial risk. Exploitation could result in substantial costs.`;
    } else if (level >= 40) {
      return `Moderate financial impact expected if exploited.`;
    } else {
      return `Limited direct financial impact expected.`;
    }
  }

  /**
   * Estimate potential loss
   */
  private estimatePotentialLoss(
    _vulnerability: Vulnerability,
    level: number
  ): BusinessImpact['potentialLoss'] {
    // Base estimates (simplified)
    const baseMin = level * 100;
    const baseMax = level * 1000;

    return {
      min: baseMin,
      max: baseMax,
      currency: 'USD',
    };
  }

  /**
   * Calculate reputation impact
   */
  private calculateReputationImpact(
    vulnerability: Vulnerability,
    asset: AssetClassification
  ): number {
    let base = 25;

    // High visibility vulnerabilities
    if (['xss', 'sql-injection', 'hardcoded-secret'].includes(vulnerability.type)) {
      base += 25;
    }

    // Data breach potential
    if (asset.dataClassification === 'confidential' || asset.dataClassification === 'restricted') {
      base += 20;
    }

    // Severity adjustment
    if (vulnerability.severity === 'critical') {
      base *= 1.5;
    }

    return Math.min(100, Math.round(base));
  }

  /**
   * Get reputation impact description
   */
  private getReputationDescription(
    _vulnerability: Vulnerability,
    level: number
  ): string {
    if (level >= 70) {
      return 'Severe reputation damage likely if publicly disclosed or exploited.';
    } else if (level >= 50) {
      return 'Moderate reputation risk. Public disclosure would be damaging.';
    } else {
      return 'Limited reputation impact expected.';
    }
  }

  /**
   * Calculate operational impact
   */
  private calculateOperationalImpact(
    vulnerability: Vulnerability,
    asset: AssetClassification
  ): number {
    let base = 20;

    // Availability impacts
    if (['command-injection', 'sql-injection'].includes(vulnerability.type)) {
      base += 30;
    }

    // System criticality
    base *= (asset.criticality / 50);

    return Math.min(100, Math.round(base));
  }

  /**
   * Get operational impact description
   */
  private getOperationalDescription(
    _vulnerability: Vulnerability,
    level: number
  ): string {
    if (level >= 70) {
      return 'High operational disruption likely. Could cause system outages.';
    } else if (level >= 40) {
      return 'Moderate operational impact. May affect system availability.';
    } else {
      return 'Limited operational impact expected.';
    }
  }

  /**
   * Calculate compliance impact
   */
  private calculateComplianceImpact(
    vulnerability: Vulnerability,
    asset: AssetClassification
  ): number {
    let base = 30;

    // Compliance requirements
    const highRiskCompliance = ['PCI-DSS', 'HIPAA', 'GDPR', 'SOX'];
    const hasHighRisk = asset.complianceRequirements.some(req =>
      highRiskCompliance.includes(req)
    );

    if (hasHighRisk) {
      base += 40;
    }

    // Data vulnerabilities have higher compliance impact
    if (['sql-injection', 'path-traversal', 'hardcoded-secret'].includes(vulnerability.type)) {
      base += 20;
    }

    return Math.min(100, Math.round(base));
  }

  /**
   * Get compliance impact description
   */
  private getComplianceDescription(
    _vulnerability: Vulnerability,
    level: number,
    asset: AssetClassification
  ): string {
    const reqs = asset.complianceRequirements.join(', ');
    if (level >= 70) {
      return `Critical compliance violation risk for ${reqs}.`;
    } else if (level >= 40) {
      return `May affect compliance with ${reqs}.`;
    } else {
      return 'Limited compliance impact.';
    }
  }

  /**
   * Calculate privacy impact
   */
  private calculatePrivacyImpact(
    vulnerability: Vulnerability,
    asset: AssetClassification
  ): number {
    let base = 30;

    if (asset.dataClassification === 'restricted') {
      base += 40;
    } else if (asset.dataClassification === 'confidential') {
      base += 25;
    }

    if (vulnerability.severity === 'critical' || vulnerability.severity === 'high') {
      base += 20;
    }

    return Math.min(100, Math.round(base));
  }

  /**
   * Get privacy impact description
   */
  private getPrivacyDescription(
    _vulnerability: Vulnerability,
    level: number
  ): string {
    if (level >= 70) {
      return 'High risk of personal data exposure. May trigger breach notification requirements.';
    } else if (level >= 40) {
      return 'Moderate privacy risk. Could expose user data.';
    } else {
      return 'Limited privacy impact expected.';
    }
  }

  /**
   * Calculate comprehensive risk score for a vulnerability
   */
  scoreVulnerability(
    vulnerability: Vulnerability,
    threatContext?: ThreatContext
  ): RiskScore {
    // Calculate CVSS
    const cvssScore = this.calculateCVSS(vulnerability);

    // Assess business impact
    const businessImpacts = this.assessBusinessImpact(vulnerability);

    // Calculate risk factors
    const factors = this.calculateRiskFactors(vulnerability, cvssScore, businessImpacts, threatContext);

    // Calculate overall score
    let overallScore = 0;
    for (const factor of factors) {
      overallScore += factor.score * factor.weight;
    }

    // Apply threat context multiplier
    if (threatContext?.riskMultiplier) {
      overallScore *= threatContext.riskMultiplier;
    }

    // Cap at 100
    overallScore = Math.min(100, Math.round(overallScore));

    // Determine risk level
    const riskLevel = this.scoreToRiskLevel(overallScore);

    // Calculate confidence
    const confidence = this.calculateConfidence(vulnerability, factors);

    // Generate recommendations
    const recommendations = this.generateRecommendations(
      vulnerability,
      cvssScore,
      businessImpacts,
      threatContext
    );

    // Estimate remediation time
    const remediationTimeEstimate = this.estimateRemediationTime(vulnerability);

    return {
      overallScore,
      riskLevel,
      cvssScore,
      businessImpacts,
      factors,
      assetContext: this.options.assetClassification,
      threatContext,
      confidence,
      recommendations,
      remediationTimeEstimate,
    };
  }

  /**
   * Calculate risk factors
   */
  private calculateRiskFactors(
    vulnerability: Vulnerability,
    cvssScore: CVSSScore,
    businessImpacts: BusinessImpact[],
    threatContext?: ThreatContext
  ): RiskFactor[] {
    const factors: RiskFactor[] = [];

    // Technical severity factor
    factors.push({
      name: 'Technical Severity',
      weight: 0.3,
      score: cvssScore.baseScore * 10,
      description: `CVSS ${cvssScore.baseScore} (${cvssScore.severity})`,
      evidence: [cvssScore.vectorString],
    });

    // Business impact factor
    const avgBusinessImpact = businessImpacts.reduce((sum, bi) => sum + bi.level, 0) / businessImpacts.length;
    factors.push({
      name: 'Business Impact',
      weight: 0.25,
      score: avgBusinessImpact,
      description: 'Aggregated business impact assessment',
      evidence: businessImpacts.map(bi => `${bi.category}: ${bi.level}`),
    });

    // Exploitability factor
    const exploitability = this.assessExploitability(vulnerability);
    factors.push({
      name: 'Exploitability',
      weight: 0.2,
      score: exploitability,
      description: 'Likelihood and ease of exploitation',
    });

    // Threat landscape factor
    if (threatContext) {
      factors.push({
        name: 'Threat Landscape',
        weight: 0.15,
        score: threatContext.activelyExploited ? 100 : 50,
        description: threatContext.activelyExploited
          ? 'Actively exploited in the wild'
          : 'No active exploitation known',
      });
    } else {
      factors.push({
        name: 'Threat Landscape',
        weight: 0.15,
        score: 30,
        description: 'Threat intelligence not available',
      });
    }

    // Asset criticality factor
    factors.push({
      name: 'Asset Criticality',
      weight: 0.1,
      score: this.options.assetClassification.criticality,
      description: `Asset type: ${this.options.assetClassification.type}`,
    });

    // Add custom factors
    for (const custom of this.options.customFactors) {
      factors.push(custom);
    }

    return factors;
  }

  /**
   * Assess exploitability
   */
  private assessExploitability(vulnerability: Vulnerability): number {
    let score = 50;

    // Known vulnerability types are more exploitable
    const highExploitabilityTypes = ['sql-injection', 'command-injection', 'xss'];
    if (highExploitabilityTypes.includes(vulnerability.type)) {
      score += 30;
    }

    // Severity indicates exploitability
    if (vulnerability.severity === 'critical') {
      score += 20;
    } else if (vulnerability.severity === 'high') {
      score += 10;
    }

    // Public exploit availability would increase this
    // (In real implementation, check exploit databases)

    return Math.min(100, score);
  }

  /**
   * Convert score to risk level
   */
  private scoreToRiskLevel(score: number): RiskScore['riskLevel'] {
    if (score >= 90) return 'critical';
    if (score >= 70) return 'high';
    if (score >= 40) return 'medium';
    if (score >= 20) return 'low';
    return 'informational';
  }

  /**
   * Calculate confidence
   */
  private calculateConfidence(
    vulnerability: Vulnerability,
    factors: RiskFactor[]
  ): number {
    let confidence = 0.7; // Base confidence

    // More factors increase confidence
    if (factors.length >= 5) {
      confidence += 0.1;
    }

    // Known vulnerability types have higher confidence
    if (VULN_TYPE_CVSS_MAP[vulnerability.type]) {
      confidence += 0.1;
    }

    // Reduce for info level
    if (vulnerability.severity === 'info') {
      confidence -= 0.1;
    }

    return Math.min(1, Math.max(0, confidence));
  }

  /**
   * Generate prioritized recommendations
   */
  private generateRecommendations(
    vulnerability: Vulnerability,
    cvssScore: CVSSScore,
    businessImpacts: BusinessImpact[],
    threatContext?: ThreatContext
  ): string[] {
    const recommendations: string[] = [];

    // Urgency-based recommendations
    if (threatContext?.activelyExploited) {
      recommendations.push('URGENT: Apply patches immediately - active exploitation detected');
    }

    if (cvssScore.baseScore >= 9) {
      recommendations.push('Critical vulnerability - prioritize remediation within 24 hours');
    } else if (cvssScore.baseScore >= 7) {
      recommendations.push('High severity - remediate within 1 week');
    }

    // Type-specific recommendations
    switch (vulnerability.type) {
      case 'injection':
        recommendations.push('Use parameterized queries or prepared statements');
        recommendations.push('Implement input validation');
        break;
      case 'xss':
        recommendations.push('Implement output encoding');
        recommendations.push('Use Content Security Policy headers');
        break;
      case 'command-injection':
        recommendations.push('Avoid shell commands with user input');
        recommendations.push('Use safe APIs instead of exec/spawn');
        break;
      case 'sensitive-exposure':
        recommendations.push('Move credentials to secure secrets management');
        recommendations.push('Rotate exposed credentials');
        break;
      case 'path-traversal':
        recommendations.push('Validate and sanitize file paths');
        recommendations.push('Use allowlists for accessible directories');
        break;
    }

    // Business impact recommendations
    const highImpacts = businessImpacts.filter(bi => bi.level >= 70);
    for (const impact of highImpacts) {
      recommendations.push(`Address ${impact.category} risk: ${impact.description}`);
    }

    return recommendations;
  }

  /**
   * Estimate remediation time
   */
  private estimateRemediationTime(
    vulnerability: Vulnerability
  ): RiskScore['remediationTimeEstimate'] {
    // Base estimates by type
    const estimates: Record<string, { min: number; max: number; unit: 'hours' | 'days' }> = {
      'sensitive-exposure': { min: 1, max: 4, unit: 'hours' },
      'xss': { min: 2, max: 8, unit: 'hours' },
      'injection': { min: 4, max: 16, unit: 'hours' },
      'command-injection': { min: 4, max: 24, unit: 'hours' },
      'path-traversal': { min: 2, max: 8, unit: 'hours' },
      'ssrf': { min: 4, max: 16, unit: 'hours' },
      'broken-auth': { min: 1, max: 3, unit: 'days' },
      'prototype-pollution': { min: 2, max: 8, unit: 'hours' },
    };

    return estimates[vulnerability.type] ?? { min: 4, max: 24, unit: 'hours' };
  }

  /**
   * Score multiple vulnerabilities and create summary
   */
  scoreBatch(vulnerabilities: Vulnerability[]): RiskSummary {
    const scores = vulnerabilities.map(v => ({
      vulnerability: v,
      riskScore: this.scoreVulnerability(v),
    }));

    // Calculate distribution
    const distribution = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
      informational: 0,
    };

    let totalScore = 0;
    for (const { riskScore } of scores) {
      distribution[riskScore.riskLevel]++;
      totalScore += riskScore.overallScore;
    }

    // Calculate average
    const averageRiskScore = scores.length > 0
      ? Math.round(totalScore / scores.length)
      : 0;

    // Get top risks
    const topRisks = scores
      .sort((a, b) => b.riskScore.overallScore - a.riskScore.overallScore)
      .slice(0, 5);

    // Aggregate business impact
    const impactTotals = new Map<BusinessImpactCategory, number>();
    for (const { riskScore } of scores) {
      for (const impact of riskScore.businessImpacts) {
        const current = impactTotals.get(impact.category) || 0;
        impactTotals.set(impact.category, current + impact.level);
      }
    }

    const totalBusinessImpact = Array.from(impactTotals.entries()).map(
      ([category, totalScore]) => ({ category, totalScore })
    );

    // Calculate security posture (inverse of risk)
    const securityPosture = Math.max(0, 100 - averageRiskScore);

    return {
      totalVulnerabilities: vulnerabilities.length,
      averageRiskScore,
      distribution,
      topRisks,
      totalBusinessImpact,
      securityPosture,
      trend: 'stable', // Would be calculated from historical data
    };
  }

  /**
   * Score attack chain
   */
  scoreAttackChain(chain: AttackChain): RiskScore {
    // Create a synthetic vulnerability for the chain
    const syntheticVuln: Vulnerability = {
      id: chain.id,
      type: 'code-injection', // Use a valid type for attack chains
      severity: chain.riskScore >= 80 ? 'critical' : chain.riskScore >= 60 ? 'high' : 'medium',
      description: chain.name,
      recommendation: chain.mitigations.join('; '),
      location: chain.patterns[0]?.location ?? {
        file: 'unknown',
        startLine: 0,
        endLine: 0,
        startColumn: 0,
        endColumn: 0,
      },
      cwes: [],
      confidence: 0.9,
      ruleId: 'attack-chain',
      detectedAt: new Date(),
    };

    const baseScore = this.scoreVulnerability(syntheticVuln);

    // Adjust for chain complexity
    const chainMultiplier = 1 + (chain.killChainStages.length * 0.1);
    baseScore.overallScore = Math.min(100, Math.round(baseScore.overallScore * chainMultiplier));

    // Add chain-specific recommendations
    baseScore.recommendations.unshift(
      `Attack chain detected covering ${chain.killChainStages.length} kill chain stages`
    );

    return baseScore;
  }

  /**
   * Score pattern match
   */
  scorePatternMatch(match: PatternMatch): number {
    const severityScore = {
      critical: 90,
      high: 70,
      medium: 50,
      low: 25,
    }[match.pattern.severity];

    return Math.round(severityScore * match.confidence);
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create a RiskScorer instance
 */
export function createRiskScorer(options?: RiskScorerOptions): RiskScorer {
  return new RiskScorer(options);
}

/**
 * Quick CVSS calculation
 */
export function calculateCVSS(vulnerability: Vulnerability): CVSSScore {
  const scorer = createRiskScorer();
  return scorer.calculateCVSS(vulnerability);
}

/**
 * Quick risk score
 */
export function quickRiskScore(vulnerability: Vulnerability): RiskScore {
  const scorer = createRiskScorer();
  return scorer.scoreVulnerability(vulnerability);
}

/**
 * Score multiple vulnerabilities
 */
export function scoreVulnerabilities(vulnerabilities: Vulnerability[]): RiskSummary {
  const scorer = createRiskScorer();
  return scorer.scoreBatch(vulnerabilities);
}
