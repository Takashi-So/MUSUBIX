/**
 * @fileoverview Neuro-Symbolic Core - integrates neural (LLM) and symbolic reasoning
 * @module @nahisaho/musubix-security/intelligence/neuro-symbolic-core
 * @trace DES-SEC2-INT-001, REQ-SEC2-INT-001, REQ-SEC2-INT-002, REQ-SEC2-INT-003
 */

import type { Vulnerability, Severity } from '../types/vulnerability.js';
import type {
  Evidence,
  NeuralResult,
  SymbolicResult,
  KnowledgeGraphMatch,
  FinalDecision,
  NeuroSymbolicResult,
  IntegrationOptions,
  INeuroSymbolicCore,
  ILLMAnalyzer,
  IKnowledgeQuery,
} from '../types/neuro-symbolic.js';
import type { TaintPath } from '../types/taint.js';

/**
 * Default integration options
 */
const DEFAULT_OPTIONS: Required<IntegrationOptions> = {
  neuralThreshold: 0.8,
  requireSymbolicValidation: true,
  llmProvider: 'openai',
  maxTokens: 2000,
  kgQueryDepth: 3,
};

/**
 * Security patterns for symbolic matching
 */
const SECURITY_PATTERNS = new Map<string, { cwes: string[]; severity: Severity }>([
  ['sql-injection', { cwes: ['CWE-89'], severity: 'critical' }],
  ['command-injection', { cwes: ['CWE-78'], severity: 'critical' }],
  ['xss', { cwes: ['CWE-79'], severity: 'high' }],
  ['path-traversal', { cwes: ['CWE-22'], severity: 'high' }],
  ['ssrf', { cwes: ['CWE-918'], severity: 'high' }],
  ['insecure-deserialization', { cwes: ['CWE-502'], severity: 'critical' }],
  ['hardcoded-secret', { cwes: ['CWE-798'], severity: 'high' }],
  ['missing-authentication', { cwes: ['CWE-306'], severity: 'critical' }],
  ['missing-authorization', { cwes: ['CWE-862'], severity: 'high' }],
  ['sensitive-data-exposure', { cwes: ['CWE-200'], severity: 'medium' }],
]);

/**
 * Security rules for inference
 */
const SECURITY_RULES = [
  {
    id: 'RULE-001',
    name: 'Unsanitized User Input to SQL',
    pattern: 'user_input -> sql_query',
    cwes: ['CWE-89'],
  },
  {
    id: 'RULE-002',
    name: 'Unsanitized User Input to Shell',
    pattern: 'user_input -> exec|spawn',
    cwes: ['CWE-78'],
  },
  {
    id: 'RULE-003',
    name: 'Unsanitized User Input to HTML',
    pattern: 'user_input -> html_output',
    cwes: ['CWE-79'],
  },
  {
    id: 'RULE-004',
    name: 'Unsanitized User Input to File Path',
    pattern: 'user_input -> file_path',
    cwes: ['CWE-22'],
  },
  {
    id: 'RULE-005',
    name: 'Unsanitized User Input to URL',
    pattern: 'user_input -> http_request',
    cwes: ['CWE-918'],
  },
];

/**
 * Neuro-Symbolic Core implementation
 * Integrates neural (LLM) analysis with symbolic (knowledge graph) reasoning
 * @trace DES-SEC2-INT-001
 */
export class NeuroSymbolicCore implements INeuroSymbolicCore {
  private options: Required<IntegrationOptions>;
  private llmAnalyzer: ILLMAnalyzer | null = null;
  private knowledgeQuery: IKnowledgeQuery | null = null;

  constructor(options: IntegrationOptions = {}) {
    this.options = { ...DEFAULT_OPTIONS, ...options };
  }

  /**
   * Set LLM analyzer implementation
   */
  setLLMAnalyzer(analyzer: ILLMAnalyzer): void {
    this.llmAnalyzer = analyzer;
  }

  /**
   * Set knowledge query implementation
   */
  setKnowledgeQuery(query: IKnowledgeQuery): void {
    this.knowledgeQuery = query;
  }

  /**
   * Integrate neural and symbolic analysis for a vulnerability
   * @trace REQ-SEC2-INT-003
   */
  async integrate(
    vulnerability: Vulnerability,
    options?: IntegrationOptions
  ): Promise<NeuroSymbolicResult> {
    const opts = { ...this.options, ...options };
    
    // Run neural analysis (if LLM analyzer is available)
    let neuralResult: NeuralResult;
    if (this.llmAnalyzer) {
      neuralResult = await this.analyzeNeural(vulnerability, vulnerability.codeSnippet);
    } else {
      // Fallback: use heuristic-based pseudo-neural analysis
      neuralResult = this.generateHeuristicNeuralResult(vulnerability);
    }
    
    // Run symbolic validation
    const symbolicResult = await this.validateSymbolic(vulnerability);
    
    // Apply integration rules (REQ-SEC2-INT-002)
    const finalDecision = this.applyIntegrationRules(
      neuralResult,
      symbolicResult,
      opts.neuralThreshold
    );
    
    // Calculate combined confidence
    const combinedConfidence = this.calculateScore(neuralResult, symbolicResult);
    
    // Generate rationale
    const rationale = this.generateRationale(
      neuralResult,
      symbolicResult,
      finalDecision
    );
    
    return {
      neuralConfidence: neuralResult.confidence,
      symbolicValid: symbolicResult.valid,
      finalDecision,
      neuralExplanation: neuralResult.explanation,
      symbolicEvidence: symbolicResult.evidence,
      combinedConfidence,
      rationale,
    };
  }

  /**
   * Validate a finding using symbolic reasoning only
   */
  async validateSymbolic(vulnerability: Vulnerability): Promise<SymbolicResult> {
    const evidence: Evidence[] = [];
    const matchedPatterns: string[] = [];
    const appliedRules: string[] = [];
    let knowledgeGraphMatches: KnowledgeGraphMatch[] = [];
    
    // 1. Pattern matching
    for (const [patternName, patternInfo] of SECURITY_PATTERNS) {
      const hasMatchingCWE = vulnerability.cwes.some(cwe => 
        patternInfo.cwes.includes(cwe)
      );
      
      if (hasMatchingCWE) {
        matchedPatterns.push(patternName);
        evidence.push({
          type: 'pattern-match',
          source: patternName,
          description: `Matched security pattern: ${patternName} (${patternInfo.cwes.join(', ')})`,
          weight: 0.8,
          relatedCWEs: patternInfo.cwes,
        });
      }
    }
    
    // 2. Rule inference
    for (const rule of SECURITY_RULES) {
      const hasMatchingCWE = vulnerability.cwes.some(cwe => 
        rule.cwes.includes(cwe)
      );
      
      if (hasMatchingCWE) {
        appliedRules.push(rule.id);
        evidence.push({
          type: 'rule-inference',
          source: rule.id,
          description: `Applied rule: ${rule.name}`,
          weight: 0.7,
          relatedCWEs: rule.cwes,
        });
      }
    }
    
    // 3. Knowledge graph query (if available)
    if (this.knowledgeQuery) {
      try {
        const codePattern = vulnerability.codeSnippet ?? '';
        knowledgeGraphMatches = await this.knowledgeQuery.queryPattern(
          codePattern,
          vulnerability.cwes
        );
        
        for (const match of knowledgeGraphMatches) {
          evidence.push({
            type: 'knowledge-graph',
            source: match.entityUri,
            description: `Knowledge graph match: ${match.entityType} (score: ${match.score})`,
            weight: match.score,
          });
        }
      } catch {
        // Knowledge graph query failed, continue without it
      }
    }
    
    // 4. Static analysis evidence (from vulnerability detection)
    evidence.push({
      type: 'static-analysis',
      source: vulnerability.ruleId,
      description: `Detected by static analysis rule: ${vulnerability.ruleId}`,
      weight: vulnerability.confidence,
    });
    
    // Determine validity based on evidence weight
    const totalWeight = evidence.reduce((sum, e) => sum + e.weight, 0);
    const avgWeight = evidence.length > 0 ? totalWeight / evidence.length : 0;
    const valid = avgWeight >= 0.5 && matchedPatterns.length > 0;
    
    return {
      valid,
      evidence,
      matchedPatterns,
      appliedRules,
      knowledgeGraphMatches: knowledgeGraphMatches.length > 0 
        ? knowledgeGraphMatches 
        : undefined,
    };
  }

  /**
   * Analyze a finding using neural (LLM) analysis
   */
  async analyzeNeural(
    vulnerability: Vulnerability,
    context?: string
  ): Promise<NeuralResult> {
    if (!this.llmAnalyzer) {
      return this.generateHeuristicNeuralResult(vulnerability);
    }
    
    return this.llmAnalyzer.analyzeContext(
      context ?? vulnerability.codeSnippet ?? '',
      vulnerability
    );
  }

  /**
   * Generate heuristic-based pseudo-neural result when LLM is not available
   */
  private generateHeuristicNeuralResult(vulnerability: Vulnerability): NeuralResult {
    // Estimate confidence based on vulnerability characteristics
    let confidence = vulnerability.confidence;
    
    // Adjust based on severity
    const severityBoost: Record<Severity, number> = {
      critical: 0.1,
      high: 0.05,
      medium: 0,
      low: -0.05,
      info: -0.1,
    };
    confidence = Math.max(0, Math.min(1, confidence + severityBoost[vulnerability.severity]));
    
    // Generate explanation based on vulnerability info
    const explanation = this.generateExplanation(vulnerability);
    
    return {
      confidence,
      explanation,
      suggestedSeverity: vulnerability.severity,
      suggestedFixes: [vulnerability.recommendation],
      model: 'heuristic-fallback',
      latency: 0,
    };
  }

  /**
   * Generate human-readable explanation
   */
  private generateExplanation(vulnerability: Vulnerability): string {
    const cwes = vulnerability.cwes.join(', ');
    const location = `${vulnerability.location.file}:${vulnerability.location.startLine}`;
    
    return `Security vulnerability detected at ${location}. ` +
           `This finding is classified as ${vulnerability.severity} severity ` +
           `and relates to ${cwes}. ${vulnerability.description} ` +
           `Recommended action: ${vulnerability.recommendation}`;
  }

  /**
   * Calculate combined confidence score
   * @trace REQ-SEC2-INT-002
   */
  calculateScore(
    neuralResult: NeuralResult,
    symbolicResult: SymbolicResult
  ): number {
    // If symbolic validation fails, significantly reduce confidence
    if (!symbolicResult.valid) {
      return neuralResult.confidence * 0.3;
    }
    
    // Weight symbolic evidence
    const symbolicWeight = symbolicResult.evidence.reduce(
      (sum, e) => sum + e.weight, 0
    ) / Math.max(1, symbolicResult.evidence.length);
    
    // Combined score: weighted average favoring symbolic when neural is uncertain
    const neuralWeight = neuralResult.confidence >= this.options.neuralThreshold 
      ? 0.6 
      : 0.4;
    const symbolicWeightFactor = 1 - neuralWeight;
    
    const combined = 
      neuralResult.confidence * neuralWeight + 
      symbolicWeight * symbolicWeightFactor;
    
    return Math.round(combined * 100) / 100;
  }

  /**
   * Apply integration rules to determine final decision
   * @trace REQ-SEC2-INT-002
   * 
   * Rules:
   * - If symbolic validation fails -> reject neural result
   * - If symbolic valid AND neural confidence >= threshold -> confirm
   * - If symbolic valid AND neural confidence < threshold -> prefer symbolic
   */
  private applyIntegrationRules(
    neuralResult: NeuralResult,
    symbolicResult: SymbolicResult,
    neuralThreshold: number
  ): FinalDecision {
    // Rule 1: Symbolic invalid -> reject
    if (!symbolicResult.valid) {
      return 'rejected';
    }
    
    // Rule 2: Symbolic valid AND high neural confidence -> confirm
    if (neuralResult.confidence >= neuralThreshold) {
      return 'confirmed';
    }
    
    // Rule 3: Symbolic valid but low neural confidence -> needs review
    // However, if symbolic evidence is strong, can still confirm
    const strongSymbolicEvidence = symbolicResult.evidence.filter(
      e => e.weight >= 0.7
    );
    
    if (strongSymbolicEvidence.length >= 2) {
      return 'confirmed';
    }
    
    return 'needs-review';
  }

  /**
   * Generate rationale for the decision
   */
  private generateRationale(
    neuralResult: NeuralResult,
    symbolicResult: SymbolicResult,
    decision: FinalDecision
  ): string {
    const parts: string[] = [];
    
    // Neural confidence
    parts.push(`Neural analysis confidence: ${(neuralResult.confidence * 100).toFixed(1)}%`);
    
    // Symbolic validation
    parts.push(`Symbolic validation: ${symbolicResult.valid ? 'VALID' : 'INVALID'}`);
    
    // Evidence summary
    if (symbolicResult.matchedPatterns.length > 0) {
      parts.push(`Matched patterns: ${symbolicResult.matchedPatterns.join(', ')}`);
    }
    
    if (symbolicResult.appliedRules.length > 0) {
      parts.push(`Applied rules: ${symbolicResult.appliedRules.join(', ')}`);
    }
    
    // Decision rationale
    switch (decision) {
      case 'confirmed':
        parts.push('Decision: CONFIRMED - Both neural and symbolic analysis indicate a real vulnerability.');
        break;
      case 'rejected':
        parts.push('Decision: REJECTED - Symbolic validation failed, likely false positive.');
        break;
      case 'needs-review':
        parts.push('Decision: NEEDS REVIEW - Neural confidence is low, manual review recommended.');
        break;
    }
    
    return parts.join('\n');
  }
}

/**
 * Create a default Neuro-Symbolic Core instance
 */
export function createNeuroSymbolicCore(
  options?: IntegrationOptions
): NeuroSymbolicCore {
  return new NeuroSymbolicCore(options);
}

/**
 * Stub LLM Analyzer for testing without actual LLM
 */
export class StubLLMAnalyzer implements ILLMAnalyzer {
  async analyzeContext(
    codeSnippet: string,
    vulnerability: Vulnerability
  ): Promise<NeuralResult> {
    // Simple heuristic-based analysis
    const hasUserInput = /req\.(body|query|params)|process\.env|fs\.read/i.test(codeSnippet);
    const hasDangerousSink = /exec|query|eval|innerHTML|write/i.test(codeSnippet);
    
    let confidence = vulnerability.confidence;
    if (hasUserInput && hasDangerousSink) {
      confidence = Math.min(1, confidence + 0.2);
    }
    
    return {
      confidence,
      explanation: `Code analysis: ${hasUserInput ? 'User input detected' : 'No obvious user input'}. ${hasDangerousSink ? 'Dangerous sink detected' : 'No dangerous sinks'}.`,
      suggestedSeverity: vulnerability.severity,
      suggestedFixes: [vulnerability.recommendation],
      model: 'stub-analyzer',
      latency: 10,
    };
  }
  
  async generateExplanation(
    vulnerability: Vulnerability,
    dataFlow?: TaintPath
  ): Promise<string> {
    let explanation = `This ${vulnerability.severity} severity vulnerability at ${vulnerability.location.file}:${vulnerability.location.startLine} `;
    explanation += `involves ${vulnerability.cwes.join(' and ')}. `;
    
    if (dataFlow) {
      explanation += `Data flows from ${dataFlow.source.variableName} through ${dataFlow.steps.length} steps to a dangerous sink.`;
    }
    
    return explanation;
  }
  
  async suggestFix(vulnerability: Vulnerability): Promise<string[]> {
    return [vulnerability.recommendation];
  }
}

/**
 * Stub Knowledge Query for testing without actual knowledge graph
 */
export class StubKnowledgeQuery implements IKnowledgeQuery {
  async queryPattern(
    _codePattern: string,
    cwes?: string[]
  ): Promise<KnowledgeGraphMatch[]> {
    const matches: KnowledgeGraphMatch[] = [];
    
    // Simple pattern matching
    if (cwes) {
      for (const cwe of cwes) {
        matches.push({
          entityUri: `https://cwe.mitre.org/data/definitions/${cwe.replace('CWE-', '')}.html`,
          entityType: 'CWE',
          score: 0.8,
          relatedEntities: [],
        });
      }
    }
    
    return matches;
  }
  
  async matchRule(vulnerability: Vulnerability): Promise<string[]> {
    const matchedRules: string[] = [];
    
    for (const rule of SECURITY_RULES) {
      if (vulnerability.cwes.some(cwe => rule.cwes.includes(cwe))) {
        matchedRules.push(rule.id);
      }
    }
    
    return matchedRules;
  }
  
  async inferVulnerability(codeSnippet: string): Promise<string[]> {
    const inferred: string[] = [];
    
    // Simple inference based on code patterns
    if (/query.*\$\{/.test(codeSnippet) || /query.*\+/.test(codeSnippet)) {
      inferred.push('CWE-89');
    }
    if (/exec.*\$\{/.test(codeSnippet) || /spawn.*\+/.test(codeSnippet)) {
      inferred.push('CWE-78');
    }
    if (/innerHTML\s*=/.test(codeSnippet) || /document\.write/.test(codeSnippet)) {
      inferred.push('CWE-79');
    }
    
    return inferred;
  }
}
