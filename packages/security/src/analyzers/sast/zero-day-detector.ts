/**
 * @fileoverview Zero-Day Vulnerability Detector using Knowledge Graph Pattern Deviation
 * @module @nahisaho/musubix-security/analyzers/sast/zero-day-detector
 * @trace DES-SEC2-SAST-003, REQ-SEC2-SAST-003
 */

import type { Vulnerability, Severity, SourceLocation } from '../../types/vulnerability.js';

/**
 * Zero-day detection result
 */
export interface ZeroDayResult {
  vulnerability: ZeroDayVulnerability;
  deviation: PatternDeviation;
  riskAssessment: RiskAssessment;
  confidence: number;
}

/**
 * Zero-day vulnerability
 */
export interface ZeroDayVulnerability {
  id: string;
  type: 'unknown-pattern' | 'anomalous-flow' | 'unusual-api-usage' | 'suspicious-construct';
  severity: Severity;
  location: SourceLocation;
  description: string;
  recommendation: string;
  codeSnippet: string;
}

/**
 * Pattern deviation analysis
 */
export interface PatternDeviation {
  patternId: string;
  expectedPattern: string;
  observedPattern: string;
  deviationScore: number;
  deviationType: 'structural' | 'behavioral' | 'temporal' | 'contextual';
  context: PatternContext;
}

/**
 * Pattern context
 */
export interface PatternContext {
  surroundingCode: string;
  callStack: string[];
  dataFlowPath: string[];
  relatedPatterns: string[];
}

/**
 * Risk assessment
 */
export interface RiskAssessment {
  overallRisk: Severity;
  exploitability: number; // 0-1
  impact: number; // 0-1
  attackVector: string;
  mitigationComplexity: 'low' | 'medium' | 'high';
  businessImpact: string;
}

/**
 * Detection options
 */
export interface ZeroDayOptions {
  /** Minimum deviation score to report */
  minDeviationScore?: number;
  /** Enable knowledge graph analysis */
  enableKGAnalysis?: boolean;
  /** Enable heuristic analysis */
  enableHeuristics?: boolean;
  /** Enable LLM-assisted analysis */
  enableLLMAnalysis?: boolean;
  /** Custom baseline patterns */
  customBaseline?: CodePattern[];
}

/**
 * Code pattern definition
 */
export interface CodePattern {
  id: string;
  name: string;
  type: 'safe' | 'dangerous' | 'neutral';
  signature: PatternSignature;
  frequency: number;
  confidence: number;
}

/**
 * Pattern signature
 */
export interface PatternSignature {
  astPattern?: string;
  callSequence?: string[];
  dataFlowPattern?: string;
  contextMarkers?: string[];
}

/**
 * Knowledge graph node
 */
interface KGNode {
  id: string;
  type: 'function' | 'variable' | 'class' | 'api' | 'pattern';
  name: string;
  properties: Record<string, unknown>;
  edges: KGEdge[];
}

/**
 * Knowledge graph edge
 */
interface KGEdge {
  target: string;
  relation: 'calls' | 'uses' | 'inherits' | 'contains' | 'flows-to';
  weight: number;
}

/**
 * Built-in suspicious patterns to detect
 */
const SUSPICIOUS_PATTERNS: Array<{
  id: string;
  name: string;
  regex: RegExp;
  severity: Severity;
  description: string;
}> = [
  {
    id: 'ZD-001',
    name: 'Unusual Prototype Access',
    regex: /\[['"`]__proto__['"`]\]|\[['"`]constructor['"`]\]\.prototype/,
    severity: 'high',
    description: 'Unusual prototype chain manipulation detected',
  },
  {
    id: 'ZD-002',
    name: 'Dynamic Function Construction',
    regex: /new\s+Function\s*\([^)]*\+|Function\s*\(\s*[^)]*\+/,
    severity: 'critical',
    description: 'Dynamic function construction with concatenation',
  },
  {
    id: 'ZD-003',
    name: 'Unusual Serialization',
    regex: /serialize.*deserialize|pickle\.loads|yaml\.load\s*\(/,
    severity: 'high',
    description: 'Potentially unsafe serialization/deserialization',
  },
  {
    id: 'ZD-004',
    name: 'Reflection Abuse',
    regex: /getattr\s*\([^)]*,\s*[^'"]|__getattribute__|__class__\.__bases__/,
    severity: 'medium',
    description: 'Dynamic attribute access with variable input',
  },
  {
    id: 'ZD-005',
    name: 'Memory Manipulation',
    regex: /ctypes\.memmove|struct\.pack.*\*|buffer\.write\s*\([^)]*\+/,
    severity: 'critical',
    description: 'Direct memory manipulation detected',
  },
  {
    id: 'ZD-006',
    name: 'Unusual Process Creation',
    regex: /subprocess\.Popen\s*\([^)]*shell\s*=\s*True|os\.system\s*\([^)]*\+/,
    severity: 'high',
    description: 'Dynamic command execution detected',
  },
  {
    id: 'ZD-007',
    name: 'Type Confusion Pattern',
    regex: /type\s*\([^)]+\)\s*!=|isinstance.*not|__class__\s*=\s*/,
    severity: 'medium',
    description: 'Potential type confusion vulnerability',
  },
  {
    id: 'ZD-008',
    name: 'Race Condition Pattern',
    regex: /if\s+os\.path\.exists.*open\(|check.*then.*use|toctou/i,
    severity: 'medium',
    description: 'Time-of-check to time-of-use (TOCTOU) pattern',
  },
  {
    id: 'ZD-009',
    name: 'Integer Overflow Pattern',
    regex: /<<\s*\d{2,}|\*\s*\d{10,}|parseInt.*\*.*parseInt/,
    severity: 'medium',
    description: 'Potential integer overflow vulnerability',
  },
  {
    id: 'ZD-010',
    name: 'Cryptographic Weakness',
    regex: /MD5|SHA1\s*\(|DES|RC4|ECB|random\.random\s*\(\)|Math\.random\s*\(\).*key/i,
    severity: 'high',
    description: 'Weak cryptographic primitive detected',
  },
];

/**
 * Zero-Day Detector implementation
 * @trace DES-SEC2-SAST-003
 */
export class ZeroDayDetector {
  private options: ZeroDayOptions;
  private knowledgeGraph: Map<string, KGNode>;
  // Reserved for future use with custom baseline patterns
  // private baselinePatterns: CodePattern[];

  constructor(options: ZeroDayOptions = {}) {
    this.options = {
      minDeviationScore: options.minDeviationScore ?? 0.6,
      enableKGAnalysis: options.enableKGAnalysis ?? true,
      enableHeuristics: options.enableHeuristics ?? true,
      enableLLMAnalysis: options.enableLLMAnalysis ?? false,
    };
    
    this.knowledgeGraph = new Map();
    // Reserved for custom baseline patterns
    // this.baselinePatterns = options.customBaseline ?? [];
  }

  /**
   * Detect potential zero-day vulnerabilities
   * @trace REQ-SEC2-SAST-003
   */
  async detect(code: string, filePath: string): Promise<ZeroDayResult[]> {
    const results: ZeroDayResult[] = [];
    const lines = code.split('\n');
    
    // Build local knowledge graph
    this.buildLocalKnowledgeGraph(code, filePath);
    
    // Pattern-based detection
    if (this.options.enableHeuristics) {
      const heuristicResults = this.detectSuspiciousPatterns(code, lines, filePath);
      results.push(...heuristicResults);
    }
    
    // Knowledge graph deviation analysis
    if (this.options.enableKGAnalysis) {
      const deviationResults = this.analyzePatternDeviation(code, lines, filePath);
      results.push(...deviationResults);
    }
    
    // LLM-assisted analysis (if enabled)
    if (this.options.enableLLMAnalysis) {
      const llmResults = await this.analyzeWithLLM(code, filePath);
      results.push(...llmResults);
    }
    
    // Filter by minimum deviation score
    return results.filter(
      r => r.deviation.deviationScore >= (this.options.minDeviationScore ?? 0.6)
    );
  }

  /**
   * Build local knowledge graph from code
   */
  private buildLocalKnowledgeGraph(code: string, filePath: string): void {
    // Extract functions
    const functionPattern = /(?:function\s+(\w+)|const\s+(\w+)\s*=\s*(?:async\s*)?\(|(\w+)\s*\([^)]*\)\s*{)/g;
    let match: RegExpExecArray | null;
    
    while ((match = functionPattern.exec(code)) !== null) {
      const name = match[1] ?? match[2] ?? match[3];
      const lineNum = code.substring(0, match.index).split('\n').length;
      
      const node: KGNode = {
        id: `${filePath}:${name}`,
        type: 'function',
        name,
        properties: { line: lineNum, file: filePath },
        edges: [],
      };
      
      // Find function calls within this function
      const functionBody = this.extractFunctionBody(code, match.index);
      const callPattern = /(\w+)\s*\(/g;
      let callMatch: RegExpExecArray | null;
      
      while ((callMatch = callPattern.exec(functionBody)) !== null) {
        if (!['if', 'while', 'for', 'switch', 'function', 'catch'].includes(callMatch[1])) {
          node.edges.push({
            target: callMatch[1],
            relation: 'calls',
            weight: 1,
          });
        }
      }
      
      this.knowledgeGraph.set(node.id, node);
    }
    
    // Extract classes
    const classPattern = /class\s+(\w+)(?:\s+extends\s+(\w+))?/g;
    
    while ((match = classPattern.exec(code)) !== null) {
      const className = match[1];
      const parentClass = match[2];
      
      const node: KGNode = {
        id: `${filePath}:${className}`,
        type: 'class',
        name: className,
        properties: { file: filePath },
        edges: [],
      };
      
      if (parentClass) {
        node.edges.push({
          target: parentClass,
          relation: 'inherits',
          weight: 1,
        });
      }
      
      this.knowledgeGraph.set(node.id, node);
    }
  }

  /**
   * Extract function body from code
   */
  private extractFunctionBody(code: string, startIndex: number): string {
    let depth = 0;
    let inString = false;
    let stringChar = '';
    let bodyStart = -1;
    
    for (let i = startIndex; i < code.length; i++) {
      const char = code[i];
      const prevChar = code[i - 1];
      
      if (!inString) {
        if (char === '"' || char === "'" || char === '`') {
          inString = true;
          stringChar = char;
        } else if (char === '{') {
          if (depth === 0) bodyStart = i;
          depth++;
        } else if (char === '}') {
          depth--;
          if (depth === 0) {
            return code.substring(bodyStart, i + 1);
          }
        }
      } else {
        if (char === stringChar && prevChar !== '\\') {
          inString = false;
        }
      }
    }
    
    return code.substring(startIndex, Math.min(startIndex + 500, code.length));
  }

  /**
   * Detect suspicious patterns using heuristics
   */
  private detectSuspiciousPatterns(
    code: string,
    lines: string[],
    filePath: string
  ): ZeroDayResult[] {
    const results: ZeroDayResult[] = [];
    
    for (const pattern of SUSPICIOUS_PATTERNS) {
      const globalPattern = new RegExp(pattern.regex.source, 'gm');
      let match: RegExpExecArray | null;
      
      while ((match = globalPattern.exec(code)) !== null) {
        const lineNum = code.substring(0, match.index).split('\n').length;
        const lineContent = lines[lineNum - 1] ?? '';
        
        // Calculate deviation score based on context
        const deviationScore = this.calculateDeviationScore(code, match.index, pattern);
        
        const result: ZeroDayResult = {
          vulnerability: {
            id: `${pattern.id}-${lineNum}`,
            type: 'suspicious-construct',
            severity: pattern.severity,
            location: {
              file: filePath,
              startLine: lineNum,
              endLine: lineNum,
              startColumn: 0,
              endColumn: lineContent.length,
            },
            description: pattern.description,
            recommendation: this.generateRecommendation(pattern),
            codeSnippet: this.extractCodeSnippet(lines, lineNum),
          },
          deviation: {
            patternId: pattern.id,
            expectedPattern: 'standard/safe implementation',
            observedPattern: match[0],
            deviationScore,
            deviationType: 'structural',
            context: {
              surroundingCode: this.extractCodeSnippet(lines, lineNum),
              callStack: this.extractCallStack(code, match.index),
              dataFlowPath: this.extractDataFlowPath(code, match.index),
              relatedPatterns: [],
            },
          },
          riskAssessment: this.assessRisk(pattern, deviationScore),
          confidence: deviationScore,
        };
        
        results.push(result);
      }
    }
    
    return results;
  }

  /**
   * Analyze pattern deviation using knowledge graph
   */
  private analyzePatternDeviation(
    code: string,
    lines: string[],
    filePath: string
  ): ZeroDayResult[] {
    const results: ZeroDayResult[] = [];
    
    // Analyze API usage patterns
    const apiUsageDeviations = this.detectAPIUsageDeviations(code, lines, filePath);
    results.push(...apiUsageDeviations);
    
    // Analyze data flow anomalies
    const dataFlowDeviations = this.detectDataFlowAnomalies(code, lines, filePath);
    results.push(...dataFlowDeviations);
    
    return results;
  }

  /**
   * Detect unusual API usage patterns
   */
  private detectAPIUsageDeviations(
    code: string,
    lines: string[],
    filePath: string
  ): ZeroDayResult[] {
    const results: ZeroDayResult[] = [];
    
    // Check for unusual API combinations
    const dangerousAPICombinations = [
      { apis: ['eval', 'JSON.parse'], description: 'eval with JSON parsing' },
      { apis: ['innerHTML', 'fetch'], description: 'fetch result to innerHTML' },
      { apis: ['exec', 'req.body'], description: 'user input to command execution' },
      { apis: ['query', 'req.params'], description: 'user params to database query' },
    ];
    
    for (const combo of dangerousAPICombinations) {
      const hasAllAPIs = combo.apis.every(api => code.includes(api));
      
      if (hasAllAPIs) {
        // Find the location of the first API
        const firstApiIndex = code.indexOf(combo.apis[0]);
        const lineNum = code.substring(0, firstApiIndex).split('\n').length;
        
        results.push({
          vulnerability: {
            id: `ZD-API-${lineNum}`,
            type: 'unusual-api-usage',
            severity: 'high',
            location: {
              file: filePath,
              startLine: lineNum,
              endLine: lineNum,
              startColumn: 0,
              endColumn: lines[lineNum - 1]?.length ?? 0,
            },
            description: `Dangerous API combination detected: ${combo.description}`,
            recommendation: 'Review the data flow between these APIs and add appropriate validation',
            codeSnippet: this.extractCodeSnippet(lines, lineNum),
          },
          deviation: {
            patternId: 'ZD-API-COMBO',
            expectedPattern: 'Validated data flow between APIs',
            observedPattern: combo.apis.join(' -> '),
            deviationScore: 0.8,
            deviationType: 'behavioral',
            context: {
              surroundingCode: this.extractCodeSnippet(lines, lineNum),
              callStack: [],
              dataFlowPath: combo.apis,
              relatedPatterns: [],
            },
          },
          riskAssessment: {
            overallRisk: 'high',
            exploitability: 0.7,
            impact: 0.8,
            attackVector: 'Network',
            mitigationComplexity: 'medium',
            businessImpact: 'Data compromise or code execution',
          },
          confidence: 0.75,
        });
      }
    }
    
    return results;
  }

  /**
   * Detect data flow anomalies
   */
  private detectDataFlowAnomalies(
    code: string,
    lines: string[],
    filePath: string
  ): ZeroDayResult[] {
    const results: ZeroDayResult[] = [];
    
    // Detect unusual data flow patterns
    const anomalousPatterns = [
      {
        pattern: /(\w+)\s*=\s*req\.(body|query|params)\s*[^;]*;\s*[^]*?\1\s*\+/,
        type: 'anomalous-flow' as const,
        description: 'User input used in string concatenation',
      },
      {
        pattern: /return\s+\{[^}]*password[^}]*\}/i,
        type: 'anomalous-flow' as const,
        description: 'Potential credential leakage in return value',
      },
      {
        pattern: /catch\s*\([^)]*\)\s*{\s*}/,
        type: 'suspicious-construct' as const,
        description: 'Empty catch block suppressing errors',
      },
    ];
    
    for (const anomaly of anomalousPatterns) {
      const match = code.match(anomaly.pattern);
      if (match) {
        const lineNum = code.substring(0, match.index ?? 0).split('\n').length;
        
        results.push({
          vulnerability: {
            id: `ZD-FLOW-${lineNum}`,
            type: anomaly.type,
            severity: 'medium',
            location: {
              file: filePath,
              startLine: lineNum,
              endLine: lineNum,
              startColumn: 0,
              endColumn: lines[lineNum - 1]?.length ?? 0,
            },
            description: anomaly.description,
            recommendation: 'Review data flow and add appropriate validation',
            codeSnippet: this.extractCodeSnippet(lines, lineNum),
          },
          deviation: {
            patternId: 'ZD-FLOW',
            expectedPattern: 'Validated data transformation',
            observedPattern: match[0].substring(0, 100),
            deviationScore: 0.65,
            deviationType: 'behavioral',
            context: {
              surroundingCode: this.extractCodeSnippet(lines, lineNum),
              callStack: [],
              dataFlowPath: [],
              relatedPatterns: [],
            },
          },
          riskAssessment: {
            overallRisk: 'medium',
            exploitability: 0.5,
            impact: 0.6,
            attackVector: 'Network',
            mitigationComplexity: 'low',
            businessImpact: 'Potential data exposure',
          },
          confidence: 0.6,
        });
      }
    }
    
    return results;
  }

  /**
   * LLM-assisted analysis (placeholder for future implementation)
   */
  async analyzeWithLLM(_code: string, _filePath: string): Promise<ZeroDayResult[]> {
    // This would integrate with LLM APIs for advanced analysis
    // Currently returns empty array as placeholder
    return [];
  }

  /**
   * Assess risk for a detected pattern
   */
  assessRisk(
    pattern: { severity: Severity; description: string },
    deviationScore: number
  ): RiskAssessment {
    const severityToExploitability: Record<Severity, number> = {
      critical: 0.9,
      high: 0.7,
      medium: 0.5,
      low: 0.3,
      info: 0.1,
    };
    
    const severityToImpact: Record<Severity, number> = {
      critical: 0.95,
      high: 0.8,
      medium: 0.6,
      low: 0.4,
      info: 0.2,
    };
    
    return {
      overallRisk: pattern.severity,
      exploitability: severityToExploitability[pattern.severity] * deviationScore,
      impact: severityToImpact[pattern.severity],
      attackVector: this.determineAttackVector(pattern.description),
      mitigationComplexity: this.determineMitigationComplexity(pattern.severity),
      businessImpact: this.determineBusinessImpact(pattern.severity),
    };
  }

  /**
   * Calculate deviation score based on context
   */
  private calculateDeviationScore(
    code: string,
    matchIndex: number,
    pattern: { severity: Severity }
  ): number {
    let score = 0.5;
    
    // Increase score based on severity
    const severityBonus: Record<Severity, number> = {
      critical: 0.3,
      high: 0.2,
      medium: 0.1,
      low: 0.05,
      info: 0,
    };
    score += severityBonus[pattern.severity];
    
    // Check if in sensitive context
    const beforeContext = code.substring(Math.max(0, matchIndex - 200), matchIndex).toLowerCase();
    if (beforeContext.includes('user') || beforeContext.includes('input') || beforeContext.includes('req.')) {
      score += 0.15;
    }
    
    // Check if near network operations
    if (beforeContext.includes('fetch') || beforeContext.includes('http') || beforeContext.includes('request')) {
      score += 0.1;
    }
    
    return Math.min(score, 1);
  }

  /**
   * Generate recommendation for pattern
   */
  private generateRecommendation(pattern: { id: string; description: string }): string {
    const recommendations: Record<string, string> = {
      'ZD-001': 'Avoid direct prototype manipulation. Use Object.create() or class inheritance.',
      'ZD-002': 'Use static function definitions instead of dynamic construction.',
      'ZD-003': 'Use safe serialization methods with type validation.',
      'ZD-004': 'Use explicit attribute access with whitelist validation.',
      'ZD-005': 'Avoid direct memory manipulation. Use safe buffer APIs.',
      'ZD-006': 'Use parameterized commands and avoid shell=True.',
      'ZD-007': 'Use strict type checking with TypeScript or runtime validation.',
      'ZD-008': 'Use atomic file operations or implement proper locking.',
      'ZD-009': 'Use BigInt for large numbers and validate numeric inputs.',
      'ZD-010': 'Use strong cryptographic primitives (SHA-256+, AES-256-GCM).',
    };
    
    return recommendations[pattern.id] ?? 'Review and refactor this code pattern.';
  }

  /**
   * Extract code snippet around line
   */
  private extractCodeSnippet(lines: string[], lineNum: number): string {
    const start = Math.max(0, lineNum - 3);
    const end = Math.min(lines.length, lineNum + 3);
    return lines.slice(start, end).join('\n');
  }

  /**
   * Extract call stack from context
   */
  private extractCallStack(code: string, index: number): string[] {
    const stack: string[] = [];
    const beforeCode = code.substring(0, index);
    
    // Find enclosing function
    const functionMatch = beforeCode.match(/function\s+(\w+)|const\s+(\w+)\s*=\s*(?:async\s*)?\(/g);
    if (functionMatch) {
      const lastMatch = functionMatch[functionMatch.length - 1];
      const nameMatch = lastMatch.match(/function\s+(\w+)|const\s+(\w+)/);
      if (nameMatch) {
        stack.push(nameMatch[1] ?? nameMatch[2]);
      }
    }
    
    return stack;
  }

  /**
   * Extract data flow path
   */
  private extractDataFlowPath(code: string, index: number): string[] {
    const path: string[] = [];
    const context = code.substring(Math.max(0, index - 300), Math.min(code.length, index + 100));
    
    // Look for variable assignments leading to this point
    const assignments = context.match(/(\w+)\s*=\s*[^;]+/g) ?? [];
    for (const assignment of assignments) {
      const varName = assignment.split('=')[0].trim();
      if (varName && varName.length < 30) {
        path.push(varName);
      }
    }
    
    return path.slice(-5); // Last 5 assignments
  }

  /**
   * Determine attack vector
   */
  private determineAttackVector(description: string): string {
    const desc = description.toLowerCase();
    if (desc.includes('network') || desc.includes('request')) return 'Network';
    if (desc.includes('file') || desc.includes('path')) return 'Local';
    if (desc.includes('user') || desc.includes('input')) return 'Adjacent';
    return 'Network';
  }

  /**
   * Determine mitigation complexity
   */
  private determineMitigationComplexity(severity: Severity): 'low' | 'medium' | 'high' {
    if (severity === 'critical') return 'high';
    if (severity === 'high') return 'medium';
    return 'low';
  }

  /**
   * Determine business impact
   */
  private determineBusinessImpact(severity: Severity): string {
    const impacts: Record<Severity, string> = {
      critical: 'Complete system compromise, data breach, or service disruption',
      high: 'Significant data exposure or system access',
      medium: 'Limited data exposure or service degradation',
      low: 'Minor security weakness',
      info: 'Informational finding',
    };
    return impacts[severity];
  }

  /**
   * Convert results to standard vulnerability format
   */
  toVulnerabilities(results: ZeroDayResult[]): Vulnerability[] {
    return results.map(result => ({
      id: result.vulnerability.id,
      type: 'zero-day' as const,
      severity: result.vulnerability.severity,
      cwes: ['CWE-Unknown'],
      owasp: ['A00:Unknown'],
      location: result.vulnerability.location,
      description: result.vulnerability.description,
      recommendation: result.vulnerability.recommendation,
      confidence: result.confidence,
      ruleId: result.deviation.patternId,
      codeSnippet: result.vulnerability.codeSnippet,
      detectedAt: new Date(),
    }));
  }
}

/**
 * Create zero-day detector instance
 */
export function createZeroDayDetector(options?: ZeroDayOptions): ZeroDayDetector {
  return new ZeroDayDetector(options);
}
