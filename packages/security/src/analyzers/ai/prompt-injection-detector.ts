/**
 * @fileoverview Prompt Injection Detector for LLM APIs
 * @module @nahisaho/musubix-security/analyzers/ai/prompt-injection-detector
 * @trace DES-SEC2-AI-001, REQ-SEC2-AI-001
 */

import type { Vulnerability, Severity, SourceLocation } from '../../types/vulnerability.js';

/**
 * Prompt injection detection result
 */
export interface PromptInjectionResult {
  vulnerability: PromptInjectionVulnerability;
  confidence: number;
  patterns: DetectedPattern[];
  llmCallSite: LLMCallSite;
}

/**
 * Prompt injection vulnerability
 */
export interface PromptInjectionVulnerability {
  id: string;
  type: 'direct' | 'indirect' | 'jailbreak' | 'data-exfiltration' | 'prompt-leaking';
  severity: Severity;
  location: SourceLocation;
  description: string;
  recommendation: string;
  codeSnippet: string;
}

/**
 * Detected injection pattern
 */
export interface DetectedPattern {
  patternId: string;
  patternName: string;
  matchedText: string;
  position: { start: number; end: number };
  category: 'injection' | 'jailbreak' | 'obfuscation' | 'encoding';
}

/**
 * LLM API call site information
 */
export interface LLMCallSite {
  apiType: LLMApiType;
  location: SourceLocation;
  hasInputValidation: boolean;
  hasOutputSanitization: boolean;
  promptSource: 'static' | 'user-input' | 'mixed' | 'unknown';
  modelName?: string;
}

/**
 * Supported LLM API types
 */
export type LLMApiType = 
  | 'openai' 
  | 'anthropic' 
  | 'azure-openai' 
  | 'google-ai' 
  | 'huggingface' 
  | 'langchain' 
  | 'llamaindex'
  | 'custom';

/**
 * Detection options
 */
export interface PromptInjectionOptions {
  /** Enable heuristic detection */
  enableHeuristics?: boolean;
  /** Enable pattern matching */
  enablePatterns?: boolean;
  /** Minimum confidence threshold */
  minConfidence?: number;
  /** Custom patterns */
  customPatterns?: InjectionPattern[];
  /** Skip specific patterns */
  skipPatterns?: string[];
}

/**
 * Injection pattern definition
 */
export interface InjectionPattern {
  id: string;
  name: string;
  regex: RegExp;
  severity: Severity;
  category: 'injection' | 'jailbreak' | 'obfuscation' | 'encoding';
  description: string;
}

/**
 * Built-in injection patterns
 */
const INJECTION_PATTERNS: InjectionPattern[] = [
  // Direct injection patterns
  {
    id: 'PINJ-001',
    name: 'Ignore Instructions',
    regex: /ignore\s+(all\s+)?(previous|above|prior)\s+(instructions?|prompts?|rules?)/i,
    severity: 'high',
    category: 'injection',
    description: 'Attempts to make the LLM ignore previous instructions',
  },
  {
    id: 'PINJ-002',
    name: 'New Instructions Override',
    regex: /(new|updated|real)\s+instructions?:/i,
    severity: 'high',
    category: 'injection',
    description: 'Attempts to inject new instructions',
  },
  {
    id: 'PINJ-003',
    name: 'System Prompt Override',
    regex: /system\s*[:=]\s*["']|<\|system\|>|<<SYS>>|<system>/i,
    severity: 'critical',
    category: 'injection',
    description: 'Attempts to override system prompt',
  },
  {
    id: 'PINJ-004',
    name: 'Role Manipulation',
    regex: /you\s+are\s+(now\s+)?(a|an|the)\s+\w+|act\s+as\s+(a|an|the)|pretend\s+(to\s+be|you're)/i,
    severity: 'medium',
    category: 'injection',
    description: 'Attempts to manipulate the LLM role',
  },
  
  // Jailbreak patterns
  {
    id: 'PINJ-005',
    name: 'DAN Jailbreak',
    regex: /\bDAN\b|do\s+anything\s+now|jailbreak|bypass\s+(restrictions?|filters?|safety)/i,
    severity: 'critical',
    category: 'jailbreak',
    description: 'Known jailbreak technique (DAN)',
  },
  {
    id: 'PINJ-006',
    name: 'Developer Mode',
    regex: /developer\s+mode|god\s+mode|admin\s+mode|maintenance\s+mode|debug\s+mode/i,
    severity: 'high',
    category: 'jailbreak',
    description: 'Attempts to enable special modes',
  },
  {
    id: 'PINJ-007',
    name: 'Fictional Context',
    regex: /let's\s+play\s+a\s+game|imagine\s+you|in\s+this\s+(story|scenario|fiction)/i,
    severity: 'medium',
    category: 'jailbreak',
    description: 'Uses fictional context to bypass restrictions',
  },
  
  // Obfuscation patterns
  {
    id: 'PINJ-008',
    name: 'Base64 Encoded Payload',
    regex: /(?:[A-Za-z0-9+/]{4}){10,}(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?/,
    severity: 'medium',
    category: 'obfuscation',
    description: 'Potentially base64 encoded malicious payload',
  },
  {
    id: 'PINJ-009',
    name: 'Unicode Obfuscation',
    regex: /[\u200B-\u200F\u2028-\u202F\uFEFF]|&#x?[0-9a-fA-F]+;/,
    severity: 'medium',
    category: 'obfuscation',
    description: 'Unicode characters used for obfuscation',
  },
  {
    id: 'PINJ-010',
    name: 'Leetspeak Obfuscation',
    regex: /1gn0r3|pr0mpt|1nstruct10n|syst3m|byp4ss|h4ck/i,
    severity: 'low',
    category: 'obfuscation',
    description: 'Leetspeak obfuscation attempt',
  },
  
  // Data exfiltration
  {
    id: 'PINJ-011',
    name: 'Data Exfiltration Prompt',
    regex: /repeat\s+(back|all|the|previous)|echo\s+(back|all|everything)|show\s+(me\s+)?(the\s+)?(system\s+)?prompt/i,
    severity: 'high',
    category: 'injection',
    description: 'Attempts to extract system prompt or data',
  },
  {
    id: 'PINJ-012',
    name: 'Instruction Leaking',
    regex: /what\s+(are|were)\s+your\s+(instructions?|rules?|constraints?)|reveal\s+(your\s+)?(instructions?|prompt)/i,
    severity: 'high',
    category: 'injection',
    description: 'Attempts to leak instructions',
  },
];

/**
 * LLM API detection patterns
 */
const LLM_API_PATTERNS = {
  openai: [
    /openai\.chat\.completions\.create/,
    /openai\.Completion\.create/,
    /new\s+OpenAI\(/,
    /ChatOpenAI\(/,
    /import\s+.*\s+from\s+['"]openai['"]/,
  ],
  anthropic: [
    /anthropic\.messages\.create/,
    /Anthropic\(/,
    /ChatAnthropic\(/,
    /import\s+.*\s+from\s+['"]@anthropic-ai\/sdk['"]/,
  ],
  'azure-openai': [
    /AzureOpenAI\(/,
    /azure\.openai/i,
    /azure-openai/i,
  ],
  'google-ai': [
    /google\.generativeai/,
    /GenerativeModel\(/,
    /ChatGoogleGenerativeAI\(/,
  ],
  huggingface: [
    /HuggingFaceHub\(/,
    /pipeline\s*\(\s*['"]text-generation['"]/,
    /transformers/,
  ],
  langchain: [
    /from\s+langchain/,
    /ChatPromptTemplate/,
    /LLMChain\(/,
    /ConversationChain\(/,
  ],
  llamaindex: [
    /from\s+llama_index/,
    /LlamaIndex\(/,
    /VectorStoreIndex/,
  ],
};

/**
 * Prompt Injection Detector
 * @trace DES-SEC2-AI-001
 */
export class PromptInjectionDetector {
  private options: PromptInjectionOptions;
  private patterns: InjectionPattern[];

  constructor(options: PromptInjectionOptions = {}) {
    this.options = {
      enableHeuristics: options.enableHeuristics ?? true,
      enablePatterns: options.enablePatterns ?? true,
      minConfidence: options.minConfidence ?? 0.5,
      skipPatterns: options.skipPatterns ?? [],
    };
    
    this.patterns = [
      ...INJECTION_PATTERNS.filter(p => !this.options.skipPatterns?.includes(p.id)),
      ...(options.customPatterns ?? []),
    ];
  }

  /**
   * Detect prompt injection vulnerabilities in code
   * @trace REQ-SEC2-AI-001
   */
  async detect(code: string, filePath: string): Promise<PromptInjectionResult[]> {
    const results: PromptInjectionResult[] = [];
    const lines = code.split('\n');
    
    // Find LLM API call sites
    const callSites = this.identifyLLMCalls(code, filePath);
    
    for (const callSite of callSites) {
      // Extract prompt content around the call site
      const promptContext = this.extractPromptContext(code, lines, callSite);
      
      // Check for injection patterns
      const detectedPatterns: DetectedPattern[] = [];
      
      if (this.options.enablePatterns) {
        for (const pattern of this.patterns) {
          const matches = promptContext.matchAll(new RegExp(pattern.regex, 'gi'));
          for (const match of matches) {
            detectedPatterns.push({
              patternId: pattern.id,
              patternName: pattern.name,
              matchedText: match[0],
              position: {
                start: match.index ?? 0,
                end: (match.index ?? 0) + match[0].length,
              },
              category: pattern.category,
            });
          }
        }
      }
      
      // Check for lack of input validation
      if (!callSite.hasInputValidation) {
        const confidence = this.calculateConfidence(callSite, detectedPatterns);
        
        if (confidence >= (this.options.minConfidence ?? 0.5)) {
          const vulnerability: PromptInjectionVulnerability = {
            id: `PINJ-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
            type: this.determineVulnerabilityType(detectedPatterns),
            severity: this.determineSeverity(callSite, detectedPatterns),
            location: callSite.location,
            description: this.generateDescription(callSite, detectedPatterns),
            recommendation: this.generateRecommendation(callSite, detectedPatterns),
            codeSnippet: this.extractCodeSnippet(lines, callSite.location),
          };
          
          results.push({
            vulnerability,
            confidence,
            patterns: detectedPatterns,
            llmCallSite: callSite,
          });
        }
      }
    }
    
    return results;
  }

  /**
   * Identify LLM API calls in code
   */
  identifyLLMCalls(code: string, filePath: string): LLMCallSite[] {
    const callSites: LLMCallSite[] = [];
    const lines = code.split('\n');
    
    for (const [apiType, patterns] of Object.entries(LLM_API_PATTERNS) as [LLMApiType, RegExp[]][]) {
      for (const pattern of patterns) {
        let match: RegExpExecArray | null;
        const globalPattern = new RegExp(pattern.source, 'gm');
        
        while ((match = globalPattern.exec(code)) !== null) {
          const lineNumber = code.substring(0, match.index).split('\n').length;
          const lineContent = lines[lineNumber - 1] ?? '';
          
          callSites.push({
            apiType,
            location: {
              file: filePath,
              startLine: lineNumber,
              endLine: lineNumber,
              startColumn: 0,
              endColumn: lineContent.length,
            },
            hasInputValidation: this.checkInputValidation(code, match.index, lines),
            hasOutputSanitization: this.checkOutputSanitization(code, match.index, lines),
            promptSource: this.determinePromptSource(code, match.index, lines),
            modelName: this.extractModelName(code, match.index),
          });
        }
      }
    }
    
    return callSites;
  }

  /**
   * Check if input validation exists before LLM call
   */
  checkInputValidation(code: string, callIndex: number, _lines: string[]): boolean {
    // Look for validation patterns before the call
    const beforeCall = code.substring(Math.max(0, callIndex - 500), callIndex);
    
    const validationPatterns = [
      /sanitize|validate|escape|filter|clean/i,
      /input\s*\.\s*(trim|strip|replace)/i,
      /zod\s*\.\s*(string|object)/i,
      /joi\s*\.\s*(string|object)/i,
      /yup\s*\.\s*(string|object)/i,
      /DOMPurify|xss|bleach/i,
      /if\s*\([^)]*\.length|if\s*\([^)]*\.match/i,
    ];
    
    return validationPatterns.some(p => p.test(beforeCall));
  }

  /**
   * Check if output sanitization exists after LLM call
   */
  checkOutputSanitization(code: string, callIndex: number, _lines: string[]): boolean {
    const afterCall = code.substring(callIndex, Math.min(code.length, callIndex + 500));
    
    const sanitizationPatterns = [
      /sanitize|escape|filter|clean|encode/i,
      /JSON\.parse|JSON\.stringify/i,
      /\.trim\(\)|\.replace\(/i,
      /validate.*response|check.*output/i,
    ];
    
    return sanitizationPatterns.some(p => p.test(afterCall));
  }

  /**
   * Determine prompt source type
   */
  determinePromptSource(
    code: string,
    callIndex: number,
    _lines: string[]
  ): 'static' | 'user-input' | 'mixed' | 'unknown' {
    const contextRange = code.substring(Math.max(0, callIndex - 300), callIndex + 200);
    
    const userInputPatterns = [
      /req\.body|req\.query|req\.params/,
      /request\.json|request\.form/,
      /user_input|userInput|user_message/,
      /\$\{.*input.*\}|f['"].*\{.*input.*\}/,
      /\.get\(['"].*input.*['"]\)/,
    ];
    
    const staticPatterns = [
      /const\s+prompt\s*=\s*['"`]/,
      /prompt\s*=\s*['"`][^${}]+['"`]/,
    ];
    
    const hasUserInput = userInputPatterns.some(p => p.test(contextRange));
    const hasStatic = staticPatterns.some(p => p.test(contextRange));
    
    if (hasUserInput && hasStatic) return 'mixed';
    if (hasUserInput) return 'user-input';
    if (hasStatic) return 'static';
    return 'unknown';
  }

  /**
   * Extract model name from code
   */
  extractModelName(code: string, callIndex: number): string | undefined {
    const contextRange = code.substring(Math.max(0, callIndex - 100), callIndex + 200);
    
    const modelPatterns = [
      /model\s*[=:]\s*['"]([^'"]+)['"]/,
      /model_name\s*[=:]\s*['"]([^'"]+)['"]/,
      /gpt-[34][-\w]*/,
      /claude-[23][-\w]*/,
      /gemini[-\w]*/,
    ];
    
    for (const pattern of modelPatterns) {
      const match = contextRange.match(pattern);
      if (match) {
        return match[1] ?? match[0];
      }
    }
    
    return undefined;
  }

  /**
   * Extract prompt context around LLM call
   */
  private extractPromptContext(_code: string, lines: string[], callSite: LLMCallSite): string {
    const startIdx = Math.max(0, callSite.location.startLine - 20);
    const endIdx = Math.min(lines.length, callSite.location.endLine + 10);
    return lines.slice(startIdx, endIdx).join('\n');
  }

  /**
   * Calculate detection confidence
   */
  private calculateConfidence(callSite: LLMCallSite, patterns: DetectedPattern[]): number {
    let confidence = 0.3; // Base confidence for unvalidated LLM call
    
    // Increase for user input source
    if (callSite.promptSource === 'user-input') {
      confidence += 0.4;
    } else if (callSite.promptSource === 'mixed') {
      confidence += 0.2;
    }
    
    // Increase for detected patterns
    confidence += Math.min(patterns.length * 0.1, 0.3);
    
    // Decrease if output is sanitized
    if (callSite.hasOutputSanitization) {
      confidence -= 0.1;
    }
    
    return Math.min(Math.max(confidence, 0), 1);
  }

  /**
   * Determine vulnerability type
   */
  private determineVulnerabilityType(
    patterns: DetectedPattern[]
  ): PromptInjectionVulnerability['type'] {
    const categories = patterns.map(p => p.category);
    
    if (categories.includes('jailbreak')) return 'jailbreak';
    if (patterns.some(p => p.patternId.includes('011') || p.patternId.includes('012'))) {
      return 'prompt-leaking';
    }
    return 'direct';
  }

  /**
   * Determine severity based on context
   */
  private determineSeverity(callSite: LLMCallSite, patterns: DetectedPattern[]): Severity {
    // Critical if direct user input without validation
    if (callSite.promptSource === 'user-input' && !callSite.hasInputValidation) {
      return 'critical';
    }
    
    // High if patterns detected
    const patternSeverities = patterns.map(p => {
      const patternDef = this.patterns.find(pd => pd.id === p.patternId);
      return patternDef?.severity ?? 'medium';
    });
    
    if (patternSeverities.includes('critical')) return 'critical';
    if (patternSeverities.includes('high')) return 'high';
    
    // Medium for mixed sources
    if (callSite.promptSource === 'mixed') return 'medium';
    
    return 'low';
  }

  /**
   * Generate vulnerability description
   */
  private generateDescription(callSite: LLMCallSite, patterns: DetectedPattern[]): string {
    const parts: string[] = [];
    
    parts.push(`LLM API call (${callSite.apiType}) detected`);
    
    if (callSite.promptSource === 'user-input') {
      parts.push('with user-controlled input');
    }
    
    if (!callSite.hasInputValidation) {
      parts.push('without input validation');
    }
    
    if (patterns.length > 0) {
      parts.push(`- ${patterns.length} potential injection pattern(s) found`);
    }
    
    return parts.join(' ');
  }

  /**
   * Generate recommendation
   */
  private generateRecommendation(callSite: LLMCallSite, _patterns: DetectedPattern[]): string {
    const recommendations: string[] = [];
    
    if (!callSite.hasInputValidation) {
      recommendations.push('Implement input validation and sanitization before passing to LLM');
    }
    
    if (callSite.promptSource === 'user-input') {
      recommendations.push('Use parameterized prompts with strict input boundaries');
      recommendations.push('Implement rate limiting and monitoring for suspicious patterns');
    }
    
    if (!callSite.hasOutputSanitization) {
      recommendations.push('Validate and sanitize LLM output before using in application');
    }
    
    recommendations.push('Consider using guardrails or content filtering');
    
    return recommendations.join('. ');
  }

  /**
   * Extract code snippet around location
   */
  private extractCodeSnippet(lines: string[], location: SourceLocation): string {
    const startLine = Math.max(0, location.startLine - 3);
    const endLine = Math.min(lines.length, location.endLine + 3);
    return lines.slice(startLine, endLine).join('\n');
  }

  /**
   * Convert results to standard vulnerability format
   */
  toVulnerabilities(results: PromptInjectionResult[]): Vulnerability[] {
    return results.map(result => ({
      id: result.vulnerability.id,
      type: 'prompt-injection' as const,
      severity: result.vulnerability.severity,
      cwes: ['CWE-74', 'CWE-79'], // Injection, XSS
      owasp: ['A03:2021'], // Injection
      location: result.vulnerability.location,
      description: result.vulnerability.description,
      recommendation: result.vulnerability.recommendation,
      confidence: result.confidence,
      ruleId: result.patterns[0]?.patternId ?? 'PINJ-HEURISTIC',
      codeSnippet: result.vulnerability.codeSnippet,
      detectedAt: new Date(),
    }));
  }
}

/**
 * Create prompt injection detector instance
 */
export function createPromptInjectionDetector(
  options?: PromptInjectionOptions
): PromptInjectionDetector {
  return new PromptInjectionDetector(options);
}
