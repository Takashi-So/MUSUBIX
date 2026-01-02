/**
 * Quality Metrics Calculator
 * 
 * Calculates code quality metrics
 * 
 * @packageDocumentation
 * @module codegen/quality-metrics
 * 
 * @see REQ-QUA-001 - Quality Metrics
 * @see Article VI - Quality Standards
 */

/**
 * Quality metric type
 */
export type MetricType =
  | 'loc'              // Lines of code
  | 'sloc'             // Source lines of code
  | 'comments'         // Comment lines
  | 'blank'            // Blank lines
  | 'complexity'       // Cyclomatic complexity
  | 'maintainability'  // Maintainability index
  | 'duplication'      // Code duplication
  | 'coupling'         // Coupling between modules
  | 'cohesion'         // Cohesion within modules
  | 'test-coverage';   // Test coverage

/**
 * Metric value
 */
export interface MetricValue {
  /** Metric type */
  type: MetricType;
  /** Numeric value */
  value: number;
  /** Unit */
  unit?: string;
  /** Thresholds */
  thresholds?: MetricThresholds;
  /** Status */
  status: 'good' | 'warning' | 'critical';
}

/**
 * Metric thresholds
 */
export interface MetricThresholds {
  /** Good threshold */
  good: number;
  /** Warning threshold */
  warning: number;
  /** Critical threshold */
  critical: number;
}

/**
 * File metrics
 */
export interface FileMetrics {
  /** File path */
  file: string;
  /** Language */
  language: string;
  /** Metrics */
  metrics: MetricValue[];
  /** Functions/methods */
  functions: FunctionMetrics[];
  /** Classes */
  classes: ClassMetrics[];
}

/**
 * Function metrics
 */
export interface FunctionMetrics {
  /** Function name */
  name: string;
  /** Line number */
  line: number;
  /** Lines of code */
  loc: number;
  /** Cyclomatic complexity */
  complexity: number;
  /** Parameters count */
  parameters: number;
  /** Nesting depth */
  nestingDepth: number;
  /** Cognitive complexity */
  cognitiveComplexity: number;
}

/**
 * Class metrics
 */
export interface ClassMetrics {
  /** Class name */
  name: string;
  /** Line number */
  line: number;
  /** Methods count */
  methodCount: number;
  /** Properties count */
  propertyCount: number;
  /** Lines of code */
  loc: number;
  /** Weighted methods per class */
  wmc: number;
  /** Lack of cohesion */
  lcom: number;
  /** Depth of inheritance */
  dit: number;
  /** Number of children */
  noc: number;
  /** Coupling between objects */
  cbo: number;
}

/**
 * Project metrics summary
 */
export interface ProjectMetrics {
  /** Total files */
  totalFiles: number;
  /** Total lines */
  totalLines: number;
  /** Average complexity */
  averageComplexity: number;
  /** Average maintainability */
  averageMaintainability: number;
  /** Duplication percentage */
  duplicationPercentage: number;
  /** Overall quality score */
  qualityScore: number;
  /** File metrics */
  files: FileMetrics[];
  /** Trends */
  trends?: MetricTrends;
}

/**
 * Metric trends
 */
export interface MetricTrends {
  /** Period */
  period: string;
  /** Changes */
  changes: Array<{
    metric: MetricType;
    previous: number;
    current: number;
    change: number;
    direction: 'improved' | 'degraded' | 'stable';
  }>;
}

/**
 * Quality metrics calculator configuration
 */
export interface QualityMetricsConfig {
  /** Include test files */
  includeTests: boolean;
  /** Calculate duplication */
  calculateDuplication: boolean;
  /** Duplication threshold (min lines) */
  duplicationThreshold: number;
  /** Complexity thresholds */
  complexityThresholds: MetricThresholds;
  /** Maintainability thresholds */
  maintainabilityThresholds: MetricThresholds;
}

/**
 * Default configuration
 */
export const DEFAULT_METRICS_CONFIG: QualityMetricsConfig = {
  includeTests: false,
  calculateDuplication: true,
  duplicationThreshold: 6,
  complexityThresholds: {
    good: 10,
    warning: 20,
    critical: 30,
  },
  maintainabilityThresholds: {
    good: 80,
    warning: 60,
    critical: 40,
  },
};

/**
 * Quality Metrics Calculator
 */
export class QualityMetricsCalculator {
  private config: QualityMetricsConfig;

  constructor(config?: Partial<QualityMetricsConfig>) {
    this.config = { ...DEFAULT_METRICS_CONFIG, ...config };
  }

  /**
   * Calculate metrics for code
   */
  calculate(code: string, file: string, language = 'typescript'): FileMetrics {
    const lines = code.split('\n');
    
    // Basic line metrics
    const loc = lines.length;
    const sloc = this.countSourceLines(lines);
    const comments = this.countCommentLines(lines, language);
    const blank = this.countBlankLines(lines);
    
    // Complexity metrics
    const complexity = this.calculateCyclomaticComplexity(code);
    const maintainability = this.calculateMaintainabilityIndex(
      loc,
      complexity,
      this.calculateHalsteadVolume(code)
    );

    // Function metrics
    const functions = this.extractFunctionMetrics(code, language);
    
    // Class metrics
    const classes = this.extractClassMetrics(code, language);

    return {
      file,
      language,
      metrics: [
        this.createMetric('loc', loc),
        this.createMetric('sloc', sloc),
        this.createMetric('comments', comments),
        this.createMetric('blank', blank),
        this.createMetric('complexity', complexity, this.config.complexityThresholds),
        this.createMetric('maintainability', maintainability, this.config.maintainabilityThresholds),
      ],
      functions,
      classes,
    };
  }

  /**
   * Calculate metrics for multiple files
   */
  calculateProject(
    files: Array<{ path: string; content: string; language?: string }>
  ): ProjectMetrics {
    const fileMetrics = files.map((f) => 
      this.calculate(f.content, f.path, f.language)
    );

    const totalFiles = fileMetrics.length;
    const totalLines = fileMetrics.reduce(
      (sum, f) => sum + (f.metrics.find((m) => m.type === 'loc')?.value ?? 0),
      0
    );

    const complexities = fileMetrics.map(
      (f) => f.metrics.find((m) => m.type === 'complexity')?.value ?? 0
    );
    const averageComplexity = complexities.length > 0
      ? complexities.reduce((a, b) => a + b, 0) / complexities.length
      : 0;

    const maintainabilities = fileMetrics.map(
      (f) => f.metrics.find((m) => m.type === 'maintainability')?.value ?? 0
    );
    const averageMaintainability = maintainabilities.length > 0
      ? maintainabilities.reduce((a, b) => a + b, 0) / maintainabilities.length
      : 0;

    // Calculate duplication
    let duplicationPercentage = 0;
    if (this.config.calculateDuplication) {
      const allCode = files.map((f) => f.content).join('\n');
      duplicationPercentage = this.calculateDuplication(allCode);
    }

    // Overall quality score (0-100)
    const qualityScore = this.calculateQualityScore(
      averageComplexity,
      averageMaintainability,
      duplicationPercentage
    );

    return {
      totalFiles,
      totalLines,
      averageComplexity,
      averageMaintainability,
      duplicationPercentage,
      qualityScore,
      files: fileMetrics,
    };
  }

  /**
   * Count source lines (non-blank, non-comment)
   */
  private countSourceLines(lines: string[]): number {
    return lines.filter((line) => {
      const trimmed = line.trim();
      return trimmed.length > 0 && 
             !trimmed.startsWith('//') && 
             !trimmed.startsWith('/*') &&
             !trimmed.startsWith('*') &&
             !trimmed.startsWith('#');
    }).length;
  }

  /**
   * Count comment lines
   */
  private countCommentLines(lines: string[], _language: string): number {
    let count = 0;
    let inBlockComment = false;

    for (const line of lines) {
      const trimmed = line.trim();
      
      if (inBlockComment) {
        count++;
        if (trimmed.includes('*/')) {
          inBlockComment = false;
        }
      } else if (trimmed.startsWith('/*')) {
        count++;
        if (!trimmed.includes('*/')) {
          inBlockComment = true;
        }
      } else if (trimmed.startsWith('//') || trimmed.startsWith('#')) {
        count++;
      }
    }

    return count;
  }

  /**
   * Count blank lines
   */
  private countBlankLines(lines: string[]): number {
    return lines.filter((line) => line.trim().length === 0).length;
  }

  /**
   * Calculate cyclomatic complexity
   */
  private calculateCyclomaticComplexity(code: string): number {
    let complexity = 1;

    const patterns = [
      /\bif\b/g,
      /\belse\s+if\b/g,
      /\bfor\b/g,
      /\bwhile\b/g,
      /\bdo\b/g,
      /\bcase\b/g,
      /\bcatch\b/g,
      /\?\?/g,
      /\?\./g,
      /&&/g,
      /\|\|/g,
      /\?[^:]/g,
    ];

    for (const pattern of patterns) {
      const matches = code.match(pattern);
      if (matches) {
        complexity += matches.length;
      }
    }

    return complexity;
  }

  /**
   * Calculate Halstead volume
   */
  private calculateHalsteadVolume(code: string): number {
    // Simplified Halstead volume calculation
    const operators = new Set<string>();
    const operands = new Set<string>();

    // Extract operators
    const opMatches = code.match(/[+\-*/%=<>!&|^~?:]+|\b(function|return|if|else|for|while|class|const|let|var|new|this|typeof|instanceof)\b/g);
    if (opMatches) {
      opMatches.forEach((op) => operators.add(op));
    }

    // Extract operands (identifiers and literals)
    const idMatches = code.match(/\b[a-zA-Z_]\w*\b/g);
    if (idMatches) {
      idMatches.forEach((id) => operands.add(id));
    }

    const n1 = operators.size;
    const n2 = operands.size;
    const N1 = opMatches?.length ?? 0;
    const N2 = idMatches?.length ?? 0;

    const N = N1 + N2;
    const n = n1 + n2;

    if (n === 0) return 0;

    return N * Math.log2(n);
  }

  /**
   * Calculate maintainability index
   */
  private calculateMaintainabilityIndex(
    loc: number,
    complexity: number,
    halsteadVolume: number
  ): number {
    // Original MI formula: 171 - 5.2 * ln(V) - 0.23 * CC - 16.2 * ln(LOC)
    // Scaled to 0-100
    if (loc === 0 || halsteadVolume === 0) return 100;

    const mi = 171 
      - 5.2 * Math.log(halsteadVolume + 1)
      - 0.23 * complexity 
      - 16.2 * Math.log(loc);

    // Scale to 0-100
    return Math.max(0, Math.min(100, mi * 100 / 171));
  }

  /**
   * Calculate code duplication percentage
   */
  private calculateDuplication(code: string): number {
    const lines = code.split('\n').filter((l) => l.trim().length > 0);
    if (lines.length === 0) return 0;

    const threshold = this.config.duplicationThreshold;
    const duplicatedLines = new Set<number>();

    // Simple duplication detection using n-gram comparison
    for (let i = 0; i <= lines.length - threshold; i++) {
      const chunk = lines.slice(i, i + threshold).join('\n');
      
      for (let j = i + threshold; j <= lines.length - threshold; j++) {
        const compareChunk = lines.slice(j, j + threshold).join('\n');
        
        if (chunk === compareChunk) {
          for (let k = 0; k < threshold; k++) {
            duplicatedLines.add(i + k);
            duplicatedLines.add(j + k);
          }
        }
      }
    }

    return (duplicatedLines.size / lines.length) * 100;
  }

  /**
   * Extract function metrics
   */
  private extractFunctionMetrics(code: string, _language: string): FunctionMetrics[] {
    const functions: FunctionMetrics[] = [];
    const regex = /(?:function\s+(\w+)|(?:(\w+)\s*[=:]\s*(?:async\s+)?(?:function|\([^)]*\)\s*=>)))/g;
    let match;

    while ((match = regex.exec(code)) !== null) {
      const name = match[1] || match[2];
      const line = code.substring(0, match.index).split('\n').length;
      
      // Find function body
      const startIndex = match.index;
      let braceCount = 0;
      let endIndex = startIndex;
      let started = false;

      for (let i = startIndex; i < code.length; i++) {
        if (code[i] === '{') {
          braceCount++;
          started = true;
        } else if (code[i] === '}') {
          braceCount--;
          if (started && braceCount === 0) {
            endIndex = i;
            break;
          }
        }
      }

      const funcBody = code.substring(startIndex, endIndex + 1);
      const loc = funcBody.split('\n').length;
      const complexity = this.calculateCyclomaticComplexity(funcBody);
      const parameters = this.countParameters(funcBody);
      const nestingDepth = this.calculateNestingDepth(funcBody);
      const cognitiveComplexity = this.calculateCognitiveComplexity(funcBody);

      functions.push({
        name,
        line,
        loc,
        complexity,
        parameters,
        nestingDepth,
        cognitiveComplexity,
      });
    }

    return functions;
  }

  /**
   * Count function parameters
   */
  private countParameters(funcBody: string): number {
    const match = funcBody.match(/\(([^)]*)\)/);
    if (!match || !match[1].trim()) return 0;
    
    return match[1].split(',').filter((p) => p.trim()).length;
  }

  /**
   * Calculate nesting depth
   */
  private calculateNestingDepth(code: string): number {
    let maxDepth = 0;
    let currentDepth = 0;

    for (const char of code) {
      if (char === '{') {
        currentDepth++;
        maxDepth = Math.max(maxDepth, currentDepth);
      } else if (char === '}') {
        currentDepth--;
      }
    }

    return maxDepth;
  }

  /**
   * Calculate cognitive complexity
   */
  private calculateCognitiveComplexity(code: string): number {
    let complexity = 0;
    let nesting = 0;

    const lines = code.split('\n');
    
    for (const line of lines) {
      const trimmed = line.trim();
      
      // Control flow structures add to complexity based on nesting
      if (/\b(if|else\s+if|for|while|do|switch|catch)\b/.test(trimmed)) {
        complexity += 1 + nesting;
      }
      
      // Logical operators add 1
      const logicalOps = trimmed.match(/&&|\|\|/g);
      if (logicalOps) {
        complexity += logicalOps.length;
      }

      // Track nesting
      if (trimmed.includes('{')) nesting++;
      if (trimmed.includes('}')) nesting = Math.max(0, nesting - 1);
    }

    return complexity;
  }

  /**
   * Extract class metrics
   */
  private extractClassMetrics(code: string, _language: string): ClassMetrics[] {
    const classes: ClassMetrics[] = [];
    const regex = /class\s+(\w+)/g;
    let match;

    while ((match = regex.exec(code)) !== null) {
      const name = match[1];
      const line = code.substring(0, match.index).split('\n').length;
      
      // Find class body
      const startIndex = code.indexOf('{', match.index);
      let braceCount = 1;
      let endIndex = startIndex + 1;

      while (braceCount > 0 && endIndex < code.length) {
        if (code[endIndex] === '{') braceCount++;
        else if (code[endIndex] === '}') braceCount--;
        endIndex++;
      }

      const classBody = code.substring(startIndex, endIndex);
      const loc = classBody.split('\n').length;
      
      // Count methods
      const methodMatches = classBody.match(/(?:async\s+)?(?:static\s+)?(?:get\s+|set\s+)?(\w+)\s*\([^)]*\)\s*[:{]/g);
      const methodCount = methodMatches?.length ?? 0;
      
      // Count properties
      const propMatches = classBody.match(/(?:private|public|protected|readonly)?\s*(\w+)\s*[?:]?\s*:\s*\w+/g);
      const propertyCount = propMatches?.length ?? 0;

      // WMC - sum of complexities of all methods
      const wmc = this.calculateCyclomaticComplexity(classBody);

      classes.push({
        name,
        line,
        methodCount,
        propertyCount,
        loc,
        wmc,
        lcom: 0, // Simplified - would need full analysis
        dit: 0,  // Would need inheritance tree
        noc: 0,  // Would need full codebase
        cbo: 0,  // Would need dependency analysis
      });
    }

    return classes;
  }

  /**
   * Create metric value with status
   */
  private createMetric(
    type: MetricType,
    value: number,
    thresholds?: MetricThresholds
  ): MetricValue {
    let status: 'good' | 'warning' | 'critical' = 'good';

    if (thresholds) {
      // For metrics where lower is better (complexity)
      if (type === 'complexity' || type === 'duplication' || type === 'coupling') {
        if (value >= thresholds.critical) status = 'critical';
        else if (value >= thresholds.warning) status = 'warning';
      } 
      // For metrics where higher is better (maintainability, cohesion)
      else {
        if (value <= thresholds.critical) status = 'critical';
        else if (value <= thresholds.warning) status = 'warning';
      }
    }

    return {
      type,
      value: Math.round(value * 100) / 100,
      thresholds,
      status,
    };
  }

  /**
   * Calculate overall quality score
   */
  private calculateQualityScore(
    avgComplexity: number,
    avgMaintainability: number,
    duplication: number
  ): number {
    // Weight factors
    const complexityWeight = 0.3;
    const maintainabilityWeight = 0.5;
    const duplicationWeight = 0.2;

    // Normalize complexity (lower is better, target: 10)
    const complexityScore = Math.max(0, 100 - (avgComplexity - 10) * 5);

    // Maintainability is already 0-100
    const maintainabilityScore = avgMaintainability;

    // Normalize duplication (lower is better)
    const duplicationScore = Math.max(0, 100 - duplication * 2);

    const score = 
      complexityScore * complexityWeight +
      maintainabilityScore * maintainabilityWeight +
      duplicationScore * duplicationWeight;

    return Math.round(Math.max(0, Math.min(100, score)));
  }
}

/**
 * Create quality metrics calculator instance
 */
export function createQualityMetricsCalculator(
  config?: Partial<QualityMetricsConfig>
): QualityMetricsCalculator {
  return new QualityMetricsCalculator(config);
}
