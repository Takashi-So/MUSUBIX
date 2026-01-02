/**
 * SOLID Validator
 * 
 * Validates code against SOLID principles
 * 
 * @packageDocumentation
 * @module design/solid-validator
 * 
 * @see REQ-DES-003 - SOLID Principles Validation
 * @see Article III - Design Validation
 */

import type { CodeStructure, ClassInfo, RelationshipInfo } from './pattern-detector.js';

/**
 * SOLID principle
 */
export type SOLIDPrinciple =
  | 'S' // Single Responsibility
  | 'O' // Open/Closed
  | 'L' // Liskov Substitution
  | 'I' // Interface Segregation
  | 'D'; // Dependency Inversion

/**
 * SOLID principle info
 */
export interface SOLIDPrincipleInfo {
  /** Principle code */
  code: SOLIDPrinciple;
  /** Full name */
  name: string;
  /** Description */
  description: string;
  /** Violation indicators */
  violationIndicators: string[];
}

/**
 * SOLID principles information
 */
export const SOLID_PRINCIPLES: Record<SOLIDPrinciple, SOLIDPrincipleInfo> = {
  S: {
    code: 'S',
    name: 'Single Responsibility Principle',
    description: 'A class should have only one reason to change',
    violationIndicators: [
      'Too many methods',
      'Methods with unrelated purposes',
      'Multiple domains handled',
    ],
  },
  O: {
    code: 'O',
    name: 'Open/Closed Principle',
    description: 'Open for extension, closed for modification',
    violationIndicators: [
      'Switch statements on type',
      'If-else chains for types',
      'Concrete class dependencies',
    ],
  },
  L: {
    code: 'L',
    name: 'Liskov Substitution Principle',
    description: 'Subtypes must be substitutable for base types',
    violationIndicators: [
      'Override that changes behavior',
      'Throwing unexpected exceptions',
      'Empty implementations',
    ],
  },
  I: {
    code: 'I',
    name: 'Interface Segregation Principle',
    description: 'Clients should not depend on unused methods',
    violationIndicators: [
      'Large interfaces',
      'Partial implementations',
      'Unused method implementations',
    ],
  },
  D: {
    code: 'D',
    name: 'Dependency Inversion Principle',
    description: 'Depend on abstractions, not concretions',
    violationIndicators: [
      'Direct concrete instantiation',
      'Importing concrete classes',
      'No interface/abstract usage',
    ],
  },
};

/**
 * SOLID violation
 */
export interface SOLIDViolation {
  /** Principle violated */
  principle: SOLIDPrinciple;
  /** Severity */
  severity: 'high' | 'medium' | 'low';
  /** Class/element involved */
  element: string;
  /** Description */
  description: string;
  /** Suggestion */
  suggestion: string;
  /** Code location */
  location?: {
    file?: string;
    line?: number;
  };
}

/**
 * SOLID validation result
 */
export interface SOLIDValidationResult {
  /** Overall score (0-100) */
  score: number;
  /** Score by principle */
  principleScores: Record<SOLIDPrinciple, number>;
  /** Violations found */
  violations: SOLIDViolation[];
  /** Recommendations */
  recommendations: string[];
  /** Summary */
  summary: SOLIDSummary;
}

/**
 * SOLID summary
 */
export interface SOLIDSummary {
  /** Total classes analyzed */
  classesAnalyzed: number;
  /** Classes with violations */
  classesWithViolations: number;
  /** Total violations */
  totalViolations: number;
  /** Violations by principle */
  violationsByPrinciple: Record<SOLIDPrinciple, number>;
  /** Compliance level */
  complianceLevel: 'excellent' | 'good' | 'moderate' | 'poor';
}

/**
 * SOLID validator configuration
 */
export interface SOLIDValidatorConfig {
  /** Methods threshold for SRP */
  srpMethodThreshold: number;
  /** Interface methods threshold for ISP */
  ispMethodThreshold: number;
  /** Enable strict mode */
  strictMode: boolean;
  /** Principles to validate */
  enabledPrinciples: SOLIDPrinciple[];
}

/**
 * Default configuration
 */
export const DEFAULT_SOLID_CONFIG: SOLIDValidatorConfig = {
  srpMethodThreshold: 10,
  ispMethodThreshold: 5,
  strictMode: false,
  enabledPrinciples: ['S', 'O', 'L', 'I', 'D'],
};

/**
 * SOLID Validator
 */
export class SOLIDValidator {
  private config: SOLIDValidatorConfig;

  constructor(config?: Partial<SOLIDValidatorConfig>) {
    this.config = { ...DEFAULT_SOLID_CONFIG, ...config };
  }

  /**
   * Validate code structure against SOLID
   */
  validate(structure: CodeStructure): SOLIDValidationResult {
    const violations: SOLIDViolation[] = [];
    const principleScores: Record<SOLIDPrinciple, number> = {
      S: 100, O: 100, L: 100, I: 100, D: 100,
    };

    // Validate each enabled principle
    if (this.config.enabledPrinciples.includes('S')) {
      const srpViolations = this.validateSRP(structure);
      violations.push(...srpViolations);
      principleScores.S = this.calculateScore(srpViolations, structure.classes.length);
    }

    if (this.config.enabledPrinciples.includes('O')) {
      const ocpViolations = this.validateOCP(structure);
      violations.push(...ocpViolations);
      principleScores.O = this.calculateScore(ocpViolations, structure.classes.length);
    }

    if (this.config.enabledPrinciples.includes('L')) {
      const lspViolations = this.validateLSP(structure);
      violations.push(...lspViolations);
      principleScores.L = this.calculateScore(lspViolations, structure.classes.length);
    }

    if (this.config.enabledPrinciples.includes('I')) {
      const ispViolations = this.validateISP(structure);
      violations.push(...ispViolations);
      principleScores.I = this.calculateScore(ispViolations, structure.classes.length);
    }

    if (this.config.enabledPrinciples.includes('D')) {
      const dipViolations = this.validateDIP(structure);
      violations.push(...dipViolations);
      principleScores.D = this.calculateScore(dipViolations, structure.classes.length);
    }

    // Calculate overall score
    const enabledCount = this.config.enabledPrinciples.length;
    const overallScore = enabledCount > 0
      ? this.config.enabledPrinciples.reduce((sum, p) => sum + principleScores[p], 0) / enabledCount
      : 100;

    // Generate recommendations
    const recommendations = this.generateRecommendations(violations, principleScores);

    // Generate summary
    const summary = this.generateSummary(structure, violations);

    return {
      score: Math.round(overallScore),
      principleScores,
      violations,
      recommendations,
      summary,
    };
  }

  /**
   * Validate source code string
   */
  validateCode(code: string): SOLIDValidationResult {
    const structure = this.parseCodeStructure(code);
    return this.validate(structure);
  }

  /**
   * Validate Single Responsibility Principle
   */
  private validateSRP(structure: CodeStructure): SOLIDViolation[] {
    const violations: SOLIDViolation[] = [];

    for (const cls of structure.classes) {
      if (cls.isInterface) continue;

      // Check method count
      if (cls.methods.length > this.config.srpMethodThreshold) {
        violations.push({
          principle: 'S',
          severity: 'high',
          element: cls.name,
          description: `Class has ${cls.methods.length} methods (threshold: ${this.config.srpMethodThreshold})`,
          suggestion: 'Consider extracting related methods into separate classes',
        });
      }

      // Check for god class indicators
      const godClassIndicators = this.detectGodClassIndicators(cls);
      if (godClassIndicators.length > 2) {
        violations.push({
          principle: 'S',
          severity: 'medium',
          element: cls.name,
          description: `Class appears to handle multiple responsibilities: ${godClassIndicators.join(', ')}`,
          suggestion: 'Split into smaller, focused classes',
        });
      }
    }

    return violations;
  }

  /**
   * Validate Open/Closed Principle
   */
  private validateOCP(structure: CodeStructure): SOLIDViolation[] {
    const violations: SOLIDViolation[] = [];

    for (const cls of structure.classes) {
      if (cls.isInterface || cls.isAbstract) continue;

      // Check for type-checking patterns (suggests OCP violation)
      for (const method of cls.methods) {
        if (this.suggestsTypeChecking(method)) {
          violations.push({
            principle: 'O',
            severity: 'medium',
            element: `${cls.name}.${method}`,
            description: 'Method name suggests type-checking logic',
            suggestion: 'Consider using polymorphism instead of type checks',
          });
        }
      }

      // Check if class could benefit from abstraction
      if (!cls.isAbstract && !cls.implements.length && cls.methods.length > 3) {
        const hasVariantMethods = cls.methods.some((m) => 
          m.includes('type') || m.includes('kind') || m.includes('mode')
        );
        if (hasVariantMethods) {
          violations.push({
            principle: 'O',
            severity: 'low',
            element: cls.name,
            description: 'Class might benefit from strategy pattern',
            suggestion: 'Extract variant behavior into strategy classes',
          });
        }
      }
    }

    return violations;
  }

  /**
   * Validate Liskov Substitution Principle
   */
  private validateLSP(structure: CodeStructure): SOLIDViolation[] {
    const violations: SOLIDViolation[] = [];

    // Build inheritance hierarchy
    const hierarchy = this.buildHierarchy(structure);

    for (const [child, parent] of hierarchy) {
      const childClass = structure.classes.find((c) => c.name === child);
      const parentClass = structure.classes.find((c) => c.name === parent);

      if (!childClass || !parentClass) continue;

      // Check for empty/noop implementations
      const parentMethods = new Set(parentClass.methods);
      for (const method of childClass.methods) {
        if (parentMethods.has(method)) {
          // Check for potential violation indicators in method names
          if (method.startsWith('throw') || method.includes('NotSupported')) {
            violations.push({
              principle: 'L',
              severity: 'high',
              element: `${child}.${method}`,
              description: 'Method might throw or be unsupported, violating substitutability',
              suggestion: 'Ensure subclass can fully substitute parent class',
            });
          }
        }
      }

      // Check if child removes parent functionality
      if (childClass.methods.length < parentClass.methods.length / 2) {
        violations.push({
          principle: 'L',
          severity: 'medium',
          element: child,
          description: 'Subclass has significantly fewer methods than parent',
          suggestion: 'Verify that inheritance is appropriate here',
        });
      }
    }

    return violations;
  }

  /**
   * Validate Interface Segregation Principle
   */
  private validateISP(structure: CodeStructure): SOLIDViolation[] {
    const violations: SOLIDViolation[] = [];

    for (const cls of structure.classes) {
      if (!cls.isInterface) continue;

      // Check interface size
      if (cls.methods.length > this.config.ispMethodThreshold) {
        violations.push({
          principle: 'I',
          severity: 'medium',
          element: cls.name,
          description: `Interface has ${cls.methods.length} methods (threshold: ${this.config.ispMethodThreshold})`,
          suggestion: 'Consider splitting into smaller, focused interfaces',
        });
      }

      // Check for unrelated method groups
      const methodGroups = this.groupMethodsByPurpose(cls.methods);
      if (methodGroups.size > 2) {
        violations.push({
          principle: 'I',
          severity: 'low',
          element: cls.name,
          description: `Interface appears to have ${methodGroups.size} distinct method groups`,
          suggestion: 'Split into multiple focused interfaces',
        });
      }
    }

    // Check for fat interface implementations
    for (const cls of structure.classes) {
      if (cls.isInterface) continue;

      for (const impl of cls.implements) {
        const iface = structure.classes.find((c) => c.name === impl && c.isInterface);
        if (iface && iface.methods.length > this.config.ispMethodThreshold * 2) {
          violations.push({
            principle: 'I',
            severity: 'medium',
            element: cls.name,
            description: `Implements large interface ${impl} (${iface.methods.length} methods)`,
            suggestion: 'Verify all interface methods are needed',
          });
        }
      }
    }

    return violations;
  }

  /**
   * Validate Dependency Inversion Principle
   */
  private validateDIP(structure: CodeStructure): SOLIDViolation[] {
    const violations: SOLIDViolation[] = [];

    // Get all interfaces/abstracts
    const abstractions = new Set(
      structure.classes
        .filter((c) => c.isInterface || c.isAbstract)
        .map((c) => c.name)
    );

    for (const cls of structure.classes) {
      if (cls.isInterface || cls.isAbstract) continue;

      // Check if high-level class depends on concretions
      const isHighLevel = cls.name.includes('Manager') || 
                         cls.name.includes('Service') ||
                         cls.name.includes('Controller') ||
                         cls.name.includes('Handler');

      if (isHighLevel) {
        // Check relationships for concrete dependencies
        const dependencies = structure.relationships
          .filter((r) => r.source === cls.name && r.type === 'dependency');

        for (const dep of dependencies) {
          if (!abstractions.has(dep.target)) {
            // Might be depending on concrete class
            const targetClass = structure.classes.find((c) => c.name === dep.target);
            if (targetClass && !targetClass.isInterface && !targetClass.isAbstract) {
              violations.push({
                principle: 'D',
                severity: 'medium',
                element: cls.name,
                description: `High-level class depends on concrete ${dep.target}`,
                suggestion: `Depend on an abstraction (interface) instead of ${dep.target}`,
              });
            }
          }
        }

        // Check if using constructor injection
        const usesInjection = cls.methods.some((m) => 
          m.includes('inject') || m === 'constructor'
        ) && cls.implements.length > 0;

        if (!usesInjection && dependencies.length > 0) {
          violations.push({
            principle: 'D',
            severity: 'low',
            element: cls.name,
            description: 'Consider using dependency injection',
            suggestion: 'Inject dependencies through constructor',
          });
        }
      }
    }

    return violations;
  }

  /**
   * Detect god class indicators
   */
  private detectGodClassIndicators(cls: ClassInfo): string[] {
    const indicators: string[] = [];
    const methodPrefixes = new Map<string, number>();

    for (const method of cls.methods) {
      // Extract prefix (e.g., "get", "set", "handle", "process")
      const match = method.match(/^([a-z]+)/i);
      if (match) {
        const prefix = match[1].toLowerCase();
        methodPrefixes.set(prefix, (methodPrefixes.get(prefix) ?? 0) + 1);
      }
    }

    // Different responsibility indicators
    const responsibilityPrefixes = ['handle', 'process', 'calculate', 'validate', 'render', 'save', 'load', 'send'];
    for (const prefix of responsibilityPrefixes) {
      if ((methodPrefixes.get(prefix) ?? 0) >= 2) {
        indicators.push(`${prefix}*`);
      }
    }

    return indicators;
  }

  /**
   * Check if method name suggests type checking
   */
  private suggestsTypeChecking(methodName: string): boolean {
    const patterns = [
      /^handle\w+Type$/i,
      /^process\w+Kind$/i,
      /^by(Type|Kind|Mode)$/i,
    ];
    return patterns.some((p) => p.test(methodName));
  }

  /**
   * Build inheritance hierarchy
   */
  private buildHierarchy(structure: CodeStructure): Map<string, string> {
    const hierarchy = new Map<string, string>();

    for (const cls of structure.classes) {
      if (cls.extends) {
        hierarchy.set(cls.name, cls.extends);
      }
    }

    return hierarchy;
  }

  /**
   * Group methods by purpose
   */
  private groupMethodsByPurpose(methods: string[]): Map<string, string[]> {
    const groups = new Map<string, string[]>();

    for (const method of methods) {
      // Simple grouping by prefix
      const match = method.match(/^([a-z]+)/i);
      const prefix = match ? match[1].toLowerCase() : 'other';
      
      if (!groups.has(prefix)) {
        groups.set(prefix, []);
      }
      groups.get(prefix)!.push(method);
    }

    return groups;
  }

  /**
   * Calculate score from violations
   */
  private calculateScore(violations: SOLIDViolation[], classCount: number): number {
    if (classCount === 0) return 100;

    const penaltyMap = { high: 20, medium: 10, low: 5 };
    const totalPenalty = violations.reduce(
      (sum, v) => sum + penaltyMap[v.severity],
      0
    );

    const maxPenalty = classCount * 30;
    const penalty = Math.min(totalPenalty, maxPenalty);
    
    return Math.max(0, Math.round(100 - (penalty / maxPenalty) * 100));
  }

  /**
   * Generate recommendations
   */
  private generateRecommendations(
    violations: SOLIDViolation[],
    scores: Record<SOLIDPrinciple, number>
  ): string[] {
    const recommendations: string[] = [];

    // Prioritize lowest scores
    const sortedPrinciples = (Object.keys(scores) as SOLIDPrinciple[])
      .sort((a, b) => scores[a] - scores[b]);

    for (const principle of sortedPrinciples.slice(0, 2)) {
      if (scores[principle] < 70) {
        const info = SOLID_PRINCIPLES[principle];
        recommendations.push(
          `Focus on ${info.name} (${principle}): ${info.description}`
        );
      }
    }

    // Add specific recommendations for high-severity violations
    const highViolations = violations.filter((v) => v.severity === 'high');
    for (const v of highViolations.slice(0, 3)) {
      recommendations.push(`Fix ${v.element}: ${v.suggestion}`);
    }

    if (recommendations.length === 0) {
      recommendations.push('Good SOLID compliance! Continue following best practices.');
    }

    return recommendations;
  }

  /**
   * Generate summary
   */
  private generateSummary(
    structure: CodeStructure,
    violations: SOLIDViolation[]
  ): SOLIDSummary {
    const classesAnalyzed = structure.classes.filter((c) => !c.isInterface).length;
    const classesWithViolations = new Set(violations.map((v) => v.element.split('.')[0])).size;

    const violationsByPrinciple: Record<SOLIDPrinciple, number> = {
      S: 0, O: 0, L: 0, I: 0, D: 0,
    };
    for (const v of violations) {
      violationsByPrinciple[v.principle]++;
    }

    const violationRatio = classesAnalyzed > 0 
      ? classesWithViolations / classesAnalyzed 
      : 0;

    let complianceLevel: SOLIDSummary['complianceLevel'];
    if (violationRatio < 0.1) complianceLevel = 'excellent';
    else if (violationRatio < 0.3) complianceLevel = 'good';
    else if (violationRatio < 0.5) complianceLevel = 'moderate';
    else complianceLevel = 'poor';

    return {
      classesAnalyzed,
      classesWithViolations,
      totalViolations: violations.length,
      violationsByPrinciple,
      complianceLevel,
    };
  }

  /**
   * Parse code into structure (simplified)
   */
  private parseCodeStructure(code: string): CodeStructure {
    const classes: ClassInfo[] = [];
    const relationships: RelationshipInfo[] = [];

    // Simple regex-based parsing
    const classRegex = /(?:export\s+)?(?:abstract\s+)?(class|interface)\s+(\w+)(?:\s+extends\s+(\w+))?(?:\s+implements\s+([^{]+))?/g;
    let match;
    
    while ((match = classRegex.exec(code)) !== null) {
      const isInterface = match[1] === 'interface';
      const isAbstract = code.substring(Math.max(0, match.index - 20), match.index).includes('abstract');
      
      const methods = this.extractMethods(code, match[2]);
      const properties = this.extractProperties(code, match[2]);

      classes.push({
        name: match[2],
        isInterface,
        isAbstract,
        methods,
        properties,
        extends: match[3],
        implements: match[4] ? match[4].split(',').map((s) => s.trim()) : [],
      });

      if (match[3]) {
        relationships.push({
          source: match[2],
          target: match[3],
          type: 'inheritance',
        });
      }
    }

    return { classes, functions: [], relationships };
  }

  /**
   * Extract methods
   */
  private extractMethods(code: string, className: string): string[] {
    const methods: string[] = [];
    const classStart = code.indexOf(`class ${className}`) || code.indexOf(`interface ${className}`);
    if (classStart === -1) return methods;

    let braceCount = 0;
    let classEnd = classStart;
    for (let i = classStart; i < code.length; i++) {
      if (code[i] === '{') braceCount++;
      if (code[i] === '}') braceCount--;
      if (braceCount === 0 && code[i] === '}') {
        classEnd = i;
        break;
      }
    }

    const classBody = code.substring(classStart, classEnd);
    const methodRegex = /(?:public|private|protected|static|async)?\s*(\w+)\s*\([^)]*\)/g;
    let match;
    while ((match = methodRegex.exec(classBody)) !== null) {
      if (!['constructor', 'if', 'for', 'while', 'switch'].includes(match[1])) {
        methods.push(match[1]);
      }
    }

    return methods;
  }

  /**
   * Extract properties
   */
  private extractProperties(code: string, className: string): string[] {
    const properties: string[] = [];
    const classStart = code.indexOf(`class ${className}`);
    if (classStart === -1) return properties;

    const classBody = code.substring(classStart, classStart + 1000);
    const propRegex = /(?:public|private|protected|static|readonly)?\s+(\w+)\s*[;:=]/g;
    let match;
    while ((match = propRegex.exec(classBody)) !== null) {
      properties.push(match[1]);
    }

    return properties;
  }

  /**
   * Get principle information
   */
  static getPrincipleInfo(principle: SOLIDPrinciple): SOLIDPrincipleInfo {
    return SOLID_PRINCIPLES[principle];
  }

  /**
   * Get all principles
   */
  static getAllPrinciples(): SOLIDPrincipleInfo[] {
    return Object.values(SOLID_PRINCIPLES);
  }
}

/**
 * Create SOLID validator instance
 */
export function createSOLIDValidator(
  config?: Partial<SOLIDValidatorConfig>
): SOLIDValidator {
  return new SOLIDValidator(config);
}
