/**
 * Pattern Conformance Checker
 * 
 * Checks code conformance to design patterns
 * 
 * @packageDocumentation
 * @module codegen/pattern-conformance
 * 
 * @see REQ-COD-003 - Pattern Conformance
 * @see Article V - Design Standards
 */

import type { PatternCategory } from '../types/index.js';

/**
 * Conformance level
 */
export type ConformanceLevel = 'full' | 'partial' | 'minimal' | 'none';

/**
 * Pattern conformance result
 */
export interface PatternConformanceResult {
  /** Pattern ID */
  patternId: string;
  /** Pattern name */
  patternName: string;
  /** Category */
  category: PatternCategory;
  /** Conformance level */
  conformance: ConformanceLevel;
  /** Conformance score (0-100) */
  score: number;
  /** Matched elements */
  matchedElements: ConformanceElement[];
  /** Missing elements */
  missingElements: ConformanceElement[];
  /** Violations */
  violations: ConformanceViolation[];
  /** Recommendations */
  recommendations: string[];
}

/**
 * Conformance element
 */
export interface ConformanceElement {
  /** Element type */
  type: 'class' | 'interface' | 'method' | 'property' | 'relationship';
  /** Element name */
  name: string;
  /** Expected role */
  role: string;
  /** Location in code */
  location?: {
    file?: string;
    line?: number;
  };
}

/**
 * Conformance violation
 */
export interface ConformanceViolation {
  /** Violation ID */
  id: string;
  /** Severity */
  severity: 'error' | 'warning' | 'info';
  /** Message */
  message: string;
  /** Element */
  element?: string;
  /** Location */
  location?: {
    file?: string;
    line?: number;
  };
  /** Fix suggestion */
  fix?: string;
}

/**
 * Pattern specification
 */
export interface PatternSpecification {
  /** Pattern ID */
  id: string;
  /** Pattern name */
  name: string;
  /** Category */
  category: PatternCategory;
  /** Required participants */
  participants: ParticipantSpec[];
  /** Required relationships */
  relationships: RelationshipSpec[];
  /** Method signatures */
  methodSignatures?: MethodSignatureSpec[];
  /** Constraints */
  constraints?: ConstraintSpec[];
}

/**
 * Participant specification
 */
export interface ParticipantSpec {
  /** Role name */
  role: string;
  /** Type */
  type: 'class' | 'interface' | 'abstract';
  /** Is required */
  required: boolean;
  /** Name pattern */
  namePattern?: RegExp;
  /** Required methods */
  requiredMethods?: string[];
  /** Required properties */
  requiredProperties?: string[];
}

/**
 * Relationship specification
 */
export interface RelationshipSpec {
  /** From role */
  from: string;
  /** To role */
  to: string;
  /** Relationship type */
  type: 'extends' | 'implements' | 'composes' | 'aggregates' | 'uses' | 'creates';
  /** Is required */
  required: boolean;
}

/**
 * Method signature specification
 */
export interface MethodSignatureSpec {
  /** Role */
  role: string;
  /** Method name pattern */
  namePattern: RegExp;
  /** Return type pattern */
  returnTypePattern?: RegExp;
  /** Parameters */
  parameters?: Array<{
    typePattern: RegExp;
    optional?: boolean;
  }>;
}

/**
 * Constraint specification
 */
export interface ConstraintSpec {
  /** Constraint ID */
  id: string;
  /** Description */
  description: string;
  /** Check function */
  check: (context: ConformanceContext) => boolean;
  /** Severity */
  severity: 'error' | 'warning';
}

/**
 * Conformance context
 */
export interface ConformanceContext {
  /** Code being checked */
  code: string;
  /** File path */
  file: string;
  /** Detected classes */
  classes: ClassInfo[];
  /** Detected interfaces */
  interfaces: InterfaceInfo[];
  /** Detected relationships */
  relationships: RelationshipInfo[];
}

/**
 * Class info for conformance checking
 */
export interface ClassInfo {
  /** Class name */
  name: string;
  /** Line number */
  line: number;
  /** Methods */
  methods: string[];
  /** Properties */
  properties: string[];
  /** Extends */
  extends?: string;
  /** Implements */
  implements: string[];
  /** Is abstract */
  isAbstract: boolean;
}

/**
 * Interface info
 */
export interface InterfaceInfo {
  /** Interface name */
  name: string;
  /** Line number */
  line: number;
  /** Methods */
  methods: string[];
  /** Properties */
  properties: string[];
  /** Extends */
  extends: string[];
}

/**
 * Relationship info
 */
export interface RelationshipInfo {
  /** From class/interface */
  from: string;
  /** To class/interface */
  to: string;
  /** Relationship type */
  type: 'extends' | 'implements' | 'composes' | 'aggregates' | 'uses' | 'creates';
}

/**
 * Pattern conformance checker configuration
 */
export interface PatternConformanceConfig {
  /** Minimum conformance score to pass */
  minScore: number;
  /** Strict mode */
  strictMode: boolean;
  /** Custom pattern specifications */
  customPatterns?: PatternSpecification[];
}

/**
 * Default configuration
 */
export const DEFAULT_CONFORMANCE_CONFIG: PatternConformanceConfig = {
  minScore: 70,
  strictMode: false,
};

/**
 * Built-in pattern specifications
 */
const PATTERN_SPECIFICATIONS: PatternSpecification[] = [
  {
    id: 'singleton',
    name: 'Singleton',
    category: 'creational',
    participants: [
      {
        role: 'Singleton',
        type: 'class',
        required: true,
        requiredMethods: ['getInstance'],
        requiredProperties: ['instance'],
      },
    ],
    relationships: [],
    constraints: [
      {
        id: 'private-constructor',
        description: 'Constructor should be private',
        severity: 'warning',
        check: (ctx) => {
          return ctx.code.includes('private constructor') ||
                 ctx.code.includes('private static instance');
        },
      },
    ],
  },
  {
    id: 'factory-method',
    name: 'Factory Method',
    category: 'creational',
    participants: [
      {
        role: 'Creator',
        type: 'abstract',
        required: true,
        requiredMethods: ['create', 'factoryMethod', 'make'],
      },
      {
        role: 'ConcreteCreator',
        type: 'class',
        required: true,
      },
      {
        role: 'Product',
        type: 'interface',
        required: true,
      },
      {
        role: 'ConcreteProduct',
        type: 'class',
        required: true,
      },
    ],
    relationships: [
      { from: 'ConcreteCreator', to: 'Creator', type: 'extends', required: true },
      { from: 'ConcreteProduct', to: 'Product', type: 'implements', required: true },
      { from: 'Creator', to: 'Product', type: 'creates', required: true },
    ],
  },
  {
    id: 'observer',
    name: 'Observer',
    category: 'behavioral',
    participants: [
      {
        role: 'Subject',
        type: 'interface',
        required: true,
        requiredMethods: ['attach', 'detach', 'notify', 'subscribe', 'unsubscribe'],
      },
      {
        role: 'Observer',
        type: 'interface',
        required: true,
        requiredMethods: ['update', 'notify', 'onEvent'],
      },
      {
        role: 'ConcreteSubject',
        type: 'class',
        required: true,
      },
      {
        role: 'ConcreteObserver',
        type: 'class',
        required: true,
      },
    ],
    relationships: [
      { from: 'ConcreteSubject', to: 'Subject', type: 'implements', required: true },
      { from: 'ConcreteObserver', to: 'Observer', type: 'implements', required: true },
      { from: 'Subject', to: 'Observer', type: 'aggregates', required: true },
    ],
  },
  {
    id: 'strategy',
    name: 'Strategy',
    category: 'behavioral',
    participants: [
      {
        role: 'Strategy',
        type: 'interface',
        required: true,
        requiredMethods: ['execute', 'apply', 'run'],
      },
      {
        role: 'ConcreteStrategy',
        type: 'class',
        required: true,
      },
      {
        role: 'Context',
        type: 'class',
        required: true,
        requiredMethods: ['setStrategy', 'executeStrategy'],
      },
    ],
    relationships: [
      { from: 'ConcreteStrategy', to: 'Strategy', type: 'implements', required: true },
      { from: 'Context', to: 'Strategy', type: 'composes', required: true },
    ],
  },
  {
    id: 'decorator',
    name: 'Decorator',
    category: 'structural',
    participants: [
      {
        role: 'Component',
        type: 'interface',
        required: true,
      },
      {
        role: 'ConcreteComponent',
        type: 'class',
        required: true,
      },
      {
        role: 'Decorator',
        type: 'abstract',
        required: true,
      },
      {
        role: 'ConcreteDecorator',
        type: 'class',
        required: true,
      },
    ],
    relationships: [
      { from: 'ConcreteComponent', to: 'Component', type: 'implements', required: true },
      { from: 'Decorator', to: 'Component', type: 'implements', required: true },
      { from: 'Decorator', to: 'Component', type: 'composes', required: true },
      { from: 'ConcreteDecorator', to: 'Decorator', type: 'extends', required: true },
    ],
  },
  {
    id: 'adapter',
    name: 'Adapter',
    category: 'structural',
    participants: [
      {
        role: 'Target',
        type: 'interface',
        required: true,
      },
      {
        role: 'Adapter',
        type: 'class',
        required: true,
      },
      {
        role: 'Adaptee',
        type: 'class',
        required: true,
      },
    ],
    relationships: [
      { from: 'Adapter', to: 'Target', type: 'implements', required: true },
      { from: 'Adapter', to: 'Adaptee', type: 'composes', required: true },
    ],
  },
  {
    id: 'repository',
    name: 'Repository',
    category: 'architectural',
    participants: [
      {
        role: 'Repository',
        type: 'interface',
        required: true,
        requiredMethods: ['find', 'findById', 'save', 'delete', 'findAll'],
      },
      {
        role: 'ConcreteRepository',
        type: 'class',
        required: true,
      },
      {
        role: 'Entity',
        type: 'class',
        required: true,
      },
    ],
    relationships: [
      { from: 'ConcreteRepository', to: 'Repository', type: 'implements', required: true },
    ],
  },
];

/**
 * Pattern Conformance Checker
 */
export class PatternConformanceChecker {
  private config: PatternConformanceConfig;
  private patterns: PatternSpecification[];

  constructor(config?: Partial<PatternConformanceConfig>) {
    this.config = { ...DEFAULT_CONFORMANCE_CONFIG, ...config };
    this.patterns = [...PATTERN_SPECIFICATIONS];
    
    if (this.config.customPatterns) {
      this.patterns.push(...this.config.customPatterns);
    }
  }

  /**
   * Check conformance to a specific pattern
   */
  checkPattern(
    code: string,
    patternId: string,
    file = 'unknown'
  ): PatternConformanceResult | null {
    const pattern = this.patterns.find((p) => p.id === patternId);
    if (!pattern) return null;

    const context = this.buildContext(code, file);
    return this.evaluateConformance(pattern, context);
  }

  /**
   * Check conformance to all patterns
   */
  checkAllPatterns(
    code: string,
    file = 'unknown'
  ): PatternConformanceResult[] {
    const context = this.buildContext(code, file);
    const results: PatternConformanceResult[] = [];

    for (const pattern of this.patterns) {
      const result = this.evaluateConformance(pattern, context);
      if (result.score > 0) {
        results.push(result);
      }
    }

    return results.sort((a, b) => b.score - a.score);
  }

  /**
   * Check if code meets minimum conformance
   */
  meetsMinimumConformance(result: PatternConformanceResult): boolean {
    return result.score >= this.config.minScore;
  }

  /**
   * Build conformance context from code
   */
  private buildContext(code: string, file: string): ConformanceContext {
    return {
      code,
      file,
      classes: this.extractClasses(code),
      interfaces: this.extractInterfaces(code),
      relationships: this.extractRelationships(code),
    };
  }

  /**
   * Extract classes from code
   */
  private extractClasses(code: string): ClassInfo[] {
    const classes: ClassInfo[] = [];
    const regex = /(?:abstract\s+)?class\s+(\w+)(?:\s+extends\s+(\w+))?(?:\s+implements\s+([^{]+))?\s*\{/g;
    let match;

    while ((match = regex.exec(code)) !== null) {
      const name = match[1];
      const line = code.substring(0, match.index).split('\n').length;
      const extendsClass = match[2];
      const implementsStr = match[3];
      const isAbstract = match[0].startsWith('abstract');

      // Find class body
      const startIndex = match.index + match[0].length - 1;
      const body = this.extractBody(code, startIndex);

      // Extract methods and properties
      const methods = this.extractMethodNames(body);
      const properties = this.extractPropertyNames(body);
      const implements_ = implementsStr
        ? implementsStr.split(',').map((s) => s.trim())
        : [];

      classes.push({
        name,
        line,
        methods,
        properties,
        extends: extendsClass,
        implements: implements_,
        isAbstract,
      });
    }

    return classes;
  }

  /**
   * Extract interfaces from code
   */
  private extractInterfaces(code: string): InterfaceInfo[] {
    const interfaces: InterfaceInfo[] = [];
    const regex = /interface\s+(\w+)(?:\s+extends\s+([^{]+))?\s*\{/g;
    let match;

    while ((match = regex.exec(code)) !== null) {
      const name = match[1];
      const line = code.substring(0, match.index).split('\n').length;
      const extendsStr = match[2];

      const startIndex = match.index + match[0].length - 1;
      const body = this.extractBody(code, startIndex);

      const methods = this.extractMethodNames(body);
      const properties = this.extractPropertyNames(body);
      const extends_ = extendsStr
        ? extendsStr.split(',').map((s) => s.trim())
        : [];

      interfaces.push({
        name,
        line,
        methods,
        properties,
        extends: extends_,
      });
    }

    return interfaces;
  }

  /**
   * Extract relationships from code
   */
  private extractRelationships(code: string): RelationshipInfo[] {
    const relationships: RelationshipInfo[] = [];
    const classes = this.extractClasses(code);

    for (const cls of classes) {
      // Extends relationship
      if (cls.extends) {
        relationships.push({
          from: cls.name,
          to: cls.extends,
          type: 'extends',
        });
      }

      // Implements relationships
      for (const impl of cls.implements) {
        relationships.push({
          from: cls.name,
          to: impl,
          type: 'implements',
        });
      }

      // Composition/aggregation (check for property types)
      for (const prop of cls.properties) {
        const propMatch = code.match(new RegExp(`${prop}\\s*[?:]\\s*(\\w+)`));
        if (propMatch && propMatch[1]) {
          const targetType = propMatch[1];
          // Check if it's a known class or interface
          const isKnown = classes.some((c) => c.name === targetType);
          if (isKnown) {
            relationships.push({
              from: cls.name,
              to: targetType,
              type: 'composes',
            });
          }
        }
      }
    }

    return relationships;
  }

  /**
   * Extract body between braces
   */
  private extractBody(code: string, startIndex: number): string {
    let braceCount = 1;
    let endIndex = startIndex + 1;

    while (braceCount > 0 && endIndex < code.length) {
      if (code[endIndex] === '{') braceCount++;
      else if (code[endIndex] === '}') braceCount--;
      endIndex++;
    }

    return code.substring(startIndex, endIndex);
  }

  /**
   * Extract method names from body
   */
  private extractMethodNames(body: string): string[] {
    const methods: string[] = [];
    const regex = /(?:async\s+)?(?:static\s+)?(\w+)\s*\([^)]*\)\s*[:{]/g;
    let match;

    while ((match = regex.exec(body)) !== null) {
      if (!['constructor', 'if', 'for', 'while', 'switch'].includes(match[1])) {
        methods.push(match[1]);
      }
    }

    return methods;
  }

  /**
   * Extract property names from body
   */
  private extractPropertyNames(body: string): string[] {
    const properties: string[] = [];
    const regex = /(?:private|public|protected|readonly)?\s*(\w+)\s*[?:]?\s*:/g;
    let match;

    while ((match = regex.exec(body)) !== null) {
      properties.push(match[1]);
    }

    return properties;
  }

  /**
   * Evaluate conformance
   */
  private evaluateConformance(
    pattern: PatternSpecification,
    context: ConformanceContext
  ): PatternConformanceResult {
    const matchedElements: ConformanceElement[] = [];
    const missingElements: ConformanceElement[] = [];
    const violations: ConformanceViolation[] = [];
    const recommendations: string[] = [];

    // Check participants
    for (const participant of pattern.participants) {
      const matched = this.findParticipant(participant, context);
      
      if (matched) {
        matchedElements.push({
          type: participant.type === 'abstract' ? 'class' : participant.type,
          name: matched,
          role: participant.role,
          location: this.getLocation(matched, context),
        });

        // Check required methods
        if (participant.requiredMethods) {
          const entity = context.classes.find((c) => c.name === matched) ||
                        context.interfaces.find((i) => i.name === matched);
          
          for (const method of participant.requiredMethods) {
            const hasMethod = entity?.methods.some((m) =>
              m.toLowerCase().includes(method.toLowerCase())
            );
            if (!hasMethod) {
              violations.push({
                id: `missing-method-${participant.role}-${method}`,
                severity: 'warning',
                message: `${participant.role} should have method: ${method}`,
                element: matched,
                fix: `Add method ${method}() to ${matched}`,
              });
            }
          }
        }
      } else if (participant.required) {
        missingElements.push({
          type: participant.type === 'abstract' ? 'class' : participant.type,
          name: 'Unknown',
          role: participant.role,
        });
        recommendations.push(`Create ${participant.type} for role: ${participant.role}`);
      }
    }

    // Check relationships
    for (const rel of pattern.relationships) {
      const hasRel = context.relationships.some(
        (r) => this.matchesRole(r.from, rel.from, pattern, context) &&
               this.matchesRole(r.to, rel.to, pattern, context) &&
               r.type === rel.type
      );

      if (!hasRel && rel.required) {
        violations.push({
          id: `missing-relationship-${rel.from}-${rel.to}`,
          severity: this.config.strictMode ? 'error' : 'warning',
          message: `Missing ${rel.type} relationship from ${rel.from} to ${rel.to}`,
          fix: `Add ${rel.type} relationship`,
        });
      }
    }

    // Check constraints
    for (const constraint of pattern.constraints ?? []) {
      if (!constraint.check(context)) {
        violations.push({
          id: constraint.id,
          severity: constraint.severity,
          message: constraint.description,
        });
      }
    }

    // Calculate score
    const totalRequired = pattern.participants.filter((p) => p.required).length +
                         pattern.relationships.filter((r) => r.required).length;
    const matched = matchedElements.length;
    const score = totalRequired > 0
      ? Math.round((matched / totalRequired) * 100 - violations.length * 5)
      : 0;

    return {
      patternId: pattern.id,
      patternName: pattern.name,
      category: pattern.category,
      conformance: this.getConformanceLevel(Math.max(0, score)),
      score: Math.max(0, score),
      matchedElements,
      missingElements,
      violations,
      recommendations,
    };
  }

  /**
   * Find participant in context
   */
  private findParticipant(
    participant: ParticipantSpec,
    context: ConformanceContext
  ): string | null {
    const candidates = participant.type === 'interface'
      ? context.interfaces.map((i) => i.name)
      : context.classes.filter((c) =>
          participant.type === 'abstract' ? c.isAbstract : !c.isAbstract
        ).map((c) => c.name);

    // Check by name pattern
    if (participant.namePattern) {
      const match = candidates.find((c) => participant.namePattern!.test(c));
      if (match) return match;
    }

    // Check by role name similarity
    const roleLower = participant.role.toLowerCase();
    const match = candidates.find((c) =>
      c.toLowerCase().includes(roleLower) ||
      roleLower.includes(c.toLowerCase())
    );

    return match ?? null;
  }

  /**
   * Check if name matches role
   */
  private matchesRole(
    name: string,
    role: string,
    pattern: PatternSpecification,
    context: ConformanceContext
  ): boolean {
    const participant = pattern.participants.find((p) => p.role === role);
    if (!participant) return false;

    const found = this.findParticipant(participant, context);
    return found === name;
  }

  /**
   * Get location for entity
   */
  private getLocation(
    name: string,
    context: ConformanceContext
  ): { file?: string; line?: number } {
    const cls = context.classes.find((c) => c.name === name);
    if (cls) return { file: context.file, line: cls.line };

    const iface = context.interfaces.find((i) => i.name === name);
    if (iface) return { file: context.file, line: iface.line };

    return { file: context.file };
  }

  /**
   * Get conformance level from score
   */
  private getConformanceLevel(score: number): ConformanceLevel {
    if (score >= 90) return 'full';
    if (score >= 70) return 'partial';
    if (score >= 40) return 'minimal';
    return 'none';
  }

  /**
   * Get available patterns
   */
  getPatterns(): PatternSpecification[] {
    return [...this.patterns];
  }

  /**
   * Add custom pattern
   */
  addPattern(pattern: PatternSpecification): void {
    this.patterns.push(pattern);
  }
}

/**
 * Create pattern conformance checker instance
 */
export function createPatternConformanceChecker(
  config?: Partial<PatternConformanceConfig>
): PatternConformanceChecker {
  return new PatternConformanceChecker(config);
}
