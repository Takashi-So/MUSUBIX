/**
 * Design Pattern Detector
 * 
 * Detects and suggests design patterns in code and design documents
 * 
 * @packageDocumentation
 * @module design/pattern-detector
 * 
 * @see REQ-DES-001 - Design Pattern Detection
 * @see Article III - Design Validation
 */

/**
 * Design pattern categories
 */
export type PatternCategory =
  | 'creational'
  | 'structural'
  | 'behavioral'
  | 'architectural';

/**
 * Design pattern definition
 */
export interface DesignPattern {
  /** Pattern ID */
  id: string;
  /** Pattern name */
  name: string;
  /** Category */
  category: PatternCategory;
  /** Description */
  description: string;
  /** Intent */
  intent: string;
  /** When to use */
  applicability: string[];
  /** Key participants */
  participants: PatternParticipant[];
  /** Detection indicators */
  indicators: PatternIndicator[];
  /** Related patterns */
  relatedPatterns: string[];
}

/**
 * Pattern participant
 */
export interface PatternParticipant {
  /** Role name */
  name: string;
  /** Description */
  description: string;
  /** Is optional */
  optional: boolean;
}

/**
 * Pattern indicator for detection
 */
export interface PatternIndicator {
  /** Indicator type */
  type: 'naming' | 'structure' | 'method' | 'relation';
  /** Detection pattern (regex or keyword) */
  pattern: string;
  /** Weight for scoring */
  weight: number;
}

/**
 * Pattern detection result
 */
export interface PatternDetectionResult {
  /** Detected pattern */
  pattern: DesignPattern;
  /** Confidence score (0-1) */
  confidence: number;
  /** Where detected */
  location: PatternLocation;
  /** Matched indicators */
  matchedIndicators: MatchedIndicator[];
  /** Missing elements */
  missingElements: string[];
  /** Suggestions */
  suggestions: string[];
}

/**
 * Pattern location
 */
export interface PatternLocation {
  /** File path */
  file?: string;
  /** Start line */
  startLine?: number;
  /** End line */
  endLine?: number;
  /** Class/module name */
  className?: string;
  /** Method names involved */
  methods?: string[];
}

/**
 * Matched indicator
 */
export interface MatchedIndicator {
  /** Indicator */
  indicator: PatternIndicator;
  /** Matched text */
  matchedText: string;
  /** Location */
  location: string;
}

/**
 * Pattern suggestion
 */
export interface PatternSuggestion {
  /** Suggested pattern */
  pattern: DesignPattern;
  /** Reason for suggestion */
  reason: string;
  /** Applicability score (0-1) */
  applicability: number;
  /** Benefits */
  benefits: string[];
  /** Implementation hints */
  implementationHints: string[];
}

/**
 * Code structure for analysis
 */
export interface CodeStructure {
  /** Classes/interfaces */
  classes: ClassInfo[];
  /** Functions */
  functions: FunctionInfo[];
  /** Relationships */
  relationships: RelationshipInfo[];
}

/**
 * Class information
 */
export interface ClassInfo {
  /** Class name */
  name: string;
  /** Is interface */
  isInterface: boolean;
  /** Is abstract */
  isAbstract: boolean;
  /** Methods */
  methods: string[];
  /** Properties */
  properties: string[];
  /** Extends */
  extends?: string;
  /** Implements */
  implements: string[];
}

/**
 * Function information
 */
export interface FunctionInfo {
  /** Function name */
  name: string;
  /** Parameters */
  parameters: string[];
  /** Return type */
  returnType?: string;
  /** Is static */
  isStatic: boolean;
}

/**
 * Relationship information
 */
export interface RelationshipInfo {
  /** Source */
  source: string;
  /** Target */
  target: string;
  /** Type */
  type: 'inheritance' | 'composition' | 'aggregation' | 'dependency' | 'association';
}

/**
 * Pattern detector configuration
 */
export interface PatternDetectorConfig {
  /** Minimum confidence for detection */
  minConfidence: number;
  /** Categories to detect */
  categories: PatternCategory[];
  /** Enable suggestions */
  enableSuggestions: boolean;
  /** Custom patterns */
  customPatterns: DesignPattern[];
}

/**
 * Default configuration
 */
export const DEFAULT_DETECTOR_CONFIG: PatternDetectorConfig = {
  minConfidence: 0.6,
  categories: ['creational', 'structural', 'behavioral', 'architectural'],
  enableSuggestions: true,
  customPatterns: [],
};

/**
 * Built-in design patterns
 */
export const DESIGN_PATTERNS: DesignPattern[] = [
  // Creational Patterns
  {
    id: 'singleton',
    name: 'Singleton',
    category: 'creational',
    description: 'Ensure a class has only one instance and provide global access',
    intent: 'Control object creation, limiting to a single instance',
    applicability: [
      'Exactly one instance of a class is needed',
      'Global access point is required',
    ],
    participants: [
      { name: 'Singleton', description: 'Class with private constructor', optional: false },
    ],
    indicators: [
      { type: 'naming', pattern: 'getInstance|instance|shared', weight: 0.3 },
      { type: 'structure', pattern: 'private constructor', weight: 0.4 },
      { type: 'structure', pattern: 'static instance', weight: 0.3 },
    ],
    relatedPatterns: ['factory-method', 'abstract-factory'],
  },
  {
    id: 'factory-method',
    name: 'Factory Method',
    category: 'creational',
    description: 'Define interface for creating objects, let subclasses decide',
    intent: 'Delegate instantiation to subclasses',
    applicability: [
      'Class cannot anticipate class of objects to create',
      'Subclasses should specify objects created',
    ],
    participants: [
      { name: 'Creator', description: 'Abstract class with factory method', optional: false },
      { name: 'ConcreteCreator', description: 'Implements factory method', optional: false },
      { name: 'Product', description: 'Interface for created objects', optional: false },
    ],
    indicators: [
      { type: 'naming', pattern: 'create|make|build|factory', weight: 0.3 },
      { type: 'method', pattern: 'returns new.*instance', weight: 0.4 },
      { type: 'structure', pattern: 'abstract.*create', weight: 0.3 },
    ],
    relatedPatterns: ['abstract-factory', 'builder', 'prototype'],
  },
  {
    id: 'builder',
    name: 'Builder',
    category: 'creational',
    description: 'Separate construction of complex object from representation',
    intent: 'Step-by-step construction of complex objects',
    applicability: [
      'Complex object construction algorithm',
      'Different representations needed',
    ],
    participants: [
      { name: 'Builder', description: 'Interface for building parts', optional: false },
      { name: 'ConcreteBuilder', description: 'Constructs and assembles', optional: false },
      { name: 'Director', description: 'Constructs using Builder', optional: true },
      { name: 'Product', description: 'Complex object built', optional: false },
    ],
    indicators: [
      { type: 'naming', pattern: 'builder|build|with', weight: 0.3 },
      { type: 'method', pattern: 'set.*return this|with.*return this', weight: 0.4 },
      { type: 'method', pattern: 'build\\(\\)', weight: 0.3 },
    ],
    relatedPatterns: ['abstract-factory', 'factory-method'],
  },

  // Structural Patterns
  {
    id: 'adapter',
    name: 'Adapter',
    category: 'structural',
    description: 'Convert interface of a class into another interface',
    intent: 'Allow incompatible interfaces to work together',
    applicability: [
      'Want to use existing class with incompatible interface',
      'Create reusable class with unrelated classes',
    ],
    participants: [
      { name: 'Target', description: 'Interface client expects', optional: false },
      { name: 'Adaptee', description: 'Existing interface to adapt', optional: false },
      { name: 'Adapter', description: 'Adapts Adaptee to Target', optional: false },
    ],
    indicators: [
      { type: 'naming', pattern: 'adapter|wrapper', weight: 0.3 },
      { type: 'structure', pattern: 'implements.*wraps', weight: 0.4 },
      { type: 'relation', pattern: 'composition with different interface', weight: 0.3 },
    ],
    relatedPatterns: ['bridge', 'decorator', 'proxy'],
  },
  {
    id: 'decorator',
    name: 'Decorator',
    category: 'structural',
    description: 'Attach additional responsibilities dynamically',
    intent: 'Flexible alternative to subclassing for extending functionality',
    applicability: [
      'Add responsibilities transparently',
      'Extend by subclassing is impractical',
    ],
    participants: [
      { name: 'Component', description: 'Interface for objects', optional: false },
      { name: 'ConcreteComponent', description: 'Object to decorate', optional: false },
      { name: 'Decorator', description: 'Wraps Component', optional: false },
    ],
    indicators: [
      { type: 'naming', pattern: 'decorator|wrapper', weight: 0.3 },
      { type: 'structure', pattern: 'implements.*has component', weight: 0.4 },
      { type: 'method', pattern: 'delegates to wrapped', weight: 0.3 },
    ],
    relatedPatterns: ['adapter', 'composite', 'strategy'],
  },
  {
    id: 'facade',
    name: 'Facade',
    category: 'structural',
    description: 'Provide unified interface to subsystem interfaces',
    intent: 'Simplify complex subsystem usage',
    applicability: [
      'Simple interface to complex subsystem needed',
      'Decouple subsystem from clients',
    ],
    participants: [
      { name: 'Facade', description: 'Knows subsystem classes', optional: false },
      { name: 'Subsystem', description: 'Implement functionality', optional: false },
    ],
    indicators: [
      { type: 'naming', pattern: 'facade|service|manager', weight: 0.2 },
      { type: 'structure', pattern: 'aggregates multiple classes', weight: 0.4 },
      { type: 'method', pattern: 'simplifies complex operations', weight: 0.4 },
    ],
    relatedPatterns: ['abstract-factory', 'mediator', 'singleton'],
  },

  // Behavioral Patterns
  {
    id: 'observer',
    name: 'Observer',
    category: 'behavioral',
    description: 'Define one-to-many dependency between objects',
    intent: 'Notify multiple objects of state changes',
    applicability: [
      'Abstraction has two aspects, one dependent on other',
      'Change to one object requires changing others',
    ],
    participants: [
      { name: 'Subject', description: 'Knows observers, sends notifications', optional: false },
      { name: 'Observer', description: 'Interface for update notification', optional: false },
      { name: 'ConcreteObserver', description: 'Maintains reference to Subject', optional: false },
    ],
    indicators: [
      { type: 'naming', pattern: 'observer|listener|subscriber|handler', weight: 0.3 },
      { type: 'method', pattern: 'subscribe|attach|addListener|on', weight: 0.35 },
      { type: 'method', pattern: 'notify|emit|publish|dispatch', weight: 0.35 },
    ],
    relatedPatterns: ['mediator', 'singleton'],
  },
  {
    id: 'strategy',
    name: 'Strategy',
    category: 'behavioral',
    description: 'Define family of algorithms, make them interchangeable',
    intent: 'Let algorithm vary independently from clients',
    applicability: [
      'Many related classes differ only in behavior',
      'Need different variants of an algorithm',
    ],
    participants: [
      { name: 'Strategy', description: 'Interface for algorithm', optional: false },
      { name: 'ConcreteStrategy', description: 'Implements algorithm', optional: false },
      { name: 'Context', description: 'Uses Strategy', optional: false },
    ],
    indicators: [
      { type: 'naming', pattern: 'strategy|policy|algorithm', weight: 0.3 },
      { type: 'structure', pattern: 'interface with multiple implementations', weight: 0.4 },
      { type: 'structure', pattern: 'context with strategy reference', weight: 0.3 },
    ],
    relatedPatterns: ['flyweight', 'state', 'template-method'],
  },
  {
    id: 'command',
    name: 'Command',
    category: 'behavioral',
    description: 'Encapsulate request as an object',
    intent: 'Parameterize objects with operations',
    applicability: [
      'Parameterize objects with actions',
      'Support undo operations',
      'Support logging changes',
    ],
    participants: [
      { name: 'Command', description: 'Interface for executing', optional: false },
      { name: 'ConcreteCommand', description: 'Binds receiver with action', optional: false },
      { name: 'Invoker', description: 'Asks command to execute', optional: false },
      { name: 'Receiver', description: 'Knows how to perform', optional: false },
    ],
    indicators: [
      { type: 'naming', pattern: 'command|action|request|handler', weight: 0.3 },
      { type: 'method', pattern: 'execute|run|handle|perform', weight: 0.35 },
      { type: 'method', pattern: 'undo|rollback|revert', weight: 0.35 },
    ],
    relatedPatterns: ['composite', 'memento', 'prototype'],
  },

  // Architectural Patterns
  {
    id: 'mvc',
    name: 'Model-View-Controller',
    category: 'architectural',
    description: 'Separate application into Model, View, Controller',
    intent: 'Separate concerns in UI applications',
    applicability: [
      'UI applications',
      'Need to support multiple views',
    ],
    participants: [
      { name: 'Model', description: 'Application data and logic', optional: false },
      { name: 'View', description: 'Visual representation', optional: false },
      { name: 'Controller', description: 'Handles user input', optional: false },
    ],
    indicators: [
      { type: 'naming', pattern: 'model|view|controller', weight: 0.4 },
      { type: 'structure', pattern: 'separate model/view/controller files', weight: 0.4 },
      { type: 'relation', pattern: 'view observes model', weight: 0.2 },
    ],
    relatedPatterns: ['observer', 'strategy', 'mvvm'],
  },
  {
    id: 'repository',
    name: 'Repository',
    category: 'architectural',
    description: 'Mediate between domain and data mapping layers',
    intent: 'Abstract data access with collection-like interface',
    applicability: [
      'Complex domain model',
      'Need to test data access independently',
    ],
    participants: [
      { name: 'Repository', description: 'Interface for data access', optional: false },
      { name: 'ConcreteRepository', description: 'Implements data access', optional: false },
    ],
    indicators: [
      { type: 'naming', pattern: 'repository|repo|store|dao', weight: 0.3 },
      { type: 'method', pattern: 'find|get|save|delete|update', weight: 0.4 },
      { type: 'structure', pattern: 'abstracts data source', weight: 0.3 },
    ],
    relatedPatterns: ['unit-of-work', 'data-mapper'],
  },
];

/**
 * Design Pattern Detector
 */
export class PatternDetector {
  private config: PatternDetectorConfig;
  private patterns: DesignPattern[];

  constructor(config?: Partial<PatternDetectorConfig>) {
    this.config = { ...DEFAULT_DETECTOR_CONFIG, ...config };
    this.patterns = [
      ...DESIGN_PATTERNS.filter((p) => this.config.categories.includes(p.category)),
      ...this.config.customPatterns,
    ];
  }

  /**
   * Detect patterns in code structure
   */
  detectPatterns(structure: CodeStructure): PatternDetectionResult[] {
    const results: PatternDetectionResult[] = [];

    for (const pattern of this.patterns) {
      const detection = this.detectPattern(pattern, structure);
      if (detection && detection.confidence >= this.config.minConfidence) {
        results.push(detection);
      }
    }

    // Sort by confidence
    results.sort((a, b) => b.confidence - a.confidence);

    return results;
  }

  /**
   * Detect patterns in source code text
   */
  detectInCode(code: string, fileName?: string): PatternDetectionResult[] {
    const structure = this.parseCodeStructure(code);
    const results = this.detectPatterns(structure);

    // Add file info
    if (fileName) {
      for (const result of results) {
        result.location.file = fileName;
      }
    }

    return results;
  }

  /**
   * Suggest patterns for a problem context
   */
  suggestPatterns(context: {
    problem: string;
    constraints?: string[];
    existing?: string[];
  }): PatternSuggestion[] {
    if (!this.config.enableSuggestions) {
      return [];
    }

    const suggestions: PatternSuggestion[] = [];
    const problemLower = context.problem.toLowerCase();

    for (const pattern of this.patterns) {
      let applicability = 0;
      const reasons: string[] = [];

      // Check intent match
      if (this.textMatch(problemLower, pattern.intent.toLowerCase())) {
        applicability += 0.3;
        reasons.push(`Intent matches: ${pattern.intent}`);
      }

      // Check applicability match
      for (const app of pattern.applicability) {
        if (this.textMatch(problemLower, app.toLowerCase())) {
          applicability += 0.2;
          reasons.push(`Applicable: ${app}`);
        }
      }

      // Skip if already using this pattern
      if (context.existing?.includes(pattern.id)) {
        continue;
      }

      if (applicability > 0.2) {
        suggestions.push({
          pattern,
          reason: reasons.join('; '),
          applicability,
          benefits: pattern.applicability,
          implementationHints: this.generateHints(pattern),
        });
      }
    }

    // Sort by applicability
    suggestions.sort((a, b) => b.applicability - a.applicability);

    return suggestions.slice(0, 5);
  }

  /**
   * Detect a specific pattern
   */
  private detectPattern(
    pattern: DesignPattern,
    structure: CodeStructure
  ): PatternDetectionResult | null {
    const matchedIndicators: MatchedIndicator[] = [];
    let totalWeight = 0;
    let matchedWeight = 0;

    for (const indicator of pattern.indicators) {
      totalWeight += indicator.weight;
      const match = this.matchIndicator(indicator, structure);
      if (match) {
        matchedIndicators.push(match);
        matchedWeight += indicator.weight;
      }
    }

    const confidence = totalWeight > 0 ? matchedWeight / totalWeight : 0;

    if (confidence < this.config.minConfidence) {
      return null;
    }

    return {
      pattern,
      confidence,
      location: this.findLocation(structure, matchedIndicators),
      matchedIndicators,
      missingElements: this.findMissing(pattern, matchedIndicators),
      suggestions: this.generateImprovements(pattern, confidence),
    };
  }

  /**
   * Match an indicator against structure
   */
  private matchIndicator(
    indicator: PatternIndicator,
    structure: CodeStructure
  ): MatchedIndicator | null {
    const regex = new RegExp(indicator.pattern, 'i');

    switch (indicator.type) {
      case 'naming':
        for (const cls of structure.classes) {
          if (regex.test(cls.name)) {
            return { indicator, matchedText: cls.name, location: `class ${cls.name}` };
          }
          for (const method of cls.methods) {
            if (regex.test(method)) {
              return { indicator, matchedText: method, location: `${cls.name}.${method}` };
            }
          }
        }
        for (const fn of structure.functions) {
          if (regex.test(fn.name)) {
            return { indicator, matchedText: fn.name, location: `function ${fn.name}` };
          }
        }
        break;

      case 'method':
        for (const cls of structure.classes) {
          for (const method of cls.methods) {
            if (regex.test(method)) {
              return { indicator, matchedText: method, location: `${cls.name}.${method}` };
            }
          }
        }
        break;

      case 'structure':
        // Check for structural patterns
        if (indicator.pattern.includes('abstract')) {
          const abstracts = structure.classes.filter((c) => c.isAbstract);
          if (abstracts.length > 0) {
            return { indicator, matchedText: abstracts[0].name, location: `abstract ${abstracts[0].name}` };
          }
        }
        if (indicator.pattern.includes('interface')) {
          const interfaces = structure.classes.filter((c) => c.isInterface);
          if (interfaces.length > 0) {
            return { indicator, matchedText: interfaces[0].name, location: `interface ${interfaces[0].name}` };
          }
        }
        if (indicator.pattern.includes('static')) {
          for (const cls of structure.classes) {
            for (const prop of cls.properties) {
              if (prop.includes('static')) {
                return { indicator, matchedText: prop, location: `${cls.name}.${prop}` };
              }
            }
          }
        }
        break;

      case 'relation':
        for (const rel of structure.relationships) {
          if (regex.test(`${rel.type} ${rel.source} ${rel.target}`)) {
            return { indicator, matchedText: `${rel.source}->${rel.target}`, location: rel.type };
          }
        }
        break;
    }

    return null;
  }

  /**
   * Parse code into structure (simplified)
   */
  private parseCodeStructure(code: string): CodeStructure {
    const classes: ClassInfo[] = [];
    const functions: FunctionInfo[] = [];
    const relationships: RelationshipInfo[] = [];

    // Simple regex-based parsing (production would use proper AST)
    
    // Detect classes
    const classRegex = /(?:export\s+)?(?:abstract\s+)?(class|interface)\s+(\w+)(?:\s+extends\s+(\w+))?(?:\s+implements\s+([^{]+))?/g;
    let match;
    while ((match = classRegex.exec(code)) !== null) {
      const isInterface = match[1] === 'interface';
      const isAbstract = code.substring(Math.max(0, match.index - 20), match.index).includes('abstract');
      
      classes.push({
        name: match[2],
        isInterface,
        isAbstract,
        methods: this.extractMethods(code, match[2]),
        properties: this.extractProperties(code, match[2]),
        extends: match[3],
        implements: match[4] ? match[4].split(',').map((s) => s.trim()) : [],
      });

      // Add relationships
      if (match[3]) {
        relationships.push({
          source: match[2],
          target: match[3],
          type: 'inheritance',
        });
      }
    }

    // Detect standalone functions
    const funcRegex = /(?:export\s+)?(?:async\s+)?function\s+(\w+)\s*\(([^)]*)\)/g;
    while ((match = funcRegex.exec(code)) !== null) {
      functions.push({
        name: match[1],
        parameters: match[2].split(',').map((s) => s.trim()).filter(Boolean),
        isStatic: false,
      });
    }

    return { classes, functions, relationships };
  }

  /**
   * Extract methods from class
   */
  private extractMethods(code: string, className: string): string[] {
    const methods: string[] = [];
    const classStart = code.indexOf(`class ${className}`);
    if (classStart === -1) return methods;

    // Find class body
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
    const methodRegex = /(?:public|private|protected|static|async)?\s*(\w+)\s*\([^)]*\)\s*(?::\s*\w+)?\s*{/g;
    let match;
    while ((match = methodRegex.exec(classBody)) !== null) {
      if (match[1] !== 'constructor' && match[1] !== 'if' && match[1] !== 'for') {
        methods.push(match[1]);
      }
    }

    return methods;
  }

  /**
   * Extract properties from class
   */
  private extractProperties(code: string, className: string): string[] {
    const properties: string[] = [];
    const classStart = code.indexOf(`class ${className}`);
    if (classStart === -1) return properties;

    const classBody = code.substring(classStart, classStart + 1000);
    const propRegex = /(?:public|private|protected|static|readonly)?\s+(\w+)\s*(?::\s*\w+)?\s*[;=]/g;
    let match;
    while ((match = propRegex.exec(classBody)) !== null) {
      properties.push(match[1]);
    }

    return properties;
  }

  /**
   * Find location in structure
   */
  private findLocation(
    _structure: CodeStructure,
    matches: MatchedIndicator[]
  ): PatternLocation {
    const classes = new Set<string>();
    const methods = new Set<string>();

    for (const match of matches) {
      const parts = match.location.split('.');
      if (parts.length > 1) {
        classes.add(parts[0].replace('class ', ''));
        methods.add(parts[1]);
      }
    }

    return {
      className: Array.from(classes)[0],
      methods: Array.from(methods),
    };
  }

  /**
   * Find missing pattern elements
   */
  private findMissing(
    pattern: DesignPattern,
    matches: MatchedIndicator[]
  ): string[] {
    const missing: string[] = [];
    const matchedTypes = new Set(matches.map((m) => m.indicator.type));

    for (const indicator of pattern.indicators) {
      if (!matchedTypes.has(indicator.type)) {
        missing.push(`Missing ${indicator.type}: ${indicator.pattern}`);
      }
    }

    return missing;
  }

  /**
   * Generate improvement suggestions
   */
  private generateImprovements(
    pattern: DesignPattern,
    confidence: number
  ): string[] {
    const suggestions: string[] = [];

    if (confidence < 0.8) {
      suggestions.push(`Consider fully implementing ${pattern.name} pattern`);
    }

    for (const participant of pattern.participants) {
      if (!participant.optional) {
        suggestions.push(`Ensure ${participant.name} is properly defined`);
      }
    }

    return suggestions;
  }

  /**
   * Generate implementation hints
   */
  private generateHints(pattern: DesignPattern): string[] {
    const hints: string[] = [];

    for (const participant of pattern.participants) {
      hints.push(`Create ${participant.name}: ${participant.description}`);
    }

    return hints;
  }

  /**
   * Simple text matching
   */
  private textMatch(text: string, pattern: string): boolean {
    const words = pattern.split(/\s+/);
    return words.some((word) => text.includes(word) && word.length > 3);
  }

  /**
   * Get all available patterns
   */
  getPatterns(): DesignPattern[] {
    return [...this.patterns];
  }

  /**
   * Get patterns by category
   */
  getPatternsByCategory(category: PatternCategory): DesignPattern[] {
    return this.patterns.filter((p) => p.category === category);
  }
}

/**
 * Create pattern detector instance
 */
export function createPatternDetector(
  config?: Partial<PatternDetectorConfig>
): PatternDetector {
  return new PatternDetector(config);
}
