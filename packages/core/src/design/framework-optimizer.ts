/**
 * Framework Optimizer
 * 
 * Provides framework-specific optimizations and best practices
 * 
 * @packageDocumentation
 * @module design/framework-optimizer
 * 
 * @see REQ-DES-002 - Framework Optimization
 * @see Article III - Design Validation
 */

/**
 * Supported frameworks
 */
export type FrameworkType =
  | 'react'
  | 'vue'
  | 'angular'
  | 'express'
  | 'fastify'
  | 'nestjs'
  | 'nextjs'
  | 'nuxt'
  | 'svelte'
  | 'node'
  | 'generic';

/**
 * Framework info
 */
export interface FrameworkInfo {
  /** Framework ID */
  id: FrameworkType;
  /** Display name */
  name: string;
  /** Category */
  category: 'frontend' | 'backend' | 'fullstack' | 'runtime';
  /** Key patterns */
  patterns: string[];
  /** Best practices */
  bestPractices: FrameworkBestPractice[];
  /** Anti-patterns */
  antiPatterns: FrameworkAntiPattern[];
  /** Detection indicators */
  detectionPatterns: string[];
}

/**
 * Best practice
 */
export interface FrameworkBestPractice {
  /** Practice ID */
  id: string;
  /** Practice name */
  name: string;
  /** Description */
  description: string;
  /** Why it matters */
  rationale: string;
  /** Example */
  example?: string;
  /** Priority */
  priority: 'high' | 'medium' | 'low';
}

/**
 * Anti-pattern
 */
export interface FrameworkAntiPattern {
  /** Anti-pattern ID */
  id: string;
  /** Name */
  name: string;
  /** Description */
  description: string;
  /** Detection pattern */
  detection: RegExp | string;
  /** Severity */
  severity: 'high' | 'medium' | 'low';
  /** Fix suggestion */
  fix: string;
}

/**
 * Optimization suggestion
 */
export interface OptimizationSuggestion {
  /** Suggestion ID */
  id: string;
  /** Category */
  category: 'performance' | 'security' | 'maintainability' | 'scalability';
  /** Title */
  title: string;
  /** Description */
  description: string;
  /** Priority */
  priority: 'high' | 'medium' | 'low';
  /** Impact */
  impact: string;
  /** How to implement */
  implementation: string;
  /** Code example */
  codeExample?: string;
  /** Related files */
  relatedFiles?: string[];
}

/**
 * Framework analysis result
 */
export interface FrameworkAnalysisResult {
  /** Detected framework */
  framework: FrameworkInfo;
  /** Confidence */
  confidence: number;
  /** Anti-patterns found */
  antiPatternsFound: AntiPatternMatch[];
  /** Best practices missing */
  missingBestPractices: FrameworkBestPractice[];
  /** Optimization suggestions */
  suggestions: OptimizationSuggestion[];
  /** Overall score */
  score: number;
}

/**
 * Anti-pattern match
 */
export interface AntiPatternMatch {
  /** Anti-pattern */
  antiPattern: FrameworkAntiPattern;
  /** Where found */
  location: string;
  /** Matched text */
  matchedText: string;
}

/**
 * Framework definitions
 */
export const FRAMEWORKS: Record<FrameworkType, FrameworkInfo> = {
  react: {
    id: 'react',
    name: 'React',
    category: 'frontend',
    patterns: ['component', 'hooks', 'jsx', 'virtual-dom'],
    detectionPatterns: ['import.*react', 'useState|useEffect|useCallback', 'React\\.Component'],
    bestPractices: [
      {
        id: 'react-memo',
        name: 'Use React.memo for expensive components',
        description: 'Wrap expensive components with React.memo to prevent unnecessary re-renders',
        rationale: 'Improves performance by avoiding re-renders when props haven\'t changed',
        priority: 'high',
      },
      {
        id: 'react-keys',
        name: 'Use stable keys in lists',
        description: 'Use unique, stable IDs as keys instead of array indices',
        rationale: 'Prevents reconciliation issues and improves performance',
        priority: 'high',
      },
      {
        id: 'react-hooks-deps',
        name: 'Correct dependency arrays',
        description: 'Include all dependencies in useEffect, useCallback, useMemo',
        rationale: 'Prevents stale closures and unexpected behavior',
        priority: 'high',
      },
      {
        id: 'react-suspense',
        name: 'Use Suspense for code splitting',
        description: 'Implement React.lazy and Suspense for large components',
        rationale: 'Reduces initial bundle size and improves loading performance',
        priority: 'medium',
      },
    ],
    antiPatterns: [
      {
        id: 'react-inline-func',
        name: 'Inline function in render',
        description: 'Creating new function references in render causes unnecessary re-renders',
        detection: /onClick=\{\s*\(\)\s*=>/,
        severity: 'medium',
        fix: 'Use useCallback or define handler outside render',
      },
      {
        id: 'react-index-key',
        name: 'Using index as key',
        description: 'Using array index as key can cause rendering issues',
        detection: /key=\{(?:index|i|idx)\}/,
        severity: 'medium',
        fix: 'Use unique item IDs as keys',
      },
      {
        id: 'react-direct-state',
        name: 'Direct state mutation',
        description: 'Mutating state directly instead of using setState',
        detection: /this\.state\.\w+\s*=/,
        severity: 'high',
        fix: 'Use setState or useState setter function',
      },
    ],
  },
  
  vue: {
    id: 'vue',
    name: 'Vue.js',
    category: 'frontend',
    patterns: ['component', 'reactive', 'single-file-component', 'composition-api'],
    detectionPatterns: ['import.*vue', 'defineComponent', 'ref\\(|reactive\\(', '\\.vue$'],
    bestPractices: [
      {
        id: 'vue-composition',
        name: 'Use Composition API',
        description: 'Prefer Composition API for complex component logic',
        rationale: 'Better code organization and TypeScript support',
        priority: 'medium',
      },
      {
        id: 'vue-computed',
        name: 'Use computed for derived state',
        description: 'Use computed properties instead of methods for derived values',
        rationale: 'Caching improves performance for expensive calculations',
        priority: 'high',
      },
    ],
    antiPatterns: [
      {
        id: 'vue-v-if-v-for',
        name: 'v-if with v-for',
        description: 'Using v-if and v-for on the same element',
        detection: /v-for.*v-if|v-if.*v-for/,
        severity: 'high',
        fix: 'Use computed property to filter list before rendering',
      },
    ],
  },

  express: {
    id: 'express',
    name: 'Express.js',
    category: 'backend',
    patterns: ['middleware', 'routing', 'rest-api'],
    detectionPatterns: ['require.*express|import.*express', 'app\\.get|app\\.post|app\\.use'],
    bestPractices: [
      {
        id: 'express-helmet',
        name: 'Use Helmet for security',
        description: 'Add Helmet middleware for security headers',
        rationale: 'Protects against common web vulnerabilities',
        priority: 'high',
      },
      {
        id: 'express-error-handler',
        name: 'Centralized error handling',
        description: 'Implement error handling middleware',
        rationale: 'Consistent error responses and logging',
        priority: 'high',
      },
      {
        id: 'express-validation',
        name: 'Request validation',
        description: 'Validate request body, params, and query',
        rationale: 'Prevents invalid data and security issues',
        priority: 'high',
      },
    ],
    antiPatterns: [
      {
        id: 'express-sync-code',
        name: 'Synchronous blocking code',
        description: 'Using synchronous operations in routes',
        detection: /readFileSync|writeFileSync|execSync/,
        severity: 'high',
        fix: 'Use async alternatives',
      },
      {
        id: 'express-uncaught',
        name: 'Uncaught async errors',
        description: 'Async route handlers without try-catch or error middleware',
        detection: /async.*\(req.*res.*\)\s*=>\s*\{(?!.*try)/,
        severity: 'high',
        fix: 'Wrap async handlers with try-catch or use express-async-errors',
      },
    ],
  },

  nestjs: {
    id: 'nestjs',
    name: 'NestJS',
    category: 'backend',
    patterns: ['dependency-injection', 'decorator', 'module', 'controller'],
    detectionPatterns: ['@nestjs', '@Module|@Controller|@Injectable', 'NestFactory'],
    bestPractices: [
      {
        id: 'nest-dto',
        name: 'Use DTOs for validation',
        description: 'Define DTOs with class-validator decorators',
        rationale: 'Type-safe validation and documentation',
        priority: 'high',
      },
      {
        id: 'nest-guards',
        name: 'Use Guards for authorization',
        description: 'Implement Guards instead of inline auth checks',
        rationale: 'Separation of concerns and reusability',
        priority: 'high',
      },
      {
        id: 'nest-interceptors',
        name: 'Use Interceptors for cross-cutting concerns',
        description: 'Implement interceptors for logging, caching, transformation',
        rationale: 'AOP-style code organization',
        priority: 'medium',
      },
    ],
    antiPatterns: [
      {
        id: 'nest-circular-dep',
        name: 'Circular dependency',
        description: 'Modules or services depending on each other',
        detection: /forwardRef/,
        severity: 'medium',
        fix: 'Refactor to remove circular dependency or use forwardRef carefully',
      },
    ],
  },

  nextjs: {
    id: 'nextjs',
    name: 'Next.js',
    category: 'fullstack',
    patterns: ['ssr', 'ssg', 'api-routes', 'file-routing'],
    detectionPatterns: ['next\\/|from.*next', 'getServerSideProps|getStaticProps', 'pages\\/|app\\/'],
    bestPractices: [
      {
        id: 'next-image',
        name: 'Use Next Image component',
        description: 'Use next/image for optimized images',
        rationale: 'Automatic image optimization and lazy loading',
        priority: 'high',
      },
      {
        id: 'next-data-fetching',
        name: 'Choose correct data fetching',
        description: 'Use getStaticProps for static, getServerSideProps for dynamic',
        rationale: 'Optimal performance based on data requirements',
        priority: 'high',
      },
      {
        id: 'next-link',
        name: 'Use Next Link for navigation',
        description: 'Use next/link instead of anchor tags',
        rationale: 'Client-side navigation with prefetching',
        priority: 'medium',
      },
    ],
    antiPatterns: [
      {
        id: 'next-client-only',
        name: 'Client-only code in pages',
        description: 'Using browser APIs without checking environment',
        detection: /window\.|document\./,
        severity: 'medium',
        fix: 'Check typeof window !== "undefined" or use useEffect',
      },
    ],
  },

  node: {
    id: 'node',
    name: 'Node.js',
    category: 'runtime',
    patterns: ['event-loop', 'streams', 'modules'],
    detectionPatterns: ['require\\(|import\\s+', 'process\\.', 'Buffer|Stream'],
    bestPractices: [
      {
        id: 'node-async',
        name: 'Use async/await',
        description: 'Prefer async/await over callbacks',
        rationale: 'Cleaner code and better error handling',
        priority: 'high',
      },
      {
        id: 'node-streams',
        name: 'Use streams for large data',
        description: 'Process large files with streams',
        rationale: 'Memory efficiency for large data',
        priority: 'medium',
      },
      {
        id: 'node-env-vars',
        name: 'Use environment variables',
        description: 'Store configuration in environment variables',
        rationale: 'Security and deployment flexibility',
        priority: 'high',
      },
    ],
    antiPatterns: [
      {
        id: 'node-callback-hell',
        name: 'Callback hell',
        description: 'Deeply nested callbacks',
        detection: /\)\s*=>\s*\{[^}]*\)\s*=>\s*\{[^}]*\)\s*=>/,
        severity: 'medium',
        fix: 'Use async/await or Promises',
      },
      {
        id: 'node-sync-io',
        name: 'Synchronous I/O',
        description: 'Using synchronous I/O operations',
        detection: /Sync\(/,
        severity: 'high',
        fix: 'Use async versions of I/O functions',
      },
    ],
  },

  angular: {
    id: 'angular',
    name: 'Angular',
    category: 'frontend',
    patterns: ['component', 'service', 'module', 'dependency-injection'],
    detectionPatterns: ['@angular', '@Component|@Injectable|@NgModule', 'ngOnInit'],
    bestPractices: [],
    antiPatterns: [],
  },

  fastify: {
    id: 'fastify',
    name: 'Fastify',
    category: 'backend',
    patterns: ['plugin', 'schema-validation', 'hooks'],
    detectionPatterns: ['fastify', 'fastify\\.register|fastify\\.route'],
    bestPractices: [],
    antiPatterns: [],
  },

  nuxt: {
    id: 'nuxt',
    name: 'Nuxt.js',
    category: 'fullstack',
    patterns: ['ssr', 'auto-imports', 'file-routing'],
    detectionPatterns: ['nuxt', 'useNuxtApp|useFetch'],
    bestPractices: [],
    antiPatterns: [],
  },

  svelte: {
    id: 'svelte',
    name: 'Svelte',
    category: 'frontend',
    patterns: ['reactive', 'compile-time', 'stores'],
    detectionPatterns: ['\\.svelte$', '\\$:', 'svelte/store'],
    bestPractices: [],
    antiPatterns: [],
  },

  generic: {
    id: 'generic',
    name: 'Generic TypeScript/JavaScript',
    category: 'runtime',
    patterns: ['modules', 'classes', 'async'],
    detectionPatterns: [],
    bestPractices: [
      {
        id: 'gen-error-handling',
        name: 'Proper error handling',
        description: 'Use try-catch for async operations',
        rationale: 'Prevents unhandled rejections',
        priority: 'high',
      },
      {
        id: 'gen-typing',
        name: 'Use TypeScript types',
        description: 'Define interfaces and types for all data',
        rationale: 'Type safety and documentation',
        priority: 'high',
      },
    ],
    antiPatterns: [
      {
        id: 'gen-any',
        name: 'Using any type',
        description: 'Excessive use of any type',
        detection: /:\s*any\b/,
        severity: 'medium',
        fix: 'Define proper types or use unknown',
      },
    ],
  },
};

/**
 * Framework Optimizer configuration
 */
export interface FrameworkOptimizerConfig {
  /** Custom frameworks */
  customFrameworks?: FrameworkInfo[];
  /** Strict mode */
  strictMode: boolean;
  /** Minimum confidence for detection */
  detectionThreshold: number;
}

/**
 * Default configuration
 */
export const DEFAULT_OPTIMIZER_CONFIG: FrameworkOptimizerConfig = {
  strictMode: false,
  detectionThreshold: 0.6,
};

/**
 * Framework Optimizer
 */
export class FrameworkOptimizer {
  private config: FrameworkOptimizerConfig;
  private frameworks: Map<FrameworkType, FrameworkInfo>;

  constructor(config?: Partial<FrameworkOptimizerConfig>) {
    this.config = { ...DEFAULT_OPTIMIZER_CONFIG, ...config };
    this.frameworks = new Map(Object.entries(FRAMEWORKS) as Array<[FrameworkType, FrameworkInfo]>);
    
    // Add custom frameworks
    if (this.config.customFrameworks) {
      for (const fw of this.config.customFrameworks) {
        this.frameworks.set(fw.id, fw);
      }
    }
  }

  /**
   * Detect framework from code
   */
  detectFramework(code: string): { framework: FrameworkType; confidence: number } | null {
    const scores = new Map<FrameworkType, number>();

    for (const [id, info] of this.frameworks) {
      let matches = 0;
      for (const pattern of info.detectionPatterns) {
        const regex = new RegExp(pattern, 'i');
        if (regex.test(code)) {
          matches++;
        }
      }
      if (matches > 0) {
        const confidence = matches / info.detectionPatterns.length;
        scores.set(id, confidence);
      }
    }

    // Find best match
    let bestFramework: FrameworkType | null = null;
    let bestConfidence = 0;

    for (const [id, confidence] of scores) {
      if (confidence > bestConfidence) {
        bestConfidence = confidence;
        bestFramework = id;
      }
    }

    if (bestFramework && bestConfidence >= this.config.detectionThreshold) {
      return { framework: bestFramework, confidence: bestConfidence };
    }

    return null;
  }

  /**
   * Analyze code for framework-specific issues
   */
  analyze(code: string, framework?: FrameworkType): FrameworkAnalysisResult {
    // Detect framework if not provided
    let detectedFramework = framework;
    let confidence = 1.0;

    if (!detectedFramework) {
      const detection = this.detectFramework(code);
      if (detection) {
        detectedFramework = detection.framework;
        confidence = detection.confidence;
      } else {
        detectedFramework = 'generic';
        confidence = 0.5;
      }
    }

    const frameworkInfo = this.frameworks.get(detectedFramework)!;

    // Find anti-patterns
    const antiPatternsFound = this.findAntiPatterns(code, frameworkInfo);

    // Check best practices
    const missingBestPractices = this.checkBestPractices(code, frameworkInfo);

    // Generate suggestions
    const suggestions = this.generateSuggestions(
      frameworkInfo,
      antiPatternsFound,
      missingBestPractices
    );

    // Calculate score
    const score = this.calculateScore(antiPatternsFound, missingBestPractices);

    return {
      framework: frameworkInfo,
      confidence,
      antiPatternsFound,
      missingBestPractices,
      suggestions,
      score,
    };
  }

  /**
   * Find anti-patterns in code
   */
  private findAntiPatterns(
    code: string,
    framework: FrameworkInfo
  ): AntiPatternMatch[] {
    const matches: AntiPatternMatch[] = [];

    for (const antiPattern of framework.antiPatterns) {
      const regex = typeof antiPattern.detection === 'string'
        ? new RegExp(antiPattern.detection, 'gi')
        : antiPattern.detection;

      let match;
      while ((match = regex.exec(code)) !== null) {
        matches.push({
          antiPattern,
          location: `Position ${match.index}`,
          matchedText: match[0].substring(0, 50),
        });
      }
    }

    return matches;
  }

  /**
   * Check for missing best practices
   */
  private checkBestPractices(
    code: string,
    framework: FrameworkInfo
  ): FrameworkBestPractice[] {
    const missing: FrameworkBestPractice[] = [];

    // Simple heuristic checks
    for (const practice of framework.bestPractices) {
      let implemented = false;

      switch (practice.id) {
        case 'react-memo':
          implemented = /React\.memo|memo\(/.test(code);
          break;
        case 'react-suspense':
          implemented = /Suspense|React\.lazy/.test(code);
          break;
        case 'express-helmet':
          implemented = /helmet/.test(code);
          break;
        case 'express-error-handler':
          implemented = /app\.use\([^)]*err[^)]*\)/.test(code);
          break;
        case 'nest-dto':
          implemented = /@IsString|@IsNumber|class-validator/.test(code);
          break;
        case 'next-image':
          implemented = /next\/image|Image.*from.*next/.test(code);
          break;
        default:
          // Cannot determine, assume implemented
          implemented = true;
      }

      if (!implemented && practice.priority === 'high') {
        missing.push(practice);
      }
    }

    return missing;
  }

  /**
   * Generate optimization suggestions
   */
  private generateSuggestions(
    _framework: FrameworkInfo,
    antiPatterns: AntiPatternMatch[],
    missingPractices: FrameworkBestPractice[]
  ): OptimizationSuggestion[] {
    const suggestions: OptimizationSuggestion[] = [];

    // Suggestions from anti-patterns
    for (const match of antiPatterns) {
      suggestions.push({
        id: match.antiPattern.id,
        category: 'maintainability',
        title: `Fix: ${match.antiPattern.name}`,
        description: match.antiPattern.description,
        priority: match.antiPattern.severity,
        impact: 'Code quality and maintainability',
        implementation: match.antiPattern.fix,
      });
    }

    // Suggestions from missing practices
    for (const practice of missingPractices) {
      suggestions.push({
        id: practice.id,
        category: practice.id.includes('security') ? 'security' : 'performance',
        title: `Implement: ${practice.name}`,
        description: practice.description,
        priority: practice.priority,
        impact: practice.rationale,
        implementation: practice.example ?? 'See framework documentation',
      });
    }

    // Sort by priority
    suggestions.sort((a, b) => {
      const priorityOrder = { high: 0, medium: 1, low: 2 };
      return priorityOrder[a.priority] - priorityOrder[b.priority];
    });

    return suggestions;
  }

  /**
   * Calculate optimization score
   */
  private calculateScore(
    antiPatterns: AntiPatternMatch[],
    missingPractices: FrameworkBestPractice[]
  ): number {
    let score = 100;

    // Deduct for anti-patterns
    for (const match of antiPatterns) {
      const penalty = match.antiPattern.severity === 'high' ? 15
        : match.antiPattern.severity === 'medium' ? 10
        : 5;
      score -= penalty;
    }

    // Deduct for missing practices
    for (const practice of missingPractices) {
      const penalty = practice.priority === 'high' ? 10
        : practice.priority === 'medium' ? 5
        : 2;
      score -= penalty;
    }

    return Math.max(0, score);
  }

  /**
   * Get framework info
   */
  getFrameworkInfo(framework: FrameworkType): FrameworkInfo | undefined {
    return this.frameworks.get(framework);
  }

  /**
   * Get all frameworks
   */
  getAllFrameworks(): FrameworkInfo[] {
    return Array.from(this.frameworks.values());
  }

  /**
   * Get frameworks by category
   */
  getFrameworksByCategory(category: FrameworkInfo['category']): FrameworkInfo[] {
    return Array.from(this.frameworks.values())
      .filter((fw) => fw.category === category);
  }
}

/**
 * Create framework optimizer instance
 */
export function createFrameworkOptimizer(
  config?: Partial<FrameworkOptimizerConfig>
): FrameworkOptimizer {
  return new FrameworkOptimizer(config);
}
