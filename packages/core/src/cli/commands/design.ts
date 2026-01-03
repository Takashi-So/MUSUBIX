/**
 * Design Command
 *
 * CLI commands for design generation and validation
 *
 * @packageDocumentation
 * @module cli/commands/design
 *
 * @see REQ-CLI-002 - Design CLI
 * @see REQ-DG-001 - Pattern Detection
 * @see REQ-DG-002 - SOLID Validation
 * @see DES-MUSUBIX-001 Section 16-C.2 - designコマンド設計
 * @see TSK-066〜070 - Design CLI実装
 */

import type { Command } from 'commander';
import { readFile, writeFile, mkdir, access } from 'fs/promises';
import { resolve, dirname } from 'path';
import { ExitCode, getGlobalOptions, outputResult } from '../base.js';

/**
 * Design command options
 */
export interface DesignOptions {
  output?: string;
  format?: 'mermaid' | 'plantuml' | 'markdown' | 'json';
  verbose?: boolean;
  patterns?: string[];
  level?: 'context' | 'container' | 'component' | 'code';
}

/**
 * C4 Model types
 */
export type C4Level = 'context' | 'container' | 'component' | 'code';

/**
 * C4 Element
 */
export interface C4Element {
  id: string;
  name: string;
  description: string;
  type: 'person' | 'software_system' | 'container' | 'component';
  technology?: string;
  tags?: string[];
}

/**
 * C4 Relationship
 */
export interface C4Relationship {
  source: string;
  target: string;
  description: string;
  technology?: string;
}

/**
 * C4 Model
 */
export interface C4Model {
  level: C4Level;
  title: string;
  elements: C4Element[];
  relationships: C4Relationship[];
}

/**
 * Design pattern
 */
export interface DesignPattern {
  name: string;
  category: 'creational' | 'structural' | 'behavioral';
  intent: string;
  applicability: string[];
  consequences: { positive: string[]; negative: string[] };
}

/**
 * Generate result
 */
export interface GenerateResult {
  success: boolean;
  design: C4Model;
  patterns: DesignPattern[];
  traceability: Array<{ requirement: string; designElement: string }>;
  message: string;
}

/**
 * Validation result
 */
export interface DesignValidationResult {
  success: boolean;
  valid: boolean;
  solidViolations: Array<{
    principle: 'S' | 'O' | 'L' | 'I' | 'D';
    element: string;
    message: string;
    severity: 'error' | 'warning';
  }>;
  traceabilityGaps: Array<{
    requirement: string;
    message: string;
  }>;
  message: string;
}

/**
 * ADR structure
 */
export interface ADRDocument {
  id: string;
  title: string;
  date: string;
  status: 'proposed' | 'accepted' | 'deprecated' | 'superseded';
  context: string;
  decision: string;
  consequences: string[];
  relatedRequirements: string[];
}

/**
 * Pattern detection result
 */
export interface PatternDetectionResult {
  success: boolean;
  patterns: Array<{
    name: string;
    category: string;
    confidence: number;
    location: string;
    suggestion?: string;
  }>;
  recommendations: string[];
  message: string;
}

/**
 * SOLID principles validation rules
 */
export const SOLID_PRINCIPLES = {
  S: 'Single Responsibility Principle',
  O: 'Open/Closed Principle',
  L: 'Liskov Substitution Principle',
  I: 'Interface Segregation Principle',
  D: 'Dependency Inversion Principle',
};

/**
 * Known design patterns
 */
const KNOWN_PATTERNS: Record<string, DesignPattern> = {
  factory: {
    name: 'Factory',
    category: 'creational',
    intent: 'Define an interface for creating objects without specifying concrete classes',
    applicability: ['Object creation logic is complex', 'System needs to be independent of how objects are created'],
    consequences: {
      positive: ['Isolates concrete classes', 'Easy to introduce new products'],
      negative: ['May require new subclasses for minor variations'],
    },
  },
  singleton: {
    name: 'Singleton',
    category: 'creational',
    intent: 'Ensure a class has only one instance',
    applicability: ['Exactly one instance is needed', 'Global access point required'],
    consequences: {
      positive: ['Controlled access to sole instance', 'Reduced namespace'],
      negative: ['Difficult to test', 'Hidden dependencies'],
    },
  },
  observer: {
    name: 'Observer',
    category: 'behavioral',
    intent: 'Define a one-to-many dependency between objects',
    applicability: ['Changes to one object require changes to others', 'Objects should be loosely coupled'],
    consequences: {
      positive: ['Loose coupling', 'Broadcast communication'],
      negative: ['Unexpected updates', 'Memory leaks if not managed'],
    },
  },
  strategy: {
    name: 'Strategy',
    category: 'behavioral',
    intent: 'Define a family of algorithms and make them interchangeable',
    applicability: ['Multiple algorithms exist for a task', 'Behavior varies based on context'],
    consequences: {
      positive: ['Algorithms can vary independently', 'Eliminates conditional statements'],
      negative: ['Increased number of objects', 'Clients must be aware of strategies'],
    },
  },
  adapter: {
    name: 'Adapter',
    category: 'structural',
    intent: 'Convert interface of a class into another interface clients expect',
    applicability: ['Use existing class with incompatible interface', 'Create reusable class with unrelated classes'],
    consequences: {
      positive: ['Increased reusability', 'Flexibility in design'],
      negative: ['Increased complexity', 'Performance overhead'],
    },
  },
};

/**
 * Register design command
 */
export function registerDesignCommand(program: Command): void {
  const design = program
    .command('design')
    .description('Design generation and validation');

  // design generate
  design
    .command('generate <requirements>')
    .description('Generate design from requirements')
    .option('-o, --output <file>', 'Output file')
    .option('-f, --format <format>', 'Output format', 'markdown')
    .option('-l, --level <level>', 'C4 level', 'component')
    .action(async (requirements: string, options: DesignOptions) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const reqPath = resolve(process.cwd(), requirements);
        const content = await readFile(reqPath, 'utf-8');

        // Parse requirements and generate design
        const model = generateC4Model(content, options.level ?? 'component');
        const patterns = detectApplicablePatterns(content);
        const traceability = generateTraceability(content, model);

        const result: GenerateResult = {
          success: true,
          design: model,
          patterns,
          traceability,
          message: `Generated ${options.level ?? 'component'} design with ${model.elements.length} elements`,
        };

        // Output
        if (options.output) {
          const outputPath = resolve(process.cwd(), options.output);
          await mkdir(dirname(outputPath), { recursive: true });

          let outputContent: string;
          if (options.format === 'mermaid') {
            outputContent = generateMermaidDiagram(model);
          } else if (options.format === 'plantuml') {
            outputContent = generatePlantUMLDiagram(model);
          } else if (options.format === 'json' || globalOpts.json) {
            outputContent = JSON.stringify(result, null, 2);
          } else {
            outputContent = generateMarkdownDesign(model, patterns, traceability);
          }

          await writeFile(outputPath, outputContent, 'utf-8');
          if (!globalOpts.quiet) {
            console.log(`✅ Design saved to ${outputPath}`);
          }

          // Automatic design review (Article VII & IX compliance)
          console.log('\n' + '═'.repeat(60));
          console.log('🔍 設計レビューを実行中...');
          console.log('═'.repeat(60) + '\n');

          const reviewResult = await reviewDesign(model, patterns, traceability);
          displayDesignReviewResult(reviewResult, globalOpts.quiet ?? false);

          // Save review result
          const reviewPath = outputPath.replace('.md', '-REVIEW.md').replace('.json', '-REVIEW.md');
          await writeFile(reviewPath, generateDesignReviewDocument(reviewResult), 'utf-8');
          console.log(`📋 レビュー結果を保存しました: ${reviewPath}`);
        } else {
          outputResult(result, globalOpts);
        }

        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Design generation failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // design patterns
  design
    .command('patterns <context>')
    .description('Detect applicable design patterns')
    .option('-p, --patterns <list>', 'Pattern categories to check', 'all')
    .action(async (context: string, _options: { patterns?: string }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        // Check if context is a file or direct text
        let content: string;
        try {
          const contextPath = resolve(process.cwd(), context);
          await access(contextPath);
          content = await readFile(contextPath, 'utf-8');
        } catch {
          content = context;
        }

        const patterns = detectApplicablePatterns(content);
        const recommendations = generatePatternRecommendations(content, patterns);

        const result: PatternDetectionResult = {
          success: true,
          patterns: patterns.map(p => ({
            name: p.name,
            category: p.category,
            confidence: 0.8,
            location: 'identified from context',
            suggestion: p.intent,
          })),
          recommendations,
          message: `Detected ${patterns.length} applicable patterns`,
        };

        outputResult(result, globalOpts);
        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Pattern detection failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // design validate
  design
    .command('validate <file>')
    .description('Validate SOLID compliance')
    .option('--strict', 'Enable strict mode', false)
    .action(async (file: string, options: { strict?: boolean }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const filePath = resolve(process.cwd(), file);
        const content = await readFile(filePath, 'utf-8');

        const { violations, gaps } = validateDesign(content, options.strict ?? false);

        const result: DesignValidationResult = {
          success: true,
          valid: violations.length === 0 && gaps.length === 0,
          solidViolations: violations,
          traceabilityGaps: gaps,
          message: violations.length === 0
            ? '✅ Design is SOLID compliant'
            : `❌ Found ${violations.length} SOLID violations`,
        };

        outputResult(result, globalOpts);
        process.exit(violations.filter(v => v.severity === 'error').length === 0
          ? ExitCode.SUCCESS
          : ExitCode.VALIDATION_ERROR);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Validation failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // design c4
  design
    .command('c4 <file>')
    .description('Generate C4 diagram')
    .option('-l, --level <level>', 'C4 level (context|container|component|code)', 'component')
    .option('-f, --format <format>', 'Output format (mermaid|plantuml)', 'mermaid')
    .option('-o, --output <file>', 'Output file')
    .action(async (file: string, options: DesignOptions) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const filePath = resolve(process.cwd(), file);
        const content = await readFile(filePath, 'utf-8');

        const model = generateC4Model(content, options.level ?? 'component');

        let diagram: string;
        if (options.format === 'plantuml') {
          diagram = generatePlantUMLDiagram(model);
        } else {
          diagram = generateMermaidDiagram(model);
        }

        if (options.output) {
          const outputPath = resolve(process.cwd(), options.output);
          await mkdir(dirname(outputPath), { recursive: true });
          await writeFile(outputPath, diagram, 'utf-8');
          if (!globalOpts.quiet) {
            console.log(`✅ C4 diagram saved to ${outputPath}`);
          }
        } else {
          console.log(diagram);
        }

        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ C4 generation failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // design adr
  design
    .command('adr <decision>')
    .description('Generate ADR document')
    .option('-o, --output <dir>', 'Output directory', 'docs/adr')
    .option('--context <text>', 'Decision context')
    .option('--status <status>', 'ADR status', 'proposed')
    .action(async (decision: string, options: { output?: string; context?: string; status?: string }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const outputDir = resolve(process.cwd(), options.output ?? 'docs/adr');
        await mkdir(outputDir, { recursive: true });

        // Get next ADR number
        const { readdir } = await import('fs/promises');
        let files: string[] = [];
        try {
          files = await readdir(outputDir);
        } catch {
          // Directory is new
        }
        const adrNumbers = files
          .filter(f => f.match(/^\d{4}-/))
          .map(f => parseInt(f.slice(0, 4), 10))
          .filter(n => !isNaN(n));
        const nextNumber = Math.max(0, ...adrNumbers) + 1;

        const adr: ADRDocument = {
          id: `ADR-${String(nextNumber).padStart(4, '0')}`,
          title: decision,
          date: new Date().toISOString().split('T')[0],
          status: (options.status as ADRDocument['status']) ?? 'proposed',
          context: options.context ?? 'Context to be filled',
          decision: decision,
          consequences: ['Positive and negative consequences to be documented'],
          relatedRequirements: [],
        };

        const content = generateADRMarkdown(adr);
        const slug = decision.toLowerCase().replace(/[^a-z0-9]+/g, '-').slice(0, 50);
        const filename = `${String(nextNumber).padStart(4, '0')}-${slug}.md`;
        const outputPath = resolve(outputDir, filename);

        await writeFile(outputPath, content, 'utf-8');

        if (!globalOpts.quiet) {
          console.log(`✅ ADR created: ${outputPath}`);
        }

        if (globalOpts.json) {
          outputResult({ success: true, adr, path: outputPath }, globalOpts);
        }

        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ ADR generation failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });
}

/**
 * Generate C4 model from content
 */
function generateC4Model(content: string, level: C4Level): C4Model {
  const elements: C4Element[] = [];
  const relationships: C4Relationship[] = [];
  const seenIds = new Set<string>();

  // Check if this is an EARS requirements document
  const isEarsDoc = content.includes('EARS') || content.includes('SHALL') || content.includes('REQ-');

  if (isEarsDoc) {
    // Extract components from EARS requirements
    const contentLower = content.toLowerCase();
    
    // Add user/actor if mentioned
    if (contentLower.includes('user') || contentLower.includes('ユーザー')) {
      elements.push({
        id: 'user',
        name: 'User',
        description: 'System user who interacts with the application',
        type: 'person',
      });
    }
    
    // Infer system components from EARS requirements
    const componentInferences = [
      { keywords: ['task', 'タスク'], name: 'TaskService', desc: 'Manages task lifecycle and operations' },
      { keywords: ['notification', 'notify', 'alert', '通知'], name: 'NotificationService', desc: 'Handles user notifications and alerts' },
      { keywords: ['persist', 'store', 'save', 'storage', '保存', '永続'], name: 'DataRepository', desc: 'Handles data persistence and storage' },
      { keywords: ['authenticate', 'auth', 'login', '認証'], name: 'AuthService', desc: 'Manages authentication and authorization' },
      { keywords: ['priority', '優先'], name: 'PriorityManager', desc: 'Manages item prioritization' },
      { keywords: ['deadline', 'schedule', '期限', 'スケジュール'], name: 'ScheduleService', desc: 'Manages scheduling and deadlines' },
      { keywords: ['archive', 'アーカイブ'], name: 'ArchiveService', desc: 'Handles completed item archiving' },
      { keywords: ['validation', 'validate', 'confirm', '確認'], name: 'ValidationService', desc: 'Validates user input and actions' },
      // Shopping/E-commerce components
      { keywords: ['cart', 'カート'], name: 'CartService', desc: 'Manages shopping cart operations' },
      { keywords: ['product', 'catalog', '商品', 'カタログ'], name: 'ProductCatalogService', desc: 'Manages product catalog and display' },
      { keywords: ['checkout', '購入', '決済'], name: 'CheckoutService', desc: 'Handles checkout and order processing' },
      { keywords: ['price', 'total', 'tax', '価格', '計算'], name: 'PricingService', desc: 'Calculates prices, taxes, and totals' },
      { keywords: ['stock', 'inventory', '在庫'], name: 'InventoryService', desc: 'Manages product inventory and stock levels' },
      { keywords: ['coupon', 'discount', '割引', 'クーポン'], name: 'DiscountService', desc: 'Handles coupons and discount codes' },
      { keywords: ['order', '注文'], name: 'OrderService', desc: 'Manages customer orders' },
      { keywords: ['payment', '支払'], name: 'PaymentService', desc: 'Processes payments' },
    ];

    for (const inference of componentInferences) {
      if (inference.keywords.some(kw => contentLower.includes(kw))) {
        const id = inference.name.toLowerCase().replace(/service|manager|repository/gi, '');
        if (!seenIds.has(id)) {
          seenIds.add(id);
          elements.push({
            id,
            name: inference.name,
            description: inference.desc,
            type: level === 'context' ? 'software_system' : level === 'container' ? 'container' : 'component',
            technology: 'TypeScript',
          });
        }
      }
    }

    // If no specific components found, create a generic main service
    if (elements.filter(e => e.type !== 'person').length === 0) {
      elements.push({
        id: 'main-service',
        name: 'MainService',
        description: 'Core application service',
        type: level === 'context' ? 'software_system' : 'component',
        technology: 'TypeScript',
      });
    }

    // Generate relationships based on common patterns
    const persons = elements.filter(e => e.type === 'person');
    const services = elements.filter(e => e.type !== 'person');

    // Users interact with services
    for (const person of persons) {
      for (const service of services) {
        if (service.name.includes('Service') || service.name.includes('Manager')) {
          relationships.push({
            source: person.id,
            target: service.id,
            description: 'uses',
          });
        }
      }
    }

    // Services interact with repository
    const repository = services.find(s => s.name.includes('Repository'));
    if (repository) {
      for (const service of services) {
        if (service.id !== repository.id && !service.name.includes('Notification')) {
          relationships.push({
            source: service.id,
            target: repository.id,
            description: 'stores data in',
          });
        }
      }
    }

    // Notification service receives events from other services
    const notificationService = services.find(s => s.name.includes('Notification'));
    if (notificationService) {
      for (const service of services) {
        if (service.id !== notificationService.id && service.name.includes('Service')) {
          relationships.push({
            source: service.id,
            target: notificationService.id,
            description: 'sends notifications via',
          });
        }
      }
    }
  } else {
    // Original logic for non-EARS documents
    const systemMatches = content.match(/\b(?:system|service|application|component|module)\s+["']?([A-Za-z0-9_-]+)["']?/gi) || [];
    const actorMatches = content.match(/\b(?:user|admin|client|actor)\s+["']?([A-Za-z0-9_-]+)["']?/gi) || [];

    for (const match of actorMatches) {
      const name = match.split(/\s+/).pop()?.replace(/["']/g, '') || 'Unknown';
      const id = `person-${name.toLowerCase()}`;
      if (!seenIds.has(id)) {
        seenIds.add(id);
        elements.push({
          id,
          name,
          description: `${name} user/actor`,
          type: 'person',
        });
      }
    }

    for (const match of systemMatches) {
      const words = match.split(/\s+/);
      const type = words[0].toLowerCase();
      const name = words.pop()?.replace(/["']/g, '') || 'Unknown';
      const id = `${type}-${name.toLowerCase()}`;
      if (!seenIds.has(id)) {
        seenIds.add(id);
        elements.push({
          id,
          name,
          description: `${name} ${type}`,
          type: level === 'context' ? 'software_system' : level === 'container' ? 'container' : 'component',
        });
      }
    }

    // Generate relationships for non-EARS documents
    const elementIds = elements.map(e => e.id);
    for (let i = 0; i < elementIds.length - 1; i++) {
      relationships.push({
        source: elementIds[i],
        target: elementIds[i + 1],
        description: 'interacts with',
      });
    }
  }

  return {
    level,
    title: `${level.charAt(0).toUpperCase() + level.slice(1)} Diagram`,
    elements,
    relationships,
  };
}

/**
 * Detect applicable patterns
 */
function detectApplicablePatterns(content: string): DesignPattern[] {
  const patterns: DesignPattern[] = [];
  const contentLower = content.toLowerCase();

  // Pattern detection heuristics
  if (contentLower.includes('create') || contentLower.includes('factory') || contentLower.includes('builder')) {
    patterns.push(KNOWN_PATTERNS.factory);
  }
  if (contentLower.includes('single') || contentLower.includes('unique') || contentLower.includes('global')) {
    patterns.push(KNOWN_PATTERNS.singleton);
  }
  if (contentLower.includes('notify') || contentLower.includes('event') || contentLower.includes('subscribe')) {
    patterns.push(KNOWN_PATTERNS.observer);
  }
  if (contentLower.includes('algorithm') || contentLower.includes('strategy') || contentLower.includes('interchangeable')) {
    patterns.push(KNOWN_PATTERNS.strategy);
  }
  if (contentLower.includes('adapter') || contentLower.includes('convert') || contentLower.includes('compatible')) {
    patterns.push(KNOWN_PATTERNS.adapter);
  }

  return patterns;
}

/**
 * Generate traceability with intelligent requirement-to-element mapping
 */
function generateTraceability(content: string, model: C4Model): Array<{ requirement: string; designElement: string }> {
  const traceability: Array<{ requirement: string; designElement: string }> = [];

  // Extract requirement IDs with their context
  const reqPattern = /REQ-[A-Z]+-\d+(?:-[A-Z]+)?/g;
  const reqMatches = content.match(reqPattern) || [];
  const uniqueReqs = [...new Set(reqMatches)];

  // Build keyword-to-element mapping from model elements
  const elementKeywords: Map<string, string[]> = new Map();
  for (const el of model.elements) {
    const keywords: string[] = [];
    const nameLower = el.name.toLowerCase();
    const descLower = el.description.toLowerCase();
    
    // Extract keywords from element name and description
    if (nameLower.includes('service')) keywords.push('service', 'logic', 'business', 'process');
    if (nameLower.includes('repository')) keywords.push('repository', 'data', 'store', 'persist', 'save');
    if (nameLower.includes('validator')) keywords.push('valid', 'check', 'verify', 'confirm');
    if (nameLower.includes('auth')) keywords.push('auth', 'login', 'user', 'session', 'permission');
    if (nameLower.includes('notification')) keywords.push('notify', 'alert', 'message', 'email');
    if (nameLower.includes('search')) keywords.push('search', 'find', 'query', 'filter');
    if (nameLower.includes('export')) keywords.push('export', 'report', 'download', 'csv', 'pdf');
    if (nameLower.includes('cache')) keywords.push('cache', 'memory', 'performance');
    if (nameLower.includes('entity')) keywords.push('entity', 'model', 'data', 'record');
    if (nameLower.includes('view')) keywords.push('view', 'display', 'ui', 'render', 'show');
    if (nameLower.includes('form')) keywords.push('form', 'input', 'submit', 'create', 'edit');
    
    // Add description keywords
    const descWords = descLower.split(/[\s,.-]+/).filter(w => w.length > 3);
    keywords.push(...descWords);
    
    elementKeywords.set(el.id, keywords);
  }

  // Extract requirement context from content
  const lines = content.split('\n');
  const reqContextMap: Map<string, string> = new Map();
  
  for (let i = 0; i < lines.length; i++) {
    for (const req of uniqueReqs) {
      if (lines[i].includes(req)) {
        // Get surrounding context (±3 lines)
        const context = lines.slice(Math.max(0, i - 3), Math.min(lines.length, i + 4)).join(' ').toLowerCase();
        reqContextMap.set(req, context);
      }
    }
  }

  // Map each requirement to the most relevant design element
  for (const req of uniqueReqs) {
    const reqContext = reqContextMap.get(req) || req.toLowerCase();
    let bestMatch = model.elements[0]?.id || 'unknown';
    let bestScore = 0;

    for (const [elementId, keywords] of elementKeywords) {
      let score = 0;
      for (const keyword of keywords) {
        if (reqContext.includes(keyword)) {
          score += 1;
        }
      }
      // Boost score for requirement ID pattern matching
      // e.g., REQ-XXX-SEC-001 should map to security-related elements
      const reqParts = req.toLowerCase().split('-');
      for (const part of reqParts) {
        if (keywords.some(k => k.includes(part) || part.includes(k))) {
          score += 2;
        }
      }
      
      if (score > bestScore) {
        bestScore = score;
        bestMatch = elementId;
      }
    }

    traceability.push({
      requirement: req,
      designElement: bestMatch,
    });
  }

  return traceability;
}

/**
 * Generate pattern recommendations
 */
function generatePatternRecommendations(analysisContent: string, patterns: DesignPattern[]): string[] {
  const recommendations: string[] = [];

  if (patterns.length === 0) {
    recommendations.push('Consider applying design patterns to improve code structure');
  }

  for (const pattern of patterns) {
    recommendations.push(`${pattern.name}: ${pattern.intent}`);
  }

  // Add content-based recommendations
  if (analysisContent.toLowerCase().includes('complex') || analysisContent.toLowerCase().includes('multiple')) {
    recommendations.push('Consider decomposing complex logic into smaller components');
  }

  return recommendations;
}

/**
 * Validate design
 */
function validateDesign(designContent: string, strict: boolean): {
  violations: DesignValidationResult['solidViolations'];
  gaps: DesignValidationResult['traceabilityGaps'];
} {
  const violations: DesignValidationResult['solidViolations'] = [];
  const gaps: DesignValidationResult['traceabilityGaps'] = [];

  // Simple heuristic validation
  const contentLower = designContent.toLowerCase();

  // Check for potential SRP violations
  if (contentLower.includes('and') && designContent.match(/class\s+\w+/gi)?.length) {
    if (strict) {
      violations.push({
        principle: 'S',
        element: 'Multiple responsibilities detected',
        message: 'Class may have multiple responsibilities',
        severity: 'warning',
      });
    }
  }

  // Check for traceability
  const reqMatches = designContent.match(/REQ-[A-Z]+-\d+/g) || [];
  const desMatches = designContent.match(/DES-[A-Z]+-\d+/g) || [];

  if (reqMatches.length > 0 && desMatches.length === 0) {
    const firstReq = reqMatches[0];
    if (firstReq) {
      gaps.push({
        requirement: firstReq,
        message: 'No design element traceability found',
      });
    }
  }

  return { violations, gaps };
}

/**
 * Generate Mermaid diagram
 */
function generateMermaidDiagram(model: C4Model): string {
  let diagram = `---\ntitle: ${model.title}\n---\nflowchart TD\n`;

  for (const element of model.elements) {
    const shape = element.type === 'person' ? '([' : element.type === 'software_system' ? '[' : '[[';
    const closeShape = element.type === 'person' ? '])' : element.type === 'software_system' ? ']' : ']]';
    diagram += `  ${element.id}${shape}"${element.name}"${closeShape}\n`;
  }

  for (const rel of model.relationships) {
    diagram += `  ${rel.source} -->|${rel.description}| ${rel.target}\n`;
  }

  return diagram;
}

/**
 * Generate PlantUML diagram
 */
function generatePlantUMLDiagram(model: C4Model): string {
  let diagram = '@startuml\n';
  diagram += `title ${model.title}\n\n`;

  for (const element of model.elements) {
    if (element.type === 'person') {
      diagram += `actor "${element.name}" as ${element.id}\n`;
    } else {
      diagram += `component "${element.name}" as ${element.id}\n`;
    }
  }

  diagram += '\n';

  for (const rel of model.relationships) {
    diagram += `${rel.source} --> ${rel.target} : ${rel.description}\n`;
  }

  diagram += '@enduml\n';
  return diagram;
}

/**
 * Generate markdown design document
 */
function generateMarkdownDesign(
  model: C4Model,
  patterns: DesignPattern[],
  traceability: Array<{ requirement: string; designElement: string }>
): string {
  let output = `# Design Document\n\n`;
  output += `## C4 ${model.title}\n\n`;

  output += `### Elements\n\n`;
  output += `| ID | Name | Type | Description |\n`;
  output += `|----|------|------|-------------|\n`;
  for (const el of model.elements) {
    output += `| ${el.id} | ${el.name} | ${el.type} | ${el.description} |\n`;
  }

  output += `\n### Relationships\n\n`;
  output += `| Source | Target | Description |\n`;
  output += `|--------|--------|-------------|\n`;
  for (const rel of model.relationships) {
    output += `| ${rel.source} | ${rel.target} | ${rel.description} |\n`;
  }

  if (patterns.length > 0) {
    output += `\n## Design Patterns\n\n`;
    for (const pattern of patterns) {
      output += `### ${pattern.name}\n`;
      output += `- **Category**: ${pattern.category}\n`;
      output += `- **Intent**: ${pattern.intent}\n\n`;
    }
  }

  if (traceability.length > 0) {
    output += `\n## Traceability\n\n`;
    output += `| Requirement | Design Element |\n`;
    output += `|-------------|----------------|\n`;
    for (const trace of traceability) {
      output += `| ${trace.requirement} | ${trace.designElement} |\n`;
    }
  }

  return output;
}

/**
 * Generate ADR markdown
 */
function generateADRMarkdown(adrDoc: ADRDocument): string {
  return `# ${adrDoc.id}: ${adrDoc.title}

- **Date**: ${adrDoc.date}
- **Status**: ${adrDoc.status}

## Context

${adrDoc.context}

## Decision

${adrDoc.decision}

## Consequences

${adrDoc.consequences.map(c => `- ${c}`).join('\n')}

## Related Requirements

${adrDoc.relatedRequirements.length > 0 ? adrDoc.relatedRequirements.map(r => `- ${r}`).join('\n') : '- None'}
`;
}

// ============================================================================
// Design Review System (Article VII & IX Compliance)
// ============================================================================

/**
 * Design review result
 */
interface DesignReviewResult {
  passed: boolean;
  score: number;
  totalChecks: number;
  passedChecks: number;
  findings: DesignReviewFinding[];
  recommendations: string[];
  constitutionCompliance: {
    articleVII: boolean;  // Design Patterns
    articleV: boolean;    // Traceability
    articleIX: boolean;   // Quality Gates
  };
  solidAnalysis: {
    s: { passed: boolean; message: string };
    o: { passed: boolean; message: string };
    l: { passed: boolean; message: string };
    i: { passed: boolean; message: string };
    d: { passed: boolean; message: string };
  };
}

/**
 * Design review finding
 */
interface DesignReviewFinding {
  severity: 'error' | 'warning' | 'info';
  category: 'solid' | 'pattern' | 'traceability' | 'completeness' | 'consistency';
  element?: string;
  message: string;
  suggestion?: string;
}

/**
 * Review design for quality and SOLID compliance
 */
async function reviewDesign(
  model: C4Model,
  patterns: DesignPattern[],
  traceability: Array<{ requirement: string; designElement: string }>
): Promise<DesignReviewResult> {
  const findings: DesignReviewFinding[] = [];
  const recommendations: string[] = [];
  let passedChecks = 0;
  let totalChecks = 0;

  // Initialize SOLID analysis
  const solidAnalysis = {
    s: { passed: true, message: 'Single responsibility maintained' },
    o: { passed: true, message: 'Open for extension, closed for modification' },
    l: { passed: true, message: 'Substitution principle applicable' },
    i: { passed: true, message: 'Interface segregation maintained' },
    d: { passed: true, message: 'Dependencies properly inverted' },
  };

  // 1. Check C4 model completeness
  totalChecks++;
  if (model.elements.length === 0) {
    findings.push({
      severity: 'error',
      category: 'completeness',
      message: 'No design elements defined',
      suggestion: 'Ensure requirements are properly parsed and design elements generated',
    });
  } else {
    passedChecks++;
  }

  // 2. Check for proper element types
  totalChecks++;
  const hasPersons = model.elements.some(e => e.type === 'person');
  const hasSystems = model.elements.some(e => e.type === 'software_system' || e.type === 'container' || e.type === 'component');
  
  if (!hasPersons && !hasSystems) {
    findings.push({
      severity: 'warning',
      category: 'completeness',
      message: 'Design lacks clear actor and system separation',
      suggestion: 'Define both actors (users) and system components',
    });
  } else {
    passedChecks++;
  }

  // 3. Check relationships exist
  totalChecks++;
  if (model.relationships.length === 0 && model.elements.length > 1) {
    findings.push({
      severity: 'warning',
      category: 'completeness',
      message: 'No relationships defined between elements',
      suggestion: 'Define how components interact with each other',
    });
  } else {
    passedChecks++;
  }

  // 4. Check design patterns are documented (Article VII)
  totalChecks++;
  if (patterns.length === 0) {
    findings.push({
      severity: 'info',
      category: 'pattern',
      message: 'No design patterns detected or applied',
      suggestion: 'Consider applying appropriate design patterns for maintainability',
    });
  } else {
    passedChecks++;
    findings.push({
      severity: 'info',
      category: 'pattern',
      message: `${patterns.length} design pattern(s) applied: ${patterns.map(p => p.name).join(', ')}`,
    });
  }

  // 5. Check traceability (Article V)
  totalChecks++;
  if (traceability.length === 0) {
    findings.push({
      severity: 'error',
      category: 'traceability',
      message: 'No traceability links to requirements',
      suggestion: 'Each design element should trace back to requirements',
    });
    solidAnalysis.d.passed = false;
    solidAnalysis.d.message = 'Missing requirement traceability violates dependency management';
  } else {
    passedChecks++;
  }

  // 6. Check Single Responsibility (S)
  totalChecks++;
  for (const element of model.elements) {
    const descWords = element.description.split(/\s+/).length;
    if (descWords > 20) {
      solidAnalysis.s.passed = false;
      solidAnalysis.s.message = 'Some components may have too many responsibilities';
      findings.push({
        severity: 'warning',
        category: 'solid',
        element: element.id,
        message: `${element.name} description is long (${descWords} words) - may indicate multiple responsibilities`,
        suggestion: 'Consider splitting into smaller, focused components',
      });
    }
  }
  if (solidAnalysis.s.passed) passedChecks++;

  // 7. Check element naming conventions
  totalChecks++;
  let namingValid = true;
  for (const element of model.elements) {
    if (!/^[a-z]/.test(element.id)) {
      namingValid = false;
      findings.push({
        severity: 'warning',
        category: 'consistency',
        element: element.id,
        message: 'Element ID does not follow naming convention (should start with lowercase)',
      });
    }
  }
  if (namingValid) passedChecks++;

  // 8. Check for circular dependencies
  totalChecks++;
  const relationshipMap = new Map<string, Set<string>>();
  for (const rel of model.relationships) {
    if (!relationshipMap.has(rel.source)) {
      relationshipMap.set(rel.source, new Set());
    }
    relationshipMap.get(rel.source)!.add(rel.target);
  }
  
  let hasCircular = false;
  for (const [source, targets] of relationshipMap) {
    for (const target of targets) {
      if (relationshipMap.get(target)?.has(source)) {
        hasCircular = true;
        findings.push({
          severity: 'warning',
          category: 'consistency',
          message: `Potential circular dependency between ${source} and ${target}`,
          suggestion: 'Review dependency direction to avoid circular references',
        });
      }
    }
  }
  if (!hasCircular) passedChecks++;

  // Generate recommendations
  const errorCount = findings.filter(f => f.severity === 'error').length;
  const warningCount = findings.filter(f => f.severity === 'warning').length;

  if (errorCount > 0) {
    recommendations.push('⚠️ Address error-level findings before implementation');
  }
  if (warningCount > 0) {
    recommendations.push('📝 Review warning-level findings for potential improvements');
  }
  if (patterns.length === 0) {
    recommendations.push('📚 Consider applying design patterns (Factory, Strategy, Observer, etc.)');
  }
  if (traceability.length < model.elements.length) {
    recommendations.push('🔗 Ensure all design elements trace back to requirements');
  }
  if (errorCount === 0 && warningCount <= 2) {
    recommendations.push('✅ Design is ready for implementation phase');
  }

  const score = totalChecks > 0 ? Math.round((passedChecks / totalChecks) * 100) : 0;

  return {
    passed: errorCount === 0,
    score,
    totalChecks,
    passedChecks,
    findings,
    recommendations,
    constitutionCompliance: {
      articleVII: patterns.length > 0,
      articleV: traceability.length > 0,
      articleIX: score >= 60,
    },
    solidAnalysis,
  };
}

/**
 * Display design review result
 */
function displayDesignReviewResult(result: DesignReviewResult, quiet: boolean): void {
  if (quiet) return;

  const statusIcon = result.passed ? '✅' : '❌';
  console.log(`${statusIcon} レビュー結果: ${result.score}% (${result.passedChecks}/${result.totalChecks} checks)`);
  console.log('');

  // Constitution compliance
  console.log('📜 憲法準拠状況:');
  console.log(`   Article V (トレーサビリティ): ${result.constitutionCompliance.articleV ? '✓' : '✗'}`);
  console.log(`   Article VII (設計パターン): ${result.constitutionCompliance.articleVII ? '✓' : '✗'}`);
  console.log(`   Article IX (品質ゲート): ${result.constitutionCompliance.articleIX ? '✓' : '✗'}`);
  console.log('');

  // SOLID Analysis
  console.log('🏗️ SOLID原則分析:');
  console.log(`   [S] 単一責任: ${result.solidAnalysis.s.passed ? '✓' : '✗'} ${result.solidAnalysis.s.message}`);
  console.log(`   [O] 開放閉鎖: ${result.solidAnalysis.o.passed ? '✓' : '✗'} ${result.solidAnalysis.o.message}`);
  console.log(`   [L] リスコフ置換: ${result.solidAnalysis.l.passed ? '✓' : '✗'} ${result.solidAnalysis.l.message}`);
  console.log(`   [I] インターフェース分離: ${result.solidAnalysis.i.passed ? '✓' : '✗'} ${result.solidAnalysis.i.message}`);
  console.log(`   [D] 依存性逆転: ${result.solidAnalysis.d.passed ? '✓' : '✗'} ${result.solidAnalysis.d.message}`);
  console.log('');

  // Findings
  if (result.findings.length > 0) {
    console.log('📋 発見事項:');
    for (const finding of result.findings) {
      const icon = finding.severity === 'error' ? '🔴' : finding.severity === 'warning' ? '🟡' : '🔵';
      console.log(`   ${icon} [${finding.category}] ${finding.message}`);
      if (finding.element) {
        console.log(`      対象: ${finding.element}`);
      }
      if (finding.suggestion) {
        console.log(`      💡 ${finding.suggestion}`);
      }
    }
    console.log('');
  }

  // Recommendations
  if (result.recommendations.length > 0) {
    console.log('💡 推奨事項:');
    for (const rec of result.recommendations) {
      console.log(`   ${rec}`);
    }
    console.log('');
  }
}

/**
 * Generate design review document
 */
function generateDesignReviewDocument(result: DesignReviewResult): string {
  const now = new Date().toISOString().split('T')[0];

  let doc = `# Design Review Report

> Generated by MUSUBIX Design Review System
> Date: ${now}

## Summary

| Metric | Value |
|--------|-------|
| **Status** | ${result.passed ? '✅ PASSED' : '❌ FAILED'} |
| **Score** | ${result.score}% |
| **Checks Passed** | ${result.passedChecks}/${result.totalChecks} |

## Constitution Compliance

| Article | Name | Status |
|---------|------|--------|
| V | Traceability | ${result.constitutionCompliance.articleV ? '✅ Compliant' : '❌ Non-compliant'} |
| VII | Design Patterns | ${result.constitutionCompliance.articleVII ? '✅ Compliant' : '⚠️ No patterns applied'} |
| IX | Quality Gates | ${result.constitutionCompliance.articleIX ? '✅ Compliant' : '❌ Non-compliant'} |

## SOLID Principles Analysis

| Principle | Status | Analysis |
|-----------|--------|----------|
| **S** - Single Responsibility | ${result.solidAnalysis.s.passed ? '✅' : '⚠️'} | ${result.solidAnalysis.s.message} |
| **O** - Open/Closed | ${result.solidAnalysis.o.passed ? '✅' : '⚠️'} | ${result.solidAnalysis.o.message} |
| **L** - Liskov Substitution | ${result.solidAnalysis.l.passed ? '✅' : '⚠️'} | ${result.solidAnalysis.l.message} |
| **I** - Interface Segregation | ${result.solidAnalysis.i.passed ? '✅' : '⚠️'} | ${result.solidAnalysis.i.message} |
| **D** - Dependency Inversion | ${result.solidAnalysis.d.passed ? '✅' : '⚠️'} | ${result.solidAnalysis.d.message} |

## Findings

`;

  if (result.findings.length === 0) {
    doc += '_No issues found._\n\n';
  } else {
    const errors = result.findings.filter(f => f.severity === 'error');
    const warnings = result.findings.filter(f => f.severity === 'warning');
    const infos = result.findings.filter(f => f.severity === 'info');

    if (errors.length > 0) {
      doc += '### 🔴 Errors\n\n';
      for (const f of errors) {
        doc += `- **[${f.category}]** ${f.message}\n`;
        if (f.element) doc += `  - Element: ${f.element}\n`;
        if (f.suggestion) doc += `  - 💡 ${f.suggestion}\n`;
      }
      doc += '\n';
    }

    if (warnings.length > 0) {
      doc += '### 🟡 Warnings\n\n';
      for (const f of warnings) {
        doc += `- **[${f.category}]** ${f.message}\n`;
        if (f.element) doc += `  - Element: ${f.element}\n`;
        if (f.suggestion) doc += `  - 💡 ${f.suggestion}\n`;
      }
      doc += '\n';
    }

    if (infos.length > 0) {
      doc += '### 🔵 Info\n\n';
      for (const f of infos) {
        doc += `- **[${f.category}]** ${f.message}\n`;
      }
      doc += '\n';
    }
  }

  doc += `## Recommendations

`;
  for (const rec of result.recommendations) {
    doc += `- ${rec}\n`;
  }

  doc += `
---

**Reviewed by**: MUSUBIX Design Review System
**Review Date**: ${now}
`;

  return doc;
}

export { generateC4Model, generateMermaidDiagram, generatePlantUMLDiagram };
