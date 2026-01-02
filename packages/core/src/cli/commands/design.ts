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

  // Extract entities from content
  const systemMatches = content.match(/\b(?:system|service|application|component|module)\s+["']?([A-Za-z0-9_-]+)["']?/gi) || [];
  const actorMatches = content.match(/\b(?:user|admin|client|actor)\s+["']?([A-Za-z0-9_-]+)["']?/gi) || [];

  const seenIds = new Set<string>();

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

  // Generate relationships
  const elementIds = elements.map(e => e.id);
  for (let i = 0; i < elementIds.length - 1; i++) {
    relationships.push({
      source: elementIds[i],
      target: elementIds[i + 1],
      description: 'interacts with',
    });
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
 * Generate traceability
 */
function generateTraceability(content: string, model: C4Model): Array<{ requirement: string; designElement: string }> {
  const traceability: Array<{ requirement: string; designElement: string }> = [];

  // Extract requirement IDs
  const reqMatches = content.match(/REQ-[A-Z]+-\d+/g) || [];

  for (const req of reqMatches) {
    if (model.elements.length > 0) {
      traceability.push({
        requirement: req,
        designElement: model.elements[0].id,
      });
    }
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

export { generateC4Model, generateMermaidDiagram, generatePlantUMLDiagram };
