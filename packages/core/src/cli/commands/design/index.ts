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
import { ExitCode, getGlobalOptions, outputResult } from '../../base.js';
import type {
  DesignOptions,
  GenerateResult,
  DesignValidationResult,
  PatternDetectionResult,
  ADRDocument,
} from './types.js';
import { detectApplicablePatterns, generatePatternRecommendations } from './patterns.js';
import { generateC4Model, generateTraceability } from './c4-generator.js';
import { generateMermaidDiagram, generatePlantUMLDiagram, generateMarkdownDesign, generateADRMarkdown } from './diagram-generator.js';
import { validateDesign, reviewDesign, displayDesignReviewResult, generateDesignReviewDocument } from './validation.js';

// Re-export all types
export type {
  DesignOptions,
  C4Level,
  C4Element,
  C4Relationship,
  C4Model,
  DesignPattern,
  GenerateResult,
  DesignValidationResult,
  ADRDocument,
  PatternDetectionResult,
  DesignReviewResult,
  DesignReviewFinding,
} from './types.js';

// Re-export patterns
export { SOLID_PRINCIPLES, KNOWN_PATTERNS, detectApplicablePatterns, generatePatternRecommendations } from './patterns.js';

// Re-export C4 generator
export { generateC4Model, generateTraceability } from './c4-generator.js';

// Re-export diagram generators
export { generateMermaidDiagram, generatePlantUMLDiagram, generateMarkdownDesign, generateADRMarkdown } from './diagram-generator.js';

// Re-export validation
export { validateDesign, reviewDesign, displayDesignReviewResult, generateDesignReviewDocument } from './validation.js';

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

  // design traceability
  design
    .command('traceability')
    .description('Validate traceability between requirements and designs (Article V)')
    .option('-p, --project <path>', 'Project root path', process.cwd())
    .option('--specs-dir <dir>', 'Requirements directory', 'storage/specs')
    .option('--design-dir <dir>', 'Design directory', 'storage/design')
    .option('--min-coverage <percent>', 'Minimum coverage percentage', '80')
    .option('--require-full', 'Require 100% coverage', false)
    .action(async (options: {
      project?: string;
      specsDir?: string;
      designDir?: string;
      minCoverage?: string;
      requireFull?: boolean;
    }) => {
      const globalOpts = getGlobalOptions(program);
      const { TraceabilityValidator } = await import('../../../validators/traceability-validator.js');

      try {
        const projectRoot = resolve(process.cwd(), options.project ?? '.');
        const validator = new TraceabilityValidator({
          specsDir: options.specsDir,
          designDir: options.designDir,
          minCoverage: parseInt(options.minCoverage ?? '80', 10),
          requireFullCoverage: options.requireFull,
        });

        const result = await validator.validate(projectRoot);

        if (globalOpts.json) {
          outputResult(result, globalOpts);
        } else {
          const report = validator.generateReport(result);
          console.log(report);
        }

        process.exit(result.valid ? ExitCode.SUCCESS : ExitCode.VALIDATION_ERROR);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Traceability validation failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });
}
