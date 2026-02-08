/**
 * Codegen Command
 *
 * CLI commands for code generation and analysis
 *
 * @packageDocumentation
 * @module cli/commands/codegen
 *
 * @see REQ-CLI-003 - Codegen CLI
 * @see REQ-CG-001 - Code Generation
 * @see REQ-CG-002 - Static Analysis
 * @see DES-MUSUBIX-001 Section 16-C.3 - codegen command design
 * @see TSK-071-073 - Codegen CLI implementation
 */

import type { Command } from 'commander';
import { readFile, writeFile, mkdir, stat } from 'fs/promises';
import { resolve, dirname } from 'path';
import { ExitCode, getGlobalOptions, outputResult } from '../../base.js';
import type {
  CodegenOptions,
  GenerationResult,
  AnalysisIssue,
  AnalysisResult,
  SecurityVulnerability,
  SecurityResult,
} from './types.js';
import { generateCodeFromDesign } from './generators.js';
import { analyzeFile, analyzeDirectory, scanFile, scanDirectory } from './security-patterns.js';

// Re-export all types
export type {
  CodegenOptions,
  GeneratedCode,
  GenerationResult,
  AnalysisIssue,
  AnalysisResult,
  SecurityVulnerability,
  SecurityResult,
  GeneratedSkeleton,
  FullSkeletonOptions,
  ExtendedGenerateOptions,
  C4Component,
  DesignPattern,
} from './types.js';

// Re-export generators
export { generateCodeFromDesign, generateFullSkeleton } from './generators.js';

// Re-export security/analysis functions
export { analyzeFile, analyzeDirectory, scanFile, scanDirectory } from './security-patterns.js';

/**
 * Register codegen command
 */
export function registerCodegenCommand(program: Command): void {
  const codegen = program
    .command('codegen')
    .description('Code generation and analysis');

  // codegen generate
  codegen
    .command('generate <design>')
    .description('Generate code from design')
    .option('-o, --output <dir>', 'Output directory', 'src/generated')
    .option('-l, --language <lang>', 'Target language', 'typescript')
    .option('-t, --template <name>', 'Code template to use')
    .option('--full-skeleton', 'Generate 4 files per component (interface, impl, test, index)')
    .option('--with-tests', 'Include test files in generation')
    .action(async (design: string, options: CodegenOptions & { fullSkeleton?: boolean; withTests?: boolean }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const designPath = resolve(process.cwd(), design);
        const content = await readFile(designPath, 'utf-8');

        // Parse design and generate code
        const files = generateCodeFromDesign(content, options, { fullSkeleton: options.fullSkeleton, withTests: options.withTests });

        const outputDir = resolve(process.cwd(), options.output ?? 'src/generated');
        await mkdir(outputDir, { recursive: true });

        let totalLines = 0;
        const languages = new Set<string>();

        for (const file of files) {
          const filePath = resolve(outputDir, file.filename);
          await mkdir(dirname(filePath), { recursive: true });
          await writeFile(filePath, file.content, 'utf-8');
          totalLines += file.content.split('\n').length;
          languages.add(file.language);
        }

        const result: GenerationResult = {
          success: true,
          files,
          summary: {
            totalFiles: files.length,
            totalLines,
            languages: Array.from(languages),
          },
          message: `Generated ${files.length} files (${totalLines} lines)`,
        };

        if (!globalOpts.quiet) {
          console.log(`\u2705 Code generated in ${outputDir}`);
          for (const file of files) {
            console.log(`   - ${file.filename}`);
          }
        }

        if (globalOpts.json) {
          outputResult(result, globalOpts);
        }

        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`\u274C Code generation failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // codegen analyze
  codegen
    .command('analyze <path>')
    .description('Static code analysis')
    .option('--strict', 'Enable strict mode', false)
    .action(async (path: string, _options: { strict?: boolean }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const targetPath = resolve(process.cwd(), path);
        const issues: AnalysisIssue[] = [];
        let fileCount = 0;
        let totalLines = 0;

        // Check if path is file or directory
        const pathStat = await stat(targetPath);

        if (pathStat.isDirectory()) {
          await analyzeDirectory(targetPath, issues, (lines) => {
            fileCount++;
            totalLines += lines;
          });
        } else {
          const content = await readFile(targetPath, 'utf-8');
          const lines = content.split('\n');
          analyzeFile(targetPath, lines, issues);
          fileCount = 1;
          totalLines = lines.length;
        }

        const errors = issues.filter(i => i.severity === 'error').length;
        const warnings = issues.filter(i => i.severity === 'warning').length;
        const info = issues.filter(i => i.severity === 'info').length;

        // Calculate metrics
        const complexity = Math.round(totalLines / 10); // Simplified
        const maintainabilityIndex = Math.max(0, 100 - errors * 10 - warnings * 2);

        const result: AnalysisResult = {
          success: true,
          issues,
          metrics: {
            files: fileCount,
            lines: totalLines,
            complexity,
            maintainabilityIndex,
          },
          summary: { errors, warnings, info },
          message: errors === 0
            ? `\u2705 Analyzed ${fileCount} files - No errors found`
            : `\u26A0\uFE0F Found ${errors} errors, ${warnings} warnings`,
        };

        outputResult(result, globalOpts);
        process.exit(errors === 0 ? ExitCode.SUCCESS : ExitCode.VALIDATION_ERROR);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`\u274C Analysis failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // codegen security
  codegen
    .command('security <path>')
    .description('Security scan')
    .option('--severity <level>', 'Minimum severity to report', 'low')
    .action(async (path: string, options: { severity?: string }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const targetPath = resolve(process.cwd(), path);
        const vulnerabilities: SecurityVulnerability[] = [];

        // Check if path is file or directory
        const pathStat = await stat(targetPath);

        if (pathStat.isDirectory()) {
          await scanDirectory(targetPath, vulnerabilities);
        } else {
          const content = await readFile(targetPath, 'utf-8');
          scanFile(targetPath, content, vulnerabilities);
        }

        // Filter by severity
        const severityOrder = ['critical', 'high', 'medium', 'low'];
        const minSeverityIndex = severityOrder.indexOf(options.severity ?? 'low');
        const filtered = vulnerabilities.filter(v =>
          severityOrder.indexOf(v.severity) <= minSeverityIndex
        );

        const critical = filtered.filter(v => v.severity === 'critical').length;
        const high = filtered.filter(v => v.severity === 'high').length;
        const medium = filtered.filter(v => v.severity === 'medium').length;
        const low = filtered.filter(v => v.severity === 'low').length;

        // Calculate security score (0-100)
        const score = Math.max(0, 100 - critical * 30 - high * 15 - medium * 5 - low * 1);

        const result: SecurityResult = {
          success: true,
          vulnerabilities: filtered,
          summary: { critical, high, medium, low },
          score,
          message: critical + high === 0
            ? `\u2705 Security score: ${score}/100 - No critical issues`
            : `\uD83D\uDD34 Security score: ${score}/100 - ${critical} critical, ${high} high severity issues`,
        };

        outputResult(result, globalOpts);
        process.exit(critical === 0 ? ExitCode.SUCCESS : ExitCode.VALIDATION_ERROR);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`\u274C Security scan failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // codegen status - Generate status transition code (BP-DESIGN-001)
  codegen
    .command('status <spec>')
    .description('Generate status transition code from specification')
    .option('-o, --output <dir>', 'Output directory', 'src/generated')
    .option('--no-validator', 'Skip generating validator function')
    .option('--no-helpers', 'Skip generating helper functions')
    .option('--enum', 'Use enum instead of union type')
    .option('--no-jsdoc', 'Skip JSDoc comments')
    .action(async (spec: string, options: { output?: string; validator?: boolean; helpers?: boolean; enum?: boolean; jsdoc?: boolean }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const specPath = resolve(process.cwd(), spec);
        const content = await readFile(specPath, 'utf-8');

        // Dynamic import to avoid circular dependency
        const { StatusTransitionGenerator, parseStatusMachineSpec } = await import('../../../codegen/status-transition-generator.js');

        // Parse spec (support both JSON and text format)
        let machineSpec;
        if (spec.endsWith('.json')) {
          machineSpec = JSON.parse(content);
        } else {
          machineSpec = parseStatusMachineSpec(content);
        }

        const generator = new StatusTransitionGenerator({
          useUnionType: !options.enum,
          generateValidator: options.validator !== false,
          generateHelpers: options.helpers !== false,
          includeJSDoc: options.jsdoc !== false,
        });

        const result = generator.generate(machineSpec);

        const outputDir = resolve(process.cwd(), options.output ?? 'src/generated');
        await mkdir(outputDir, { recursive: true });
        const outputPath = resolve(outputDir, result.fileName);
        await writeFile(outputPath, result.code, 'utf-8');

        if (!globalOpts.quiet) {
          console.log(`\u2705 Status transition code generated`);
          console.log(`   \uD83D\uDCC4 ${outputPath}`);
          console.log(`   \uD83D\uDCCA ${result.statusCount} statuses, ${result.transitionCount} transitions`);
          if (result.initialStatus) {
            console.log(`   \uD83D\uDE80 Initial: ${result.initialStatus}`);
          }
          if (result.terminalStatuses.length > 0) {
            console.log(`   \uD83C\uDFC1 Terminal: ${result.terminalStatuses.join(', ')}`);
          }
        }

        if (globalOpts.json) {
          outputResult({
            success: true,
            file: outputPath,
            ...result,
          }, globalOpts);
        }

        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`\u274C Status code generation failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });
}
