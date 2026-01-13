/**
 * Scaffold Result Aggregator
 *
 * Aggregates and formats results from multiple generators
 *
 * @packageDocumentation
 * @module cli/generators/result-aggregator
 *
 * @traceability REQ-SCF-006
 * @see DES-SCF-003 - Result Aggregator Design
 */

import { writeFile, mkdir } from 'fs/promises';
import { dirname } from 'path';
import type { GeneratedFile as VOGeneratedFile } from './value-object-generator.js';
import type { GeneratedFile as SMGeneratedFile } from './status-machine-generator.js';

/**
 * Generic generated file type
 */
export type GeneratedFile = VOGeneratedFile | SMGeneratedFile;

/**
 * Aggregated scaffold result
 */
export interface AggregatedResult {
  /** Total files generated */
  totalFiles: number;

  /** Files by type */
  byType: {
    valueObjects: GeneratedFile[];
    statusMachines: GeneratedFile[];
    tests: GeneratedFile[];
    other: GeneratedFile[];
  };

  /** Generation timestamp */
  timestamp: string;

  /** Domain used */
  domain: string;

  /** Output directory */
  outputDir: string;

  /** Success status */
  success: boolean;

  /** Error messages if any */
  errors: string[];

  /** Warnings if any */
  warnings: string[];
}

/**
 * Result aggregator configuration
 */
export interface ResultAggregatorConfig {
  domain: string;
  outputDir: string;
  generateSummary?: boolean;
  summaryFormat?: 'json' | 'markdown' | 'console';
}

/**
 * Result Aggregator
 *
 * Collects, organizes, and reports on generated scaffold files
 */
export class ResultAggregator {
  private voFiles: GeneratedFile[] = [];
  private smFiles: GeneratedFile[] = [];
  private testFiles: GeneratedFile[] = [];
  private otherFiles: GeneratedFile[] = [];
  private errors: string[] = [];
  private warnings: string[] = [];

  constructor(private config: ResultAggregatorConfig) {}

  /**
   * Add Value Object generated files
   */
  addValueObjectFiles(files: GeneratedFile[]): void {
    for (const file of files) {
      if (file.type === 'test') {
        this.testFiles.push(file);
      } else {
        this.voFiles.push(file);
      }
    }
  }

  /**
   * Add Status Machine generated files
   */
  addStatusMachineFiles(files: GeneratedFile[]): void {
    for (const file of files) {
      if (file.type === 'test') {
        this.testFiles.push(file);
      } else {
        this.smFiles.push(file);
      }
    }
  }

  /**
   * Add other generated files
   */
  addOtherFiles(files: GeneratedFile[]): void {
    this.otherFiles.push(...files);
  }

  /**
   * Add an error
   */
  addError(message: string): void {
    this.errors.push(message);
  }

  /**
   * Add a warning
   */
  addWarning(message: string): void {
    this.warnings.push(message);
  }

  /**
   * Get aggregated result
   */
  getResult(): AggregatedResult {
    const allFiles = [
      ...this.voFiles,
      ...this.smFiles,
      ...this.testFiles,
      ...this.otherFiles,
    ];

    return {
      totalFiles: allFiles.length,
      byType: {
        valueObjects: this.voFiles,
        statusMachines: this.smFiles,
        tests: this.testFiles,
        other: this.otherFiles,
      },
      timestamp: new Date().toISOString(),
      domain: this.config.domain,
      outputDir: this.config.outputDir,
      success: this.errors.length === 0,
      errors: this.errors,
      warnings: this.warnings,
    };
  }

  /**
   * Generate summary in specified format
   */
  generateSummary(format: 'json' | 'markdown' | 'console' = 'console'): string {
    const result = this.getResult();

    switch (format) {
      case 'json':
        return this.generateJsonSummary(result);
      case 'markdown':
        return this.generateMarkdownSummary(result);
      case 'console':
      default:
        return this.generateConsoleSummary(result);
    }
  }

  /**
   * Write summary to file
   */
  async writeSummary(filePath: string, format: 'json' | 'markdown' = 'markdown'): Promise<void> {
    const summary = this.generateSummary(format);
    await mkdir(dirname(filePath), { recursive: true });
    await writeFile(filePath, summary, 'utf-8');
  }

  /**
   * Print summary to console
   */
  printSummary(): void {
    console.log(this.generateSummary('console'));
  }

  /**
   * Get all file paths (relative)
   */
  getAllFilePaths(): string[] {
    const result = this.getResult();
    const allFiles = [
      ...result.byType.valueObjects,
      ...result.byType.statusMachines,
      ...result.byType.tests,
      ...result.byType.other,
    ];

    return allFiles.map((f) => {
      // Convert absolute path to relative
      return f.path.replace(this.config.outputDir + '/', '');
    });
  }

  /**
   * Generate JSON summary
   */
  private generateJsonSummary(result: AggregatedResult): string {
    const summary = {
      ...result,
      byType: {
        valueObjects: result.byType.valueObjects.map((f) => ({
          path: f.path.replace(this.config.outputDir + '/', ''),
          type: f.type,
        })),
        statusMachines: result.byType.statusMachines.map((f) => ({
          path: f.path.replace(this.config.outputDir + '/', ''),
          type: f.type,
        })),
        tests: result.byType.tests.map((f) => ({
          path: f.path.replace(this.config.outputDir + '/', ''),
          type: f.type,
        })),
        other: result.byType.other.map((f) => ({
          path: f.path.replace(this.config.outputDir + '/', ''),
          type: f.type,
        })),
      },
    };

    return JSON.stringify(summary, null, 2);
  }

  /**
   * Generate Markdown summary
   */
  private generateMarkdownSummary(result: AggregatedResult): string {
    const lines: string[] = [];

    lines.push('# Scaffold Generation Summary');
    lines.push('');
    lines.push(`**Generated**: ${result.timestamp}`);
    lines.push(`**Domain**: ${result.domain}`);
    lines.push(`**Output**: ${result.outputDir}`);
    lines.push(`**Status**: ${result.success ? '✅ Success' : '❌ Failed'}`);
    lines.push('');

    // Statistics
    lines.push('## Statistics');
    lines.push('');
    lines.push('| Type | Count |');
    lines.push('|------|-------|');
    lines.push(`| Value Objects | ${result.byType.valueObjects.length} |`);
    lines.push(`| Status Machines | ${result.byType.statusMachines.length} |`);
    lines.push(`| Tests | ${result.byType.tests.length} |`);
    lines.push(`| Other | ${result.byType.other.length} |`);
    lines.push(`| **Total** | **${result.totalFiles}** |`);
    lines.push('');

    // File list
    if (result.byType.valueObjects.length > 0) {
      lines.push('## Value Objects');
      lines.push('');
      for (const file of result.byType.valueObjects) {
        const relPath = file.path.replace(this.config.outputDir + '/', '');
        lines.push(`- \`${relPath}\``);
      }
      lines.push('');
    }

    if (result.byType.statusMachines.length > 0) {
      lines.push('## Status Machines');
      lines.push('');
      for (const file of result.byType.statusMachines) {
        const relPath = file.path.replace(this.config.outputDir + '/', '');
        lines.push(`- \`${relPath}\``);
      }
      lines.push('');
    }

    if (result.byType.tests.length > 0) {
      lines.push('## Tests');
      lines.push('');
      for (const file of result.byType.tests) {
        const relPath = file.path.replace(this.config.outputDir + '/', '');
        lines.push(`- \`${relPath}\``);
      }
      lines.push('');
    }

    // Errors and warnings
    if (result.errors.length > 0) {
      lines.push('## Errors');
      lines.push('');
      for (const error of result.errors) {
        lines.push(`- ❌ ${error}`);
      }
      lines.push('');
    }

    if (result.warnings.length > 0) {
      lines.push('## Warnings');
      lines.push('');
      for (const warning of result.warnings) {
        lines.push(`- ⚠️ ${warning}`);
      }
      lines.push('');
    }

    // Traceability
    lines.push('## Traceability');
    lines.push('');
    lines.push('| Requirement | Implementation |');
    lines.push('|-------------|----------------|');
    lines.push('| REQ-SCF-001 | Value Object Generator |');
    lines.push('| REQ-SCF-003 | Status Machine Generator |');
    lines.push('| REQ-SCF-006 | Result Aggregator |');
    lines.push('');

    return lines.join('\n');
  }

  /**
   * Generate console-friendly summary
   */
  private generateConsoleSummary(result: AggregatedResult): string {
    const lines: string[] = [];

    const status = result.success ? '✅' : '❌';
    lines.push('');
    lines.push(`${status} Scaffold Generation ${result.success ? 'Complete' : 'Failed'}`);
    lines.push('');
    lines.push(`  Domain:      ${result.domain}`);
    lines.push(`  Output:      ${result.outputDir}`);
    lines.push(`  Total Files: ${result.totalFiles}`);
    lines.push('');
    lines.push('  📦 Generated:');
    lines.push(`     Value Objects:   ${result.byType.valueObjects.length}`);
    lines.push(`     Status Machines: ${result.byType.statusMachines.length}`);
    lines.push(`     Tests:           ${result.byType.tests.length}`);
    lines.push(`     Other:           ${result.byType.other.length}`);

    if (result.errors.length > 0) {
      lines.push('');
      lines.push('  ❌ Errors:');
      for (const error of result.errors) {
        lines.push(`     - ${error}`);
      }
    }

    if (result.warnings.length > 0) {
      lines.push('');
      lines.push('  ⚠️ Warnings:');
      for (const warning of result.warnings) {
        lines.push(`     - ${warning}`);
      }
    }

    lines.push('');

    return lines.join('\n');
  }
}

/**
 * Create a new result aggregator
 */
export function createResultAggregator(config: ResultAggregatorConfig): ResultAggregator {
  return new ResultAggregator(config);
}
