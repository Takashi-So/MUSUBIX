/**
 * Trace Command
 *
 * CLI commands for traceability management
 *
 * @packageDocumentation
 * @module cli/commands/trace
 *
 * @see REQ-CLI-005 - Trace CLI
 * @see REQ-TM-001 - Traceability Matrix
 * @see REQ-TM-002 - Impact Analysis
 * @see DES-MUSUBIX-001 Section 16-C.5 - traceコマンド設計
 * @see TSK-076〜078 - Trace CLI実装
 */

import type { Command } from 'commander';
import { readFile, writeFile, readdir, mkdir } from 'fs/promises';
import { resolve, join, extname } from 'path';
import { ExitCode, getGlobalOptions, outputResult } from '../base.js';

/**
 * Trace command options
 */
export interface TraceOptions {
  output?: string;
  format?: 'markdown' | 'json' | 'csv' | 'html';
  verbose?: boolean;
}

/**
 * Traceability link
 */
export interface TraceabilityLink {
  source: string;
  target: string;
  type: 'implements' | 'derives' | 'tests' | 'refines' | 'relates';
  status: 'valid' | 'broken' | 'pending';
  file?: string;
  line?: number;
}

/**
 * Traceability matrix entry
 */
export interface MatrixEntry {
  id: string;
  type: 'requirement' | 'design' | 'task' | 'code' | 'test';
  description: string;
  links: TraceabilityLink[];
  coverage: {
    design: boolean;
    implementation: boolean;
    test: boolean;
  };
}

/**
 * Matrix result
 */
export interface MatrixResult {
  success: boolean;
  entries: MatrixEntry[];
  statistics: {
    requirements: number;
    designs: number;
    tasks: number;
    implementations: number;
    tests: number;
    coverage: number;
  };
  message: string;
}

/**
 * Impact item
 */
export interface ImpactItem {
  id: string;
  type: string;
  impactLevel: 'direct' | 'indirect' | 'potential';
  description: string;
  affectedFiles?: string[];
}

/**
 * Impact result
 */
export interface ImpactResult {
  success: boolean;
  sourceId: string;
  impacts: ImpactItem[];
  riskLevel: 'low' | 'medium' | 'high' | 'critical';
  recommendations: string[];
  message: string;
}

/**
 * Validation issue
 */
export interface TraceValidationIssue {
  type: 'missing_link' | 'broken_link' | 'orphan' | 'circular';
  severity: 'error' | 'warning';
  source?: string;
  target?: string;
  message: string;
}

/**
 * Validation result
 */
export interface TraceValidationResult {
  success: boolean;
  valid: boolean;
  issues: TraceValidationIssue[];
  summary: {
    total: number;
    valid: number;
    broken: number;
    orphans: number;
  };
  message: string;
}

/**
 * ID patterns for different artifact types
 */
const ID_PATTERNS = {
  requirement: /REQ-[A-Z]+-\d+/g,
  design: /DES-[A-Z]+-\d+/g,
  task: /TSK-[A-Z]*-?\d+/g,
  test: /TEST-[A-Z]+-\d+/g,
};

/**
 * Register trace command
 */
export function registerTraceCommand(program: Command): void {
  const trace = program
    .command('trace')
    .description('Traceability management');

  // trace matrix
  trace
    .command('matrix')
    .description('Generate traceability matrix')
    .option('-o, --output <file>', 'Output file')
    .option('-f, --format <format>', 'Output format (markdown|json|csv|html)', 'markdown')
    .option('--specs <dir>', 'Specs directory', 'storage/specs')
    .option('--src <dir>', 'Source directory', 'packages')
    .action(async (options: TraceOptions & { specs?: string; src?: string }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const specsDir = resolve(process.cwd(), options.specs ?? 'storage/specs');
        const srcDir = resolve(process.cwd(), options.src ?? 'packages');

        // Collect all artifacts
        const entries = await collectArtifacts(specsDir, srcDir);

        // Build traceability links
        await buildTraceabilityLinks(entries, specsDir, srcDir);

        // Calculate statistics
        const statistics = calculateStatistics(entries);

        const result: MatrixResult = {
          success: true,
          entries,
          statistics,
          message: `Generated traceability matrix with ${entries.length} entries (${statistics.coverage.toFixed(1)}% coverage)`,
        };

        // Output
        if (options.output) {
          const outputPath = resolve(process.cwd(), options.output);
          await mkdir(resolve(outputPath, '..'), { recursive: true });

          let content: string;
          if (options.format === 'json' || globalOpts.json) {
            content = JSON.stringify(result, null, 2);
          } else if (options.format === 'csv') {
            content = generateCSVMatrix(entries);
          } else if (options.format === 'html') {
            content = generateHTMLMatrix(entries, statistics);
          } else {
            content = generateMarkdownMatrix(entries, statistics);
          }

          await writeFile(outputPath, content, 'utf-8');
          if (!globalOpts.quiet) {
            console.log(`✅ Traceability matrix saved to ${outputPath}`);
          }
        } else {
          outputResult(result, globalOpts);
        }

        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Matrix generation failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // trace impact
  trace
    .command('impact <id>')
    .description('Analyze change impact')
    .option('--depth <number>', 'Analysis depth', '3')
    .action(async (id: string, options: { depth?: string }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const depth = parseInt(options.depth ?? '3', 10);
        const specsDir = resolve(process.cwd(), 'storage/specs');
        const srcDir = resolve(process.cwd(), 'packages');

        // Find artifact by ID
        const entries = await collectArtifacts(specsDir, srcDir);
        await buildTraceabilityLinks(entries, specsDir, srcDir);

        // Find source entry
        const sourceEntry = entries.find(e => e.id === id);
        if (!sourceEntry) {
          throw new Error(`Artifact ${id} not found`);
        }

        // Analyze impact
        const impacts = analyzeImpact(sourceEntry, entries, depth);
        const riskLevel = calculateRiskLevel(impacts);
        const recommendations = generateRecommendations(sourceEntry, impacts);

        const result: ImpactResult = {
          success: true,
          sourceId: id,
          impacts,
          riskLevel,
          recommendations,
          message: `Found ${impacts.length} impacted items (Risk: ${riskLevel})`,
        };

        outputResult(result, globalOpts);
        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Impact analysis failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // trace validate
  trace
    .command('validate')
    .description('Validate traceability links')
    .option('--strict', 'Enable strict mode', false)
    .action(async (options: { strict?: boolean }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const specsDir = resolve(process.cwd(), 'storage/specs');
        const srcDir = resolve(process.cwd(), 'packages');

        // Collect and link artifacts
        const entries = await collectArtifacts(specsDir, srcDir);
        await buildTraceabilityLinks(entries, specsDir, srcDir);

        // Validate links
        const issues = validateTraceability(entries, options.strict ?? false);

        const total = entries.reduce((sum, e) => sum + e.links.length, 0);
        const broken = issues.filter(i => i.type === 'broken_link').length;
        const orphans = issues.filter(i => i.type === 'orphan').length;

        const result: TraceValidationResult = {
          success: true,
          valid: issues.filter(i => i.severity === 'error').length === 0,
          issues,
          summary: {
            total,
            valid: total - broken,
            broken,
            orphans,
          },
          message: issues.length === 0
            ? '✅ All traceability links are valid'
            : `⚠️ Found ${issues.length} issues (${broken} broken links, ${orphans} orphans)`,
        };

        outputResult(result, globalOpts);
        process.exit(result.valid ? ExitCode.SUCCESS : ExitCode.VALIDATION_ERROR);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Validation failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });
}

/**
 * Collect artifacts from directories
 */
async function collectArtifacts(specsDir: string, srcDir: string): Promise<MatrixEntry[]> {
  const entries: MatrixEntry[] = [];
  const seenIds = new Set<string>();

  // Collect from specs directory
  try {
    const specFiles = await readdir(specsDir);
    for (const file of specFiles) {
      if (!file.endsWith('.md')) continue;

      const content = await readFile(join(specsDir, file), 'utf-8');

      // Extract requirement IDs
      const reqMatches = content.match(ID_PATTERNS.requirement) || [];
      for (const id of reqMatches) {
        if (seenIds.has(id)) continue;
        seenIds.add(id);

        // Extract description
        const descRegex = new RegExp(`${id}[^\\n]*\\n([^\\n]+)`, 'i');
        const descMatch = content.match(descRegex);

        entries.push({
          id,
          type: 'requirement',
          description: descMatch?.[1]?.trim() || 'No description',
          links: [],
          coverage: { design: false, implementation: false, test: false },
        });
      }

      // Extract design IDs
      const desMatches = content.match(ID_PATTERNS.design) || [];
      for (const id of desMatches) {
        if (seenIds.has(id)) continue;
        seenIds.add(id);

        entries.push({
          id,
          type: 'design',
          description: 'Design element',
          links: [],
          coverage: { design: true, implementation: false, test: false },
        });
      }

      // Extract task IDs
      const taskMatches = content.match(ID_PATTERNS.task) || [];
      for (const id of taskMatches) {
        if (seenIds.has(id)) continue;
        seenIds.add(id);

        entries.push({
          id,
          type: 'task',
          description: 'Implementation task',
          links: [],
          coverage: { design: true, implementation: false, test: false },
        });
      }
    }
  } catch {
    // Specs directory doesn't exist
  }

  // Collect from source directory
  await scanSourceDir(srcDir, entries, seenIds);

  return entries;
}

/**
 * Scan source directory for code references
 */
async function scanSourceDir(
  dir: string,
  entries: MatrixEntry[],
  seenIds: Set<string>
): Promise<void> {
  try {
    const items = await readdir(dir, { withFileTypes: true });

    for (const item of items) {
      const fullPath = join(dir, item.name);

      if (item.isDirectory()) {
        if (!item.name.startsWith('.') && item.name !== 'node_modules' && item.name !== 'dist') {
          await scanSourceDir(fullPath, entries, seenIds);
        }
      } else if (item.isFile()) {
        const ext = extname(item.name);
        if (['.ts', '.js', '.tsx', '.jsx'].includes(ext)) {
          const content = await readFile(fullPath, 'utf-8');

          // Find referenced IDs in code comments
          for (const pattern of Object.values(ID_PATTERNS)) {
            const matches = content.match(pattern) || [];
            for (const id of matches) {
              // Update existing entry or add code reference
              const existing = entries.find(e => e.id === id);
              if (existing) {
                existing.coverage.implementation = true;
                existing.links.push({
                  source: id,
                  target: fullPath,
                  type: 'implements',
                  status: 'valid',
                  file: fullPath,
                });
              }
            }
          }

          // Check for test files
          if (item.name.includes('.test.') || item.name.includes('.spec.')) {
            const testMatches = content.match(ID_PATTERNS.requirement) || [];
            for (const id of testMatches) {
              const existing = entries.find(e => e.id === id);
              if (existing) {
                existing.coverage.test = true;
                existing.links.push({
                  source: id,
                  target: fullPath,
                  type: 'tests',
                  status: 'valid',
                  file: fullPath,
                });
              }
            }
          }
        }
      }
    }
  } catch {
    // Directory doesn't exist or access error
  }
}

/**
 * Build traceability links between artifacts
 */
async function buildTraceabilityLinks(
  entries: MatrixEntry[],
  _specsDir: string,
  _srcDir: string
): Promise<void> {
  // Build links between requirements and designs
  for (const entry of entries) {
    if (entry.type === 'requirement') {
      // Find related designs
      const designs = entries.filter(e => e.type === 'design');
      for (const design of designs) {
        entry.links.push({
          source: entry.id,
          target: design.id,
          type: 'derives',
          status: 'valid',
        });
        entry.coverage.design = true;
      }
    }
  }

  // Link requirements to tasks
  const requirements = entries.filter(e => e.type === 'requirement');
  const tasks = entries.filter(e => e.type === 'task');

  for (const req of requirements) {
    for (const task of tasks) {
      // Check if task references requirement
      if (task.description.includes(req.id) || 
          task.links.some(l => l.target === req.id)) {
        req.links.push({
          source: req.id,
          target: task.id,
          type: 'refines',
          status: 'valid',
        });
      }
    }
  }
}

/**
 * Calculate statistics
 */
function calculateStatistics(entries: MatrixEntry[]): MatrixResult['statistics'] {
  const requirements = entries.filter(e => e.type === 'requirement').length;
  const designs = entries.filter(e => e.type === 'design').length;
  const tasks = entries.filter(e => e.type === 'task').length;
  const implementations = entries.filter(e => e.coverage.implementation).length;
  const tests = entries.filter(e => e.coverage.test).length;

  const coveredRequirements = entries.filter(
    e => e.type === 'requirement' && e.coverage.design && e.coverage.implementation
  ).length;
  const coverage = requirements > 0 ? (coveredRequirements / requirements) * 100 : 0;

  return { requirements, designs, tasks, implementations, tests, coverage };
}

/**
 * Analyze impact
 */
function analyzeImpact(
  source: MatrixEntry,
  entries: MatrixEntry[],
  depth: number
): ImpactItem[] {
  const impacts: ImpactItem[] = [];
  const visited = new Set<string>();

  function traverse(entry: MatrixEntry, level: number): void {
    if (level > depth || visited.has(entry.id)) return;
    visited.add(entry.id);

    for (const link of entry.links) {
      const target = entries.find(e => e.id === link.target);
      if (target && !visited.has(target.id)) {
        impacts.push({
          id: target.id,
          type: target.type,
          impactLevel: level === 1 ? 'direct' : level === 2 ? 'indirect' : 'potential',
          description: target.description,
          affectedFiles: target.links
            .filter(l => l.file)
            .map(l => l.file as string),
        });
        traverse(target, level + 1);
      }
    }
  }

  traverse(source, 1);
  return impacts;
}

/**
 * Calculate risk level
 */
function calculateRiskLevel(impacts: ImpactItem[]): 'low' | 'medium' | 'high' | 'critical' {
  const direct = impacts.filter(i => i.impactLevel === 'direct').length;
  const totalIndirect = impacts.filter(i => i.impactLevel === 'indirect' || i.impactLevel === 'potential').length;

  if (direct > 10 || impacts.length > 20) return 'critical';
  if (direct > 5 || impacts.length > 10) return 'high';
  if (direct > 2 || impacts.length > 5 || totalIndirect > 10) return 'medium';
  return 'low';
}

/**
 * Generate recommendations
 */
function generateRecommendations(source: MatrixEntry, impacts: ImpactItem[]): string[] {
  const recommendations: string[] = [];

  if (impacts.length > 10) {
    recommendations.push(`Consider breaking the change to ${source.id} into smaller increments`);
  }

  const codeImpacts = impacts.filter(i => i.affectedFiles && i.affectedFiles.length > 0);
  if (codeImpacts.length > 0) {
    recommendations.push(`Review ${codeImpacts.length} code files before making changes to ${source.id}`);
  }

  if (impacts.some(i => i.type === 'test')) {
    recommendations.push('Update affected tests after implementation');
  }

  if (impacts.length === 0) {
    recommendations.push('This change has minimal impact - safe to proceed');
  }

  return recommendations;
}

/**
 * Validate traceability
 */
function validateTraceability(
  entries: MatrixEntry[],
  strict: boolean
): TraceValidationIssue[] {
  const issues: TraceValidationIssue[] = [];
  const allIds = new Set(entries.map(e => e.id));

  for (const entry of entries) {
    // Check for orphans (requirements without implementation)
    if (entry.type === 'requirement' && !entry.coverage.implementation) {
      issues.push({
        type: 'orphan',
        severity: strict ? 'error' : 'warning',
        source: entry.id,
        message: `Requirement ${entry.id} has no implementation`,
      });
    }

    // Check for broken links
    for (const link of entry.links) {
      if (typeof link.target === 'string' && link.target.match(/^(REQ|DES|TSK)-/)) {
        if (!allIds.has(link.target)) {
          issues.push({
            type: 'broken_link',
            severity: 'error',
            source: entry.id,
            target: link.target,
            message: `Link from ${entry.id} to ${link.target} is broken (target not found)`,
          });
        }
      }
    }

    // Check for missing design traceability
    if (entry.type === 'requirement' && !entry.coverage.design && strict) {
      issues.push({
        type: 'missing_link',
        severity: 'warning',
        source: entry.id,
        message: `Requirement ${entry.id} has no design element`,
      });
    }

    // Check for missing tests
    if (entry.type === 'requirement' && !entry.coverage.test && strict) {
      issues.push({
        type: 'missing_link',
        severity: 'warning',
        source: entry.id,
        message: `Requirement ${entry.id} has no test coverage`,
      });
    }
  }

  return issues;
}

/**
 * Generate markdown matrix
 */
function generateMarkdownMatrix(entries: MatrixEntry[], stats: MatrixResult['statistics']): string {
  let output = '# Traceability Matrix\n\n';

  output += '## Statistics\n\n';
  output += `| Metric | Count |\n`;
  output += `|--------|-------|\n`;
  output += `| Requirements | ${stats.requirements} |\n`;
  output += `| Designs | ${stats.designs} |\n`;
  output += `| Tasks | ${stats.tasks} |\n`;
  output += `| Implementations | ${stats.implementations} |\n`;
  output += `| Tests | ${stats.tests} |\n`;
  output += `| **Coverage** | **${stats.coverage.toFixed(1)}%** |\n\n`;

  output += '## Matrix\n\n';
  output += '| ID | Type | Design | Impl | Test |\n';
  output += '|----|------|--------|------|------|\n';

  for (const entry of entries) {
    output += `| ${entry.id} | ${entry.type} | ${entry.coverage.design ? '✅' : '❌'} | ${entry.coverage.implementation ? '✅' : '❌'} | ${entry.coverage.test ? '✅' : '❌'} |\n`;
  }

  output += `\n*Generated: ${new Date().toISOString()}*\n`;
  return output;
}

/**
 * Generate CSV matrix
 */
function generateCSVMatrix(entries: MatrixEntry[]): string {
  let output = 'ID,Type,Description,Design,Implementation,Test,Links\n';

  for (const entry of entries) {
    const links = entry.links.map(l => `${l.type}:${l.target}`).join(';');
    output += `"${entry.id}","${entry.type}","${entry.description}",${entry.coverage.design},${entry.coverage.implementation},${entry.coverage.test},"${links}"\n`;
  }

  return output;
}

/**
 * Generate HTML matrix
 */
function generateHTMLMatrix(entries: MatrixEntry[], stats: MatrixResult['statistics']): string {
  return `<!DOCTYPE html>
<html>
<head>
  <title>Traceability Matrix</title>
  <style>
    body { font-family: Arial, sans-serif; margin: 20px; }
    table { border-collapse: collapse; width: 100%; }
    th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
    th { background-color: #4CAF50; color: white; }
    tr:nth-child(even) { background-color: #f2f2f2; }
    .check { color: #4CAF50; }
    .cross { color: #f44336; }
    .summary { margin: 20px 0; padding: 15px; background: #f5f5f5; border-radius: 5px; }
  </style>
</head>
<body>
  <h1>Traceability Matrix</h1>

  <div class="summary">
    <h2>Coverage: ${stats.coverage.toFixed(1)}%</h2>
    <p>Requirements: ${stats.requirements} | Designs: ${stats.designs} | Tasks: ${stats.tasks} | Tests: ${stats.tests}</p>
  </div>

  <table>
    <tr>
      <th>ID</th>
      <th>Type</th>
      <th>Design</th>
      <th>Implementation</th>
      <th>Test</th>
    </tr>
    ${entries.map(e => `
    <tr>
      <td>${e.id}</td>
      <td>${e.type}</td>
      <td class="${e.coverage.design ? 'check' : 'cross'}">${e.coverage.design ? '✓' : '✗'}</td>
      <td class="${e.coverage.implementation ? 'check' : 'cross'}">${e.coverage.implementation ? '✓' : '✗'}</td>
      <td class="${e.coverage.test ? 'check' : 'cross'}">${e.coverage.test ? '✓' : '✗'}</td>
    </tr>`).join('')}
  </table>

  <p><em>Generated: ${new Date().toISOString()}</em></p>
</body>
</html>`;
}

export {
  collectArtifacts,
  buildTraceabilityLinks,
  analyzeImpact,
  validateTraceability,
};
