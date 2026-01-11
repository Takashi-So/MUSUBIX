/**
 * @fileoverview Security CLI commands
 * @module @nahisaho/musubix-security/cli
 * @trace REQ-SEC-CLI-001
 */

import { Command } from 'commander';
import * as path from 'node:path';

import {
  createSecurityService,
  type CompleteScanResult,
} from '../services/index.js';
import type { ReportFormat } from '../services/report-generator.js';

/**
 * CLI output formatter
 */
class CLIFormatter {
  private colors = {
    critical: '\x1b[31m', // red
    high: '\x1b[91m', // light red
    medium: '\x1b[33m', // yellow
    low: '\x1b[36m', // cyan
    info: '\x1b[34m', // blue
    reset: '\x1b[0m',
    bold: '\x1b[1m',
    dim: '\x1b[2m',
    green: '\x1b[32m',
    red: '\x1b[31m',
  };

  constructor(private useColors: boolean = true) {
    if (!process.stdout.isTTY) {
      this.useColors = false;
    }
  }

  color(name: keyof typeof this.colors, text: string): string {
    if (!this.useColors) return text;
    return `${this.colors[name]}${text}${this.colors.reset}`;
  }

  bold(text: string): string {
    return this.color('bold', text);
  }

  formatSeverity(severity: string): string {
    const severityColors: Record<string, keyof typeof this.colors> = {
      critical: 'critical',
      high: 'high',
      medium: 'medium',
      low: 'low',
      info: 'info',
    };
    const color = severityColors[severity] ?? 'info';
    return this.color(color, severity.toUpperCase().padEnd(8));
  }

  formatSummary(result: CompleteScanResult): string {
    const s = result.summary;
    const lines: string[] = [];

    lines.push('');
    lines.push(this.bold('═══════════════════════════════════════════════════════════════'));
    lines.push(this.bold('  🔒 Security Scan Results'));
    lines.push(this.bold('═══════════════════════════════════════════════════════════════'));
    lines.push('');
    lines.push(`  ${this.color('dim', 'Target:')}     ${result.metadata.target}`);
    lines.push(`  ${this.color('dim', 'Duration:')}   ${result.metadata.duration}ms`);
    lines.push(`  ${this.color('dim', 'Files:')}      ${result.metadata.filesScanned}`);
    lines.push('');
    lines.push(this.bold('  Vulnerability Summary:'));
    lines.push(`    ${this.formatSeverity('critical')} ${s.bySeverity.critical}`);
    lines.push(`    ${this.formatSeverity('high')} ${s.bySeverity.high}`);
    lines.push(`    ${this.formatSeverity('medium')} ${s.bySeverity.medium}`);
    lines.push(`    ${this.formatSeverity('low')} ${s.bySeverity.low}`);
    lines.push(`    ${this.formatSeverity('info')} ${s.bySeverity.info}`);
    lines.push(`    ────────────────────`);
    lines.push(`    ${this.bold('Total:')}     ${s.totalVulnerabilities}`);
    lines.push('');

    if (s.taintedPaths > 0) {
      lines.push(`  ${this.color('dim', 'Tainted Paths:')}  ${s.taintedPaths}`);
    }
    if (s.secretsFound > 0) {
      lines.push(`  ${this.color('red', '⚠ Secrets Found:')} ${s.secretsFound}`);
    }
    if (s.vulnerableDependencies > 0) {
      lines.push(`  ${this.color('dim', 'Vulnerable Deps:')} ${s.vulnerableDependencies}`);
    }
    if (s.fixesGenerated > 0) {
      lines.push(`  ${this.color('green', '✓ Fixes Generated:')} ${s.fixesGenerated}`);
    }

    lines.push('');
    lines.push(this.bold('═══════════════════════════════════════════════════════════════'));
    lines.push('');

    return lines.join('\n');
  }

  formatVulnerabilities(result: CompleteScanResult): string {
    if (!result.vulnerabilities || result.vulnerabilities.vulnerabilities.length === 0) {
      return this.color('green', '  ✓ No vulnerabilities found\n');
    }

    const lines: string[] = [];
    const vulns = result.vulnerabilities.vulnerabilities;

    lines.push(this.bold('\n  Vulnerabilities:\n'));

    for (const vuln of vulns) {
      lines.push(`  ${this.formatSeverity(vuln.severity)} ${vuln.type}`);
      lines.push(`           ${this.color('dim', vuln.location.file)}:${vuln.location.startLine}`);
      lines.push(`           ${vuln.description}`);
      if (vuln.cwes[0]) {
        lines.push(`           ${this.color('dim', `CWE: ${vuln.cwes[0]}`)}`);
      }
      lines.push('');
    }

    return lines.join('\n');
  }

  formatSecrets(result: CompleteScanResult): string {
    if (!result.secrets || result.secrets.summary.total === 0) {
      return '';
    }

    const lines: string[] = [];
    lines.push(this.bold('\n  ⚠ Secrets Detected:\n'));

    for (const secret of result.secrets.secrets) {
      lines.push(`  ${this.color('red', '•')} ${secret.type}`);
      lines.push(`    ${this.color('dim', secret.location.file)}:${secret.location.startLine}`);
      lines.push(`    Value: ${secret.maskedValue}`);
      lines.push('');
    }

    return lines.join('\n');
  }

  formatFixes(result: CompleteScanResult): string {
    if (!result.fixes || result.fixes.length === 0) {
      return '';
    }

    const lines: string[] = [];
    lines.push(this.bold('\n  Suggested Fixes:\n'));

    for (const fix of result.fixes.slice(0, 5)) { // Show top 5
      lines.push(`  ${this.color('green', '✓')} ${fix.description}`);
      lines.push(`    ${this.color('dim', 'Strategy:')} ${fix.strategy}`);
      lines.push(`    ${this.color('dim', 'File:')} ${fix.edits[0]?.location.file ?? 'N/A'}`);
      lines.push('');
    }

    if (result.fixes.length > 5) {
      lines.push(`  ${this.color('dim', `... and ${result.fixes.length - 5} more`)}`);
    }

    return lines.join('\n');
  }
}

/**
 * Create security CLI command
 */
export function createSecurityCLI(): Command {
  const program = new Command();
  const formatter = new CLIFormatter();

  program
    .name('musubix-security')
    .description('MUSUBIX Security Scanner - Static Analysis & Vulnerability Detection')
    .version('1.8.0');

  // Scan command
  program
    .command('scan [target]')
    .description('Scan target for security vulnerabilities')
    .option('-o, --output <file>', 'Output file for report')
    .option('-f, --format <format>', 'Report format (json|sarif|markdown|html)', 'json')
    .option('--no-vulnerabilities', 'Skip vulnerability scanning')
    .option('--no-taint', 'Skip taint analysis')
    .option('--no-secrets', 'Skip secret detection')
    .option('--no-deps', 'Skip dependency audit')
    .option('--no-fixes', 'Skip fix generation')
    .option('--verify', 'Verify generated fixes')
    .option('-q, --quiet', 'Quiet mode - only output report')
    .option('--json', 'Output JSON to stdout')
    .action(async (target = '.', options) => {
      try {
        const service = createSecurityService();
        const targetPath = path.resolve(target);

        if (!options.quiet) {
          console.log(`\n  Scanning ${targetPath}...\n`);
        }

        const result = await service.scan({
          target: targetPath,
          vulnerabilities: options.vulnerabilities,
          taint: options.taint,
          secrets: options.secrets,
          dependencies: options.deps,
          generateFixes: options.fixes,
          verifyFixes: options.verify,
        });

        if (options.json) {
          console.log(JSON.stringify(result, null, 2));
          return;
        }

        if (!options.quiet) {
          console.log(formatter.formatSummary(result));
          console.log(formatter.formatVulnerabilities(result));
          console.log(formatter.formatSecrets(result));
          console.log(formatter.formatFixes(result));
        }

        if (options.output) {
          const report = await service.generateReport(
            result,
            options.format as ReportFormat
          );
          const fs = await import('node:fs/promises');
          await fs.writeFile(options.output, report, 'utf-8');
          console.log(`  Report saved to: ${options.output}\n`);
        }

        // Exit with error code if critical/high vulnerabilities found
        if (
          result.summary.bySeverity.critical > 0 ||
          result.summary.bySeverity.high > 0
        ) {
          process.exitCode = 1;
        }
      } catch (error: any) {
        console.error(`Error: ${error.message}`);
        process.exitCode = 1;
      }
    });

  // Quick scan command
  program
    .command('quick [target]')
    .description('Quick vulnerability scan (no taint/secrets/deps)')
    .option('--json', 'Output JSON')
    .action(async (target = '.', options) => {
      try {
        const service = createSecurityService();
        const result = await service.quickScan(path.resolve(target));

        if (options.json) {
          console.log(JSON.stringify(result, null, 2));
        } else {
          console.log(`\n  Found ${result.vulnerabilities.length} vulnerabilities\n`);
          for (const vuln of result.vulnerabilities.slice(0, 10)) {
            console.log(`  ${formatter.formatSeverity(vuln.severity)} ${vuln.type}`);
            console.log(`           ${vuln.location.file}:${vuln.location.startLine}\n`);
          }
        }
      } catch (error: any) {
        console.error(`Error: ${error.message}`);
        process.exitCode = 1;
      }
    });

  // Taint analysis command
  program
    .command('taint [target]')
    .description('Run taint analysis')
    .option('--json', 'Output JSON')
    .action(async (target = '.', options) => {
      try {
        const service = createSecurityService();
        const result = await service.analyzeTaint(path.resolve(target));

        if (options.json) {
          console.log(JSON.stringify(result, null, 2));
        } else {
          console.log(`\n  Sources: ${result.sources.length}`);
          console.log(`  Sinks: ${result.sinks.length}`);
          console.log(`  Tainted Paths: ${result.unsafePaths.length}\n`);

          for (const taintPath of result.unsafePaths.slice(0, 5)) {
            console.log(`  Source: ${taintPath.source.variableName ?? taintPath.source.expression} (${taintPath.source.location.file}:${taintPath.source.location.startLine})`);
            console.log(`  → Sink: ${taintPath.sink.functionName} (${taintPath.sink.location.file}:${taintPath.sink.location.startLine})`);
            console.log(`  Sanitized: ${taintPath.sanitized ? 'Yes' : 'No'}\n`);
          }
        }
      } catch (error: any) {
        console.error(`Error: ${error.message}`);
        process.exitCode = 1;
      }
    });

  // Secrets detection command
  program
    .command('secrets [target]')
    .description('Detect hardcoded secrets')
    .option('--json', 'Output JSON')
    .action(async (target = '.', options) => {
      try {
        const service = createSecurityService();
        const result = await service.detectSecrets(path.resolve(target));

        if (options.json) {
          console.log(JSON.stringify(result, null, 2));
        } else {
          console.log(`\n  Secrets Found: ${result.summary.total}\n`);
          for (const secret of result.secrets) {
            console.log(`  ⚠ ${secret.type}`);
            console.log(`    ${secret.location.file}:${secret.location.startLine}`);
            console.log(`    ${secret.maskedValue}\n`);
          }
        }
      } catch (error: any) {
        console.error(`Error: ${error.message}`);
        process.exitCode = 1;
      }
    });

  // Dependency audit command
  program
    .command('audit [target]')
    .description('Audit dependencies for vulnerabilities')
    .option('--json', 'Output JSON')
    .option('--sbom', 'Generate SBOM')
    .action(async (target = '.', options) => {
      try {
        const service = createSecurityService();
        const targetPath = path.resolve(target);

        if (options.sbom) {
          const auditor = new (await import('../analysis/index.js')).DependencyAuditor();
          const sbom = await auditor.generateSBOM(targetPath);
          console.log(JSON.stringify(sbom, null, 2));
          return;
        }

        const result = await service.auditDependencies(targetPath);

        if (options.json) {
          console.log(JSON.stringify(result, null, 2));
        } else {
          console.log(`\n  Vulnerable Dependencies: ${result.vulnerableDependencies.length}\n`);
          for (const dep of result.vulnerableDependencies) {
            console.log(`  ${formatter.formatSeverity(dep.highestSeverity)} ${dep.name}@${dep.installedVersion}`);
            console.log(`           ${dep.vulnerabilities[0]?.title ?? 'N/A'}`);
            if (dep.vulnerabilities[0]?.patchedVersion) {
              console.log(`           Fix: ${dep.vulnerabilities[0].patchedVersion}\n`);
            } else {
              console.log('');
            }
          }
        }
      } catch (error: any) {
        console.error(`Error: ${error.message}`);
        process.exitCode = 1;
      }
    });

  // Fix generation command
  program
    .command('fix [target]')
    .description('Generate fixes for vulnerabilities')
    .option('--verify', 'Verify generated fixes')
    .option('--apply', 'Apply fixes (use with caution)')
    .option('--json', 'Output JSON')
    .action(async (target = '.', options) => {
      try {
        const service = createSecurityService();
        const targetPath = path.resolve(target);

        const scanResult = await service.scan({
          target: targetPath,
          generateFixes: true,
          verifyFixes: options.verify,
        });

        if (!scanResult.fixes || scanResult.fixes.length === 0) {
          console.log('\n  No fixes to generate\n');
          return;
        }

        if (options.json) {
          console.log(JSON.stringify(scanResult.fixes, null, 2));
          return;
        }

        console.log(`\n  Generated ${scanResult.fixes.length} fixes\n`);

        for (const fix of scanResult.fixes) {
          console.log(`  ${fix.description}`);
          console.log(`    Strategy: ${fix.strategy}`);
          if (scanResult.verifications) {
            const verification = scanResult.verifications.find(v => v.fixId === fix.id);
            if (verification) {
              const status = verification.status === 'verified' ? '✓' : '✗';
              console.log(`    Verified: ${status} ${verification.status}`);
            }
          }
          console.log('');
        }

        if (options.apply) {
          console.log('  ⚠ Apply mode not yet implemented');
          console.log('    Please review fixes and apply manually\n');
        }
      } catch (error: any) {
        console.error(`Error: ${error.message}`);
        process.exitCode = 1;
      }
    });

  // Report generation command
  program
    .command('report [target]')
    .description('Generate security report')
    .option('-o, --output <file>', 'Output file (required)')
    .option('-f, --format <format>', 'Format (json|sarif|markdown|html)', 'json')
    .action(async (target = '.', options) => {
      try {
        if (!options.output) {
          console.error('Error: --output is required');
          process.exitCode = 1;
          return;
        }

        const service = createSecurityService();
        const result = await service.scan({ target: path.resolve(target) });
        const report = await service.generateReport(result, options.format as ReportFormat);

        const fs = await import('node:fs/promises');
        await fs.writeFile(options.output, report, 'utf-8');
        console.log(`  Report saved to: ${options.output}`);
      } catch (error: any) {
        console.error(`Error: ${error.message}`);
        process.exitCode = 1;
      }
    });

  // ============================================================================
  // CodeQL-equivalent commands (v3.1.0)
  // ============================================================================

  // Database build command
  program
    .command('database <action> [target]')
    .alias('db')
    .description('CodeDB operations (build|export|import)')
    .option('-o, --output <file>', 'Output file for export')
    .option('-l, --language <lang>', 'Primary language (auto-detect if not specified)')
    .option('--parallel', 'Enable parallel processing', true)
    .action(async (action, target = '.', options) => {
      try {
        const { createCodeDBBuilder } = await import('../codedb/builder.js');
        const { CodeDBSerializer } = await import('../codedb/serializer.js');
        const targetPath = path.resolve(target);

        switch (action) {
          case 'build': {
            console.log(`\n  Building CodeDB for ${targetPath}...\n`);
            const builder = createCodeDBBuilder({ parallel: options.parallel });
            
            builder.onProgress((progress) => {
              process.stdout.write(`\r  Progress: ${progress.filesProcessed}/${progress.totalFiles} files (${progress.progress.toFixed(1)}%)`);
            });

            const result = await builder.build(targetPath);
            console.log('\n');
            console.log(`  ✓ Database built successfully`);
            console.log(`    Files processed: ${result.stats.filesSucceeded}`);
            console.log(`    Errors: ${result.stats.filesFailed}`);
            console.log(`    Duration: ${result.stats.duration}ms\n`);

            if (options.output) {
              const serializer = new CodeDBSerializer();
              const serialized = serializer.serialize(result.database);
              const fs = await import('node:fs/promises');
              await fs.writeFile(options.output, serialized, 'utf-8');
              console.log(`  Database exported to: ${options.output}\n`);
            }
            break;
          }

          case 'export': {
            console.error('  Use: musubix-security database build --output <file>');
            break;
          }

          case 'import': {
            if (!target) {
              console.error('  Error: Database file path required');
              process.exitCode = 1;
              return;
            }
            const { CodeDBSerializer } = await import('../codedb/serializer.js');
            const fs = await import('node:fs/promises');
            const content = await fs.readFile(target, 'utf-8');
            const serializer = new CodeDBSerializer();
            const db = serializer.deserialize(content);
            console.log(`\n  ✓ Database imported successfully`);
            console.log(`    AST nodes: ${db.getStats().astNodes}`);
            console.log(`    DFG nodes: ${db.getStats().dfgNodes}`);
            console.log(`    CFG nodes: ${db.getStats().cfgNodes}\n`);
            break;
          }

          default:
            console.error(`  Unknown action: ${action}`);
            console.error('  Available actions: build, export, import');
            process.exitCode = 1;
        }
      } catch (error: any) {
        console.error(`Error: ${error.message}`);
        process.exitCode = 1;
      }
    });

  // MQL Query command
  program
    .command('query <mql>')
    .alias('q')
    .description('Execute MQL query against CodeDB')
    .option('-d, --database <file>', 'CodeDB file (or build from target)')
    .option('-t, --target <path>', 'Target directory to scan', '.')
    .option('--explain', 'Show query plan')
    .option('--json', 'Output JSON')
    .option('-l, --limit <n>', 'Limit results', '100')
    .action(async (mql, options) => {
      try {
        const { createMQLEngine } = await import('../mql/index.js');
        const { createCodeDBBuilder } = await import('../codedb/builder.js');
        const { CodeDBSerializer } = await import('../codedb/serializer.js');

        let db;

        if (options.database) {
          // Load from file
          const fs = await import('node:fs/promises');
          const content = await fs.readFile(options.database, 'utf-8');
          const serializer = new CodeDBSerializer();
          db = serializer.deserialize(content);
        } else {
          // Build from target
          const targetPath = path.resolve(options.target);
          console.log(`  Building CodeDB from ${targetPath}...\n`);
          const builder = createCodeDBBuilder();
          const result = await builder.build(targetPath);
          db = result.database;
        }

        const engine = createMQLEngine({ maxResults: parseInt(options.limit, 10) });

        if (options.explain) {
          const explanation = engine.explain(mql);
          console.log(explanation);
          return;
        }

        const result = await engine.execute(mql, db);

        if (options.json) {
          console.log(JSON.stringify(result, null, 2));
          return;
        }

        console.log(`\n  Query Results: ${result.rows.length} rows (${result.metadata.executionTime}ms)\n`);
        
        if (result.rows.length === 0) {
          console.log('  No results found.\n');
          return;
        }

        // Display results as table
        const columns = Object.keys(result.rows[0]).filter(k => !k.startsWith('_'));
        console.log('  ' + columns.map(c => c.padEnd(20)).join(' | '));
        console.log('  ' + columns.map(() => '-'.repeat(20)).join('-+-'));

        for (const row of result.rows.slice(0, 20)) {
          const values = columns.map(c => String(row[c] ?? '').substring(0, 20).padEnd(20));
          console.log('  ' + values.join(' | '));
        }

        if (result.rows.length > 20) {
          console.log(`\n  ... and ${result.rows.length - 20} more rows\n`);
        }
        console.log('');
      } catch (error: any) {
        console.error(`Error: ${error.message}`);
        process.exitCode = 1;
      }
    });

  // Variant analysis command
  program
    .command('variant [target]')
    .description('Run variant analysis (CodeQL-style vulnerability detection)')
    .option('-m, --model <ids...>', 'Vulnerability model IDs to check')
    .option('-c, --category <cat>', 'Category filter (injection|secrets|crypto|auth)')
    .option('-s, --severity <level>', 'Minimum severity (critical|high|medium|low|info)', 'info')
    .option('-o, --output <file>', 'Output file')
    .option('-f, --format <format>', 'Output format (json|sarif)', 'json')
    .option('--list-models', 'List available vulnerability models')
    .option('--json', 'Output JSON to stdout')
    .action(async (target = '.', options) => {
      try {
        const { createScanner, createModelManager, exportSARIF } = await import('../variant/index.js');

        if (options.listModels) {
          const manager = createModelManager();
          console.log('\n  Available Vulnerability Models:\n');
          for (const model of manager.getAllModels()) {
            const status = model.enabled ? '✓' : '○';
            console.log(`  ${status} ${model.id.padEnd(25)} ${model.severity.padEnd(8)} ${model.cweId}`);
            console.log(`    ${model.description}\n`);
          }
          return;
        }

        const targetPath = path.resolve(target);
        console.log(`\n  Running variant analysis on ${targetPath}...\n`);

        const scanner = createScanner({
          severityThreshold: options.severity,
          modelIds: options.model,
        });

        scanner.onProgress((progress) => {
          process.stdout.write(`\r  ${progress.phase}: ${progress.message} (${progress.progress.toFixed(0)}%)`);
        });

        const result = await scanner.scan(targetPath);
        console.log('\n');

        if (options.json || options.format === 'json') {
          if (options.output) {
            const fs = await import('node:fs/promises');
            await fs.writeFile(options.output, JSON.stringify(result, null, 2), 'utf-8');
            console.log(`  Report saved to: ${options.output}\n`);
          } else {
            console.log(JSON.stringify(result, null, 2));
          }
          return;
        }

        if (options.format === 'sarif') {
          const sarif = exportSARIF(result);
          if (options.output) {
            const fs = await import('node:fs/promises');
            await fs.writeFile(options.output, sarif, 'utf-8');
            console.log(`  SARIF report saved to: ${options.output}\n`);
          } else {
            console.log(sarif);
          }
          return;
        }

        // Display summary
        console.log('  ═══════════════════════════════════════════════════════════════');
        console.log('  🔍 Variant Analysis Results');
        console.log('  ═══════════════════════════════════════════════════════════════\n');
        console.log(`    Total Findings: ${result.summary.totalFindings}`);
        console.log(`    Critical: ${result.summary.bySeverity.critical}`);
        console.log(`    High: ${result.summary.bySeverity.high}`);
        console.log(`    Medium: ${result.summary.bySeverity.medium}`);
        console.log(`    Low: ${result.summary.bySeverity.low}`);
        console.log(`    Info: ${result.summary.bySeverity.info}`);
        console.log(`    Duration: ${result.metadata.executionTime}ms\n`);

        if (result.findings.length > 0) {
          console.log('  Findings:\n');
          for (const finding of result.findings.slice(0, 10)) {
            console.log(`  ${formatter.formatSeverity(finding.severity)} ${finding.modelName}`);
            console.log(`           ${finding.location.file}:${finding.location.startLine}`);
            console.log(`           ${finding.description}`);
            console.log(`           ${finding.cweId} | Confidence: ${finding.confidence}\n`);
          }
          if (result.findings.length > 10) {
            console.log(`  ... and ${result.findings.length - 10} more findings\n`);
          }
        }

        // Exit code based on findings
        if (result.summary.bySeverity.critical > 0 || result.summary.bySeverity.high > 0) {
          process.exitCode = 1;
        }
      } catch (error: any) {
        console.error(`Error: ${error.message}`);
        process.exitCode = 1;
      }
    });

  // Models management command
  program
    .command('models <action> [id]')
    .description('Manage vulnerability models (list|show|enable|disable)')
    .option('--json', 'Output JSON')
    .action(async (action, id, options) => {
      try {
        const { createModelManager } = await import('../variant/index.js');
        const manager = createModelManager();

        switch (action) {
          case 'list': {
            const models = manager.getAllModels();
            if (options.json) {
              console.log(JSON.stringify(models, null, 2));
              return;
            }
            console.log('\n  Vulnerability Models:\n');
            for (const model of models) {
              const status = model.enabled ? '✓' : '○';
              console.log(`  ${status} ${model.id.padEnd(25)} ${model.severity.padEnd(8)} ${model.cweId}`);
            }
            console.log('');
            break;
          }

          case 'show': {
            if (!id) {
              console.error('  Error: Model ID required');
              process.exitCode = 1;
              return;
            }
            const model = manager.getModel(id);
            if (!model) {
              console.error(`  Error: Model '${id}' not found`);
              process.exitCode = 1;
              return;
            }
            if (options.json) {
              console.log(JSON.stringify(model, null, 2));
              return;
            }
            console.log(`\n  Model: ${model.id}`);
            console.log(`  Name: ${model.name}`);
            console.log(`  CWE: ${model.cweId}`);
            console.log(`  Severity: ${model.severity}`);
            console.log(`  Category: ${model.category}`);
            console.log(`  Description: ${model.description}`);
            console.log(`  Enabled: ${model.enabled}`);
            console.log(`  Sources: ${model.sources.length}`);
            console.log(`  Sinks: ${model.sinks.length}`);
            console.log(`  Sanitizers: ${model.sanitizers.length}\n`);
            break;
          }

          case 'enable': {
            if (!id) {
              console.error('  Error: Model ID required');
              process.exitCode = 1;
              return;
            }
            if (manager.enableModel(id)) {
              console.log(`  ✓ Model '${id}' enabled`);
            } else {
              console.error(`  Error: Model '${id}' not found`);
              process.exitCode = 1;
            }
            break;
          }

          case 'disable': {
            if (!id) {
              console.error('  Error: Model ID required');
              process.exitCode = 1;
              return;
            }
            if (manager.disableModel(id)) {
              console.log(`  ✓ Model '${id}' disabled`);
            } else {
              console.error(`  Error: Model '${id}' not found`);
              process.exitCode = 1;
            }
            break;
          }

          default:
            console.error(`  Unknown action: ${action}`);
            console.error('  Available actions: list, show, enable, disable');
            process.exitCode = 1;
        }
      } catch (error: any) {
        console.error(`Error: ${error.message}`);
        process.exitCode = 1;
      }
    });

  return program;
}

/**
 * Run CLI
 */
export async function runCLI(args: string[] = process.argv): Promise<void> {
  const program = createSecurityCLI();
  await program.parseAsync(args);
}
