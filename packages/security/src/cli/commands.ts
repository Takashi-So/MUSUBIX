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

  return program;
}

/**
 * Run CLI
 */
export async function runCLI(args: string[] = process.argv): Promise<void> {
  const program = createSecurityCLI();
  await program.parseAsync(args);
}
