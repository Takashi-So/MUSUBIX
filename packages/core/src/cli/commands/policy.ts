/**
 * Policy CLI Commands
 * 
 * CLI interface for policy validation operations
 * 
 * @packageDocumentation
 * @module cli/commands/policy
 */

import type { Command } from 'commander';
import {
  createPolicyEngine,
  PolicyEngine,
  ValidationContext,
  PolicyCategory,
} from '@musubix/policy';

// Engine instance
let engine: PolicyEngine | null = null;

function getEngine(): PolicyEngine {
  if (!engine) {
    engine = createPolicyEngine() as PolicyEngine;
  }
  return engine;
}

/**
 * Register policy commands
 */
export function registerPolicyCommands(program: Command): void {
  const policy = program
    .command('policy')
    .description('Validate against policies');

  policy
    .command('validate [path]')
    .description('Validate a project against all registered policies')
    .option('--policy <ids>', 'Comma-separated policy IDs to validate')
    .action(async (projectPath: string | undefined, options: { policy?: string }) => {
      const targetPath = projectPath || process.cwd();
      const policyIds = options.policy ? options.policy.split(',') : undefined;
      
      const engine = getEngine();
      
      const context: ValidationContext = {
        projectPath: targetPath,
      };
      
      console.log(`🔍 Validating project: ${targetPath}\n`);
      
      const report = await engine.validate(context, policyIds);
      
      if (report.passed) {
        console.log('✅ All policies passed!\n');
      } else {
        console.log('❌ Some policies failed:\n');
      }
      
      // Show violations
      for (const violation of report.violations) {
        const icon = violation.severity === 'error' ? '❌' : violation.severity === 'warning' ? '⚠️' : 'ℹ️';
        console.log(`${icon} [${violation.policyId}] ${violation.message}`);
        if (violation.location?.file) {
          console.log(`   📍 ${violation.location.file}:${violation.location.line || 1}`);
        }
        console.log();
      }
      
      // Summary
      console.log('📊 Summary:');
      console.log(`   Total Policies: ${report.totalPolicies}`);
      console.log(`   Passed: ${report.passedPolicies}`);
      console.log(`   Failed: ${report.failedPolicies}`);
      
      if (!report.passed) {
        process.exit(1);
      }
    });

  policy
    .command('list')
    .description('List all registered policies')
    .option('--category <category>', 'Filter by category')
    .action(async (options: { category?: string }) => {
      const engine = getEngine();
      const category = options.category as PolicyCategory | undefined;
      
      const policies = engine.listPolicies(category);
      
      console.log(`📋 Registered Policies${category ? ` (${category})` : ''}:\n`);
      
      for (const p of policies) {
        const severityIcon = p.severity === 'error' ? '🔴' : p.severity === 'warning' ? '🟡' : '🔵';
        console.log(`${severityIcon} ${p.id}: ${p.name}`);
        console.log(`   ${p.description}`);
        console.log(`   Category: ${p.category}`);
        console.log();
      }
      
      console.log(`Total: ${policies.length} policies`);
    });

  policy
    .command('check <file>')
    .description('Check a specific file against relevant policies')
    .action(async (filePath: string) => {
      const fs = await import('node:fs/promises');
      let content: string;
      
      try {
        content = await fs.readFile(filePath, 'utf-8');
      } catch {
        console.error(`❌ Could not read file: ${filePath}`);
        process.exit(1);
      }
      
      const engine = getEngine();
      
      const context: ValidationContext = {
        filePath,
        content,
      };
      
      console.log(`🔍 Checking file: ${filePath}\n`);
      
      // Check EARS format for requirement files
      const policyIds = filePath.toLowerCase().includes('req') ? ['CONST-004'] : undefined;
      const report = await engine.validate(context, policyIds);
      
      if (report.passed) {
        console.log('✅ File passed all checks!');
      } else {
        console.log('❌ Issues found:\n');
        for (const violation of report.violations) {
          console.log(`   ${violation.severity.toUpperCase()}: ${violation.message}`);
        }
      }
    });

  policy
    .command('info <id>')
    .description('Get details of a specific policy')
    .action(async (id: string) => {
      const engine = getEngine();
      const p = engine.getPolicy(id);
      
      if (!p) {
        console.error(`❌ Policy not found: ${id}`);
        process.exit(1);
      }
      
      console.log(`📋 Policy: ${p.id}\n`);
      console.log(`   Name: ${p.name}`);
      console.log(`   Description: ${p.description}`);
      console.log(`   Category: ${p.category}`);
      console.log(`   Severity: ${p.severity}`);
    });
}
