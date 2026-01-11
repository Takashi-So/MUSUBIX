/**
 * Decision CLI Commands
 * 
 * CLI interface for ADR (Architecture Decision Records) operations
 * 
 * @packageDocumentation
 * @module cli/commands/decision
 */

import type { Command } from 'commander';
import * as path from 'node:path';
import {
  createDecisionManager,
  DecisionManager,
  ADRStatus,
} from '@musubix/decisions';

// Manager instance
let manager: DecisionManager | null = null;

function getManager(baseDir?: string): DecisionManager {
  if (!manager || baseDir) {
    const decisionsPath = baseDir || path.join(process.cwd(), 'docs', 'decisions');
    manager = createDecisionManager(decisionsPath) as DecisionManager;
  }
  return manager;
}

/**
 * Register decision commands
 */
export function registerDecisionCommands(program: Command): void {
  const decision = program
    .command('decision')
    .alias('adr')
    .description('Manage Architecture Decision Records');

  decision
    .command('create <title>')
    .description('Create a new Architecture Decision Record')
    .requiredOption('-c, --context <context>', 'Decision context')
    .requiredOption('-d, --decision <decision>', 'Selected decision')
    .option('-r, --rationale <rationale>', 'Rationale for the decision')
    .option('-a, --alternatives <alternatives>', 'Alternatives (comma-separated)')
    .option('--consequences <consequences>', 'Consequences (comma-separated)')
    .option('--requirements <requirements>', 'Related requirements (comma-separated)')
    .option('--decider <decider>', 'Decision maker')
    .option('--base <dir>', 'Base directory for ADR storage')
    .action(async (title: string, options: {
      context: string;
      decision: string;
      rationale?: string;
      alternatives?: string;
      consequences?: string;
      requirements?: string;
      decider?: string;
      base?: string;
    }) => {
      const mgr = getManager(options.base);
      
      const draft = {
        title,
        context: options.context,
        decision: options.decision,
        rationale: options.rationale,
        alternatives: options.alternatives?.split(',').map(s => s.trim()),
        consequences: options.consequences?.split(',').map(s => s.trim()),
        relatedRequirements: options.requirements?.split(',').map(s => s.trim()),
        decider: options.decider,
      };
      
      const adr = await mgr.create(draft);
      
      console.log(`✅ Created ADR-${adr.id}: ${adr.title}`);
      console.log(`   Status: ${adr.status}`);
      console.log(`   File: docs/decisions/${adr.id}-${adr.title.toLowerCase().replace(/\s+/g, '-').replace(/[^a-z0-9-]/g, '')}.md`);
    });

  decision
    .command('list')
    .description('List all Architecture Decision Records')
    .option('-s, --status <status>', 'Filter by status')
    .option('-k, --keyword <keyword>', 'Filter by keyword')
    .option('--base <dir>', 'Base directory for ADR storage')
    .action(async (options: { status?: string; keyword?: string; base?: string }) => {
      const mgr = getManager(options.base);
      
      const adrs = await mgr.list({
        status: options.status as ADRStatus | undefined,
        keyword: options.keyword,
      });
      
      console.log(`📋 Architecture Decision Records (${adrs.length}):\n`);
      
      for (const adr of adrs) {
        const statusIcon = adr.status === 'accepted' ? '✅' : 
                           adr.status === 'proposed' ? '📝' : 
                           adr.status === 'deprecated' ? '⚠️' : '🔄';
        console.log(`${statusIcon} ADR-${adr.id}: ${adr.title}`);
        console.log(`   Status: ${adr.status} | Date: ${adr.date}`);
      }
    });

  decision
    .command('get <id>')
    .description('Get details of a specific ADR')
    .option('--base <dir>', 'Base directory for ADR storage')
    .action(async (id: string, options: { base?: string }) => {
      const mgr = getManager(options.base);
      const adr = await mgr.get(id);
      
      if (!adr) {
        console.error(`❌ ADR not found: ${id}`);
        process.exit(1);
      }
      
      console.log(`📋 ADR-${adr.id}: ${adr.title}\n`);
      console.log(`Status: ${adr.status}`);
      console.log(`Date: ${adr.date}`);
      if (adr.decider) {
        console.log(`Decider: ${adr.decider}`);
      }
      console.log(`\n## Context\n${adr.context}`);
      console.log(`\n## Decision\n${adr.decision}`);
      if (adr.rationale) {
        console.log(`\n## Rationale\n${adr.rationale}`);
      }
      if (adr.alternatives?.length) {
        console.log(`\n## Alternatives\n${adr.alternatives.map(a => `- ${a}`).join('\n')}`);
      }
      if (adr.consequences?.length) {
        console.log(`\n## Consequences\n${adr.consequences.map(c => `- ${c}`).join('\n')}`);
      }
    });

  decision
    .command('accept <id>')
    .description('Accept a proposed ADR')
    .option('--base <dir>', 'Base directory for ADR storage')
    .action(async (id: string, options: { base?: string }) => {
      const mgr = getManager(options.base);
      
      try {
        const adr = await mgr.accept(id);
        console.log(`✅ Accepted ADR-${adr.id}: ${adr.title}`);
      } catch (error) {
        console.error(`❌ Error: ${(error as Error).message}`);
        process.exit(1);
      }
    });

  decision
    .command('deprecate <id>')
    .description('Deprecate an ADR')
    .option('--superseded-by <id>', 'ID of superseding ADR')
    .option('--base <dir>', 'Base directory for ADR storage')
    .action(async (id: string, options: { 'superseded-by'?: string; base?: string }) => {
      const mgr = getManager(options.base);
      const supersededBy = options['superseded-by'];
      
      try {
        const adr = await mgr.deprecate(id, supersededBy);
        if (supersededBy) {
          console.log(`🔄 ADR-${adr.id} superseded by ADR-${supersededBy}`);
        } else {
          console.log(`⚠️ Deprecated ADR-${adr.id}: ${adr.title}`);
        }
      } catch (error) {
        console.error(`❌ Error: ${(error as Error).message}`);
        process.exit(1);
      }
    });

  decision
    .command('search <query>')
    .description('Search ADRs by keyword')
    .option('--base <dir>', 'Base directory for ADR storage')
    .action(async (query: string, options: { base?: string }) => {
      const mgr = getManager(options.base);
      const adrs = await mgr.search(query);
      
      console.log(`🔍 Search results for "${query}" (${adrs.length}):\n`);
      
      for (const adr of adrs) {
        console.log(`  ADR-${adr.id}: ${adr.title}`);
      }
    });

  decision
    .command('index')
    .description('Generate or update the ADR index file')
    .option('--base <dir>', 'Base directory for ADR storage')
    .action(async (options: { base?: string }) => {
      const mgr = getManager(options.base);
      await mgr.generateIndex();
      
      console.log('✅ Generated docs/decisions/index.md');
    });
}
