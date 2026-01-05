/**
 * KGPR CLI Commands
 *
 * Knowledge Graph Pull Request commands for musubix CLI
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-core/cli/commands
 */

import { Command } from 'commander';
import chalk from 'chalk';
import ora from 'ora';

/**
 * Register KGPR commands
 */
export function registerKgprCommands(program: Command): void {
  const kgpr = program
    .command('kgpr')
    .description('Knowledge Graph Pull Request (KGPR) commands - share knowledge with the community');

  // kgpr create
  kgpr
    .command('create')
    .description('Create a new KGPR from local knowledge graph')
    .requiredOption('-t, --title <title>', 'KGPR title')
    .option('-d, --description <desc>', 'Description of the knowledge being shared')
    .option('-n, --namespace <ns>', 'Source namespace to include')
    .option('-l, --labels <labels>', 'Comma-separated labels', (val) => val.split(','))
    .option('-e, --entity-types <types>', 'Filter entity types (comma-separated)', (val) => val.split(','))
    .option('-p, --privacy <level>', 'Privacy level: strict, moderate, none', 'moderate')
    .option('--db <path>', 'YATA Local database path', './yata-local.db')
    .option('--auto-submit', 'Automatically submit after creation')
    .action(async (options) => {
      const spinner = ora('Creating KGPR...').start();

      try {
        // Dynamic imports
        let yataLocalModule: typeof import('@nahisaho/yata-local') | null = null;
        let yataGlobalModule: typeof import('@nahisaho/yata-global') | null = null;

        try {
          yataLocalModule = await import('@nahisaho/yata-local');
        } catch {
          spinner.fail('YATA Local not installed. Run: npm install @nahisaho/yata-local');
          return;
        }

        try {
          yataGlobalModule = await import('@nahisaho/yata-global');
        } catch {
          spinner.fail('YATA Global not installed. Run: npm install @nahisaho/yata-global');
          return;
        }

        const { createYataLocal } = yataLocalModule;
        const { createKGPRManager } = yataGlobalModule;

        const yataLocal = createYataLocal({ path: options.db });
        await yataLocal.open();

        try {
          const kgprManager = createKGPRManager();

          // Build entity map for relationship lookup
          const buildEntityMap = async () => {
            const result = await yataLocal.query({});
            const map = new Map<string, { name: string; namespace: string }>();
            for (const e of result.entities) {
              map.set(e.id, { name: e.name, namespace: e.namespace ?? 'default' });
            }
            return map;
          };

          // Connect adapter
          kgprManager.connectLocalKG({
            queryEntities: async (ns?: string) => {
              const result = await yataLocal.query({
                entityFilters: ns ? { namespace: ns } : undefined,
              });
              return result.entities.map((e) => ({
                id: e.id,
                name: e.name,
                type: e.type,
                namespace: e.namespace ?? 'default',
                filePath: e.metadata?.filePath as string | undefined,
                line: e.metadata?.line as number | undefined,
                metadata: e.metadata,
              }));
            },
            queryRelationships: async (ns?: string) => {
              const result = await yataLocal.query({
                entityFilters: ns ? { namespace: ns } : undefined,
              });
              const entityMap = await buildEntityMap();
              return result.relationships.map((r) => {
                const source = entityMap.get(r.sourceId) ?? { name: r.sourceId, namespace: 'unknown' };
                const target = entityMap.get(r.targetId) ?? { name: r.targetId, namespace: 'unknown' };
                return {
                  id: r.id,
                  sourceName: source.name,
                  sourceNamespace: source.namespace,
                  targetName: target.name,
                  targetNamespace: target.namespace,
                  type: r.type,
                  metadata: r.metadata,
                };
              });
            },
          });

          const kgpr = await kgprManager.create({
            title: options.title,
            description: options.description,
            sourceNamespace: options.namespace,
            labels: options.labels,
            entityTypes: options.entityTypes,
            privacyLevel: options.privacy,
            autoSubmit: options.autoSubmit,
          });

          spinner.succeed(`KGPR created: ${chalk.cyan(kgpr.id)}`);
          console.log();
          console.log(chalk.bold('📋 KGPR Details:'));
          console.log(`  ${chalk.gray('Title:')} ${kgpr.title}`);
          console.log(`  ${chalk.gray('Status:')} ${chalk.yellow(kgpr.status)}`);
          console.log(`  ${chalk.gray('Namespace:')} ${kgpr.sourceNamespace}`);
          console.log();
          console.log(chalk.bold('📊 Changes:'));
          console.log(`  ${chalk.green('+')} ${kgpr.diff.stats.entitiesAdded} entities`);
          console.log(`  ${chalk.green('+')} ${kgpr.diff.stats.relationshipsAdded} relationships`);
          console.log(`  ${chalk.gray('Total:')} ${kgpr.diff.stats.totalChanges} changes`);

          if (kgpr.status === 'draft') {
            console.log();
            console.log(chalk.dim(`Use ${chalk.cyan('musubix kgpr submit ' + kgpr.id)} to submit for review.`));
          }
        } finally {
          await yataLocal.close();
        }
      } catch (error) {
        spinner.fail(`Failed to create KGPR: ${error instanceof Error ? error.message : error}`);
        process.exitCode = 1;
      }
    });

  // kgpr diff
  kgpr
    .command('diff')
    .description('Preview knowledge graph diff before creating KGPR')
    .option('-n, --namespace <ns>', 'Source namespace to include')
    .option('-e, --entity-types <types>', 'Filter entity types (comma-separated)', (val) => val.split(','))
    .option('-p, --privacy <level>', 'Privacy level: strict, moderate, none', 'moderate')
    .option('--db <path>', 'YATA Local database path', './yata-local.db')
    .action(async (options) => {
      const spinner = ora('Generating diff preview...').start();

      try {
        let yataLocalModule: typeof import('@nahisaho/yata-local') | null = null;
        let yataGlobalModule: typeof import('@nahisaho/yata-global') | null = null;

        try {
          yataLocalModule = await import('@nahisaho/yata-local');
        } catch {
          spinner.fail('YATA Local not installed');
          return;
        }

        try {
          yataGlobalModule = await import('@nahisaho/yata-global');
        } catch {
          spinner.fail('YATA Global not installed');
          return;
        }

        const { createYataLocal } = yataLocalModule;
        const { createKGPRManager } = yataGlobalModule;

        const yataLocal = createYataLocal({ path: options.db });
        await yataLocal.open();

        try {
          const kgprManager = createKGPRManager();

          // Build entity map for relationship lookup
          const buildEntityMapForDiff = async () => {
            const result = await yataLocal.query({});
            const map = new Map<string, { name: string; namespace: string }>();
            for (const e of result.entities) {
              map.set(e.id, { name: e.name, namespace: e.namespace ?? 'default' });
            }
            return map;
          };

          kgprManager.connectLocalKG({
            queryEntities: async (ns?: string) => {
              const result = await yataLocal.query({
                entityFilters: ns ? { namespace: ns } : undefined,
              });
              return result.entities.map((e) => ({
                id: e.id,
                name: e.name,
                type: e.type,
                namespace: e.namespace ?? 'default',
                filePath: e.metadata?.filePath as string | undefined,
                line: e.metadata?.line as number | undefined,
                metadata: e.metadata,
              }));
            },
            queryRelationships: async (ns?: string) => {
              const result = await yataLocal.query({
                entityFilters: ns ? { namespace: ns } : undefined,
              });
              const entityMap = await buildEntityMapForDiff();
              return result.relationships.map((r) => {
                const source = entityMap.get(r.sourceId) ?? { name: r.sourceId, namespace: 'default' };
                const target = entityMap.get(r.targetId) ?? { name: r.targetId, namespace: 'default' };
                return {
                  id: r.id,
                  sourceName: source.name,
                  sourceNamespace: source.namespace,
                  targetName: target.name,
                  targetNamespace: target.namespace,
                  type: r.type,
                  metadata: r.metadata,
                };
              });
            },
          });

          const diff = await kgprManager.previewDiff({
            sourceNamespace: options.namespace,
            entityTypes: options.entityTypes,
            privacyLevel: options.privacy,
          });

          spinner.succeed('Diff preview generated');
          console.log();

          console.log(chalk.bold('📊 Statistics:'));
          console.log(`  ${chalk.green('+')} ${diff.stats.entitiesAdded} entities to add`);
          console.log(`  ${chalk.green('+')} ${diff.stats.relationshipsAdded} relationships to add`);
          console.log(`  ${chalk.gray('Total:')} ${diff.stats.totalChanges} changes`);
          console.log();

          if (diff.entities.added.length > 0) {
            console.log(chalk.bold('📦 Entities:'));
            const displayCount = Math.min(diff.entities.added.length, 15);
            for (let i = 0; i < displayCount; i++) {
              const e = diff.entities.added[i];
              console.log(`  ${chalk.green('+')} ${chalk.cyan(e.name)} ${chalk.gray(`(${e.entityType})`)} ${chalk.dim(e.namespace)}`);
            }
            if (diff.entities.added.length > 15) {
              console.log(chalk.dim(`  ... and ${diff.entities.added.length - 15} more`));
            }
            console.log();
          }

          if (diff.relationships.added.length > 0) {
            console.log(chalk.bold('🔗 Relationships:'));
            const displayCount = Math.min(diff.relationships.added.length, 10);
            for (let i = 0; i < displayCount; i++) {
              const r = diff.relationships.added[i];
              console.log(`  ${chalk.green('+')} ${r.sourceName} ${chalk.yellow(`--${r.relationshipType}-->`)} ${r.targetName}`);
            }
            if (diff.relationships.added.length > 10) {
              console.log(chalk.dim(`  ... and ${diff.relationships.added.length - 10} more`));
            }
          }

          console.log();
          console.log(chalk.dim(`Privacy level: ${options.privacy}`));
        } finally {
          await yataLocal.close();
        }
      } catch (error) {
        spinner.fail(`Failed: ${error instanceof Error ? error.message : error}`);
        process.exitCode = 1;
      }
    });

  // kgpr list
  kgpr
    .command('list')
    .alias('ls')
    .description('List KGPRs')
    .option('-s, --status <status>', 'Filter by status')
    .option('-q, --search <query>', 'Search query')
    .option('-l, --labels <labels>', 'Filter by labels (comma-separated)', (val) => val.split(','))
    .option('--limit <n>', 'Maximum results', '20')
    .action(async (options) => {
      try {
        let yataGlobalModule: typeof import('@nahisaho/yata-global') | null = null;

        try {
          yataGlobalModule = await import('@nahisaho/yata-global');
        } catch {
          console.log(chalk.red('YATA Global not installed'));
          return;
        }

        const { createKGPRManager } = yataGlobalModule;
        const kgprManager = createKGPRManager();

        const result = await kgprManager.list({
          status: options.status,
          search: options.search,
          labels: options.labels,
          limit: parseInt(options.limit),
        });

        if (result.kgprs.length === 0) {
          console.log(chalk.yellow('No KGPRs found.'));
          console.log(chalk.dim(`Use ${chalk.cyan('musubix kgpr create')} to create one.`));
          return;
        }

        console.log(chalk.bold(`📋 KGPRs (${result.total} total)`));
        console.log();

        for (const kgpr of result.kgprs) {
          const statusColor = {
            draft: chalk.gray,
            open: chalk.blue,
            reviewing: chalk.yellow,
            approved: chalk.green,
            changes_requested: chalk.red,
            merged: chalk.magenta,
            closed: chalk.gray,
          }[kgpr.status] || chalk.white;

          console.log(`${chalk.cyan(kgpr.id)} ${statusColor(`[${kgpr.status}]`)}`);
          console.log(`  ${chalk.bold(kgpr.title)}`);
          console.log(`  ${chalk.gray('by')} ${kgpr.authorName} ${chalk.gray('•')} ${kgpr.diff.stats.totalChanges} changes`);
          if (kgpr.labels.length > 0) {
            console.log(`  ${kgpr.labels.map(l => chalk.cyan(`#${l}`)).join(' ')}`);
          }
          console.log();
        }
      } catch (error) {
        console.log(chalk.red(`Error: ${error instanceof Error ? error.message : error}`));
        process.exitCode = 1;
      }
    });

  // kgpr submit
  kgpr
    .command('submit <id>')
    .description('Submit a draft KGPR for review')
    .action(async (id) => {
      const spinner = ora('Submitting KGPR...').start();

      try {
        let yataGlobalModule: typeof import('@nahisaho/yata-global') | null = null;

        try {
          yataGlobalModule = await import('@nahisaho/yata-global');
        } catch {
          spinner.fail('YATA Global not installed');
          return;
        }

        const { createKGPRManager } = yataGlobalModule;
        const kgprManager = createKGPRManager();

        const result = await kgprManager.submit(id);

        if (!result.success) {
          spinner.fail(`Failed to submit: ${result.error}`);
          return;
        }

        spinner.succeed(`KGPR submitted: ${chalk.cyan(result.kgprId)}`);

        if (result.kgprUrl) {
          console.log(`  ${chalk.gray('URL:')} ${result.kgprUrl}`);
        }

        if (result.qualityScore !== undefined) {
          const scoreColor = result.qualityScore >= 80 ? chalk.green : result.qualityScore >= 50 ? chalk.yellow : chalk.red;
          console.log(`  ${chalk.gray('Quality Score:')} ${scoreColor(result.qualityScore + '/100')}`);
        }

        if (result.duplicateWarnings && result.duplicateWarnings.length > 0) {
          console.log();
          console.log(chalk.yellow(`⚠️  ${result.duplicateWarnings.length} potential duplicate(s) detected:`));
          for (const warning of result.duplicateWarnings.slice(0, 3)) {
            console.log(`  ${warning.localEntityName} ↔ ${warning.globalEntityName} (${(warning.similarity * 100).toFixed(0)}% similar)`);
          }
        }
      } catch (error) {
        spinner.fail(`Error: ${error instanceof Error ? error.message : error}`);
        process.exitCode = 1;
      }
    });

  // kgpr show
  kgpr
    .command('show <id>')
    .description('Show details of a KGPR')
    .action(async (id) => {
      try {
        let yataGlobalModule: typeof import('@nahisaho/yata-global') | null = null;

        try {
          yataGlobalModule = await import('@nahisaho/yata-global');
        } catch {
          console.log(chalk.red('YATA Global not installed'));
          return;
        }

        const { createKGPRManager } = yataGlobalModule;
        const kgprManager = createKGPRManager();

        const kgpr = await kgprManager.get(id);

        if (!kgpr) {
          console.log(chalk.red(`KGPR not found: ${id}`));
          return;
        }

        const statusColor = {
          draft: chalk.gray,
          open: chalk.blue,
          reviewing: chalk.yellow,
          approved: chalk.green,
          changes_requested: chalk.red,
          merged: chalk.magenta,
          closed: chalk.gray,
        }[kgpr.status] || chalk.white;

        console.log(chalk.bold(`📋 KGPR: ${kgpr.title}`));
        console.log(`${chalk.gray('ID:')} ${chalk.cyan(kgpr.id)}`);
        console.log(`${chalk.gray('Status:')} ${statusColor(kgpr.status)}`);
        console.log(`${chalk.gray('Author:')} ${kgpr.authorName}`);
        console.log(`${chalk.gray('Namespace:')} ${kgpr.sourceNamespace}`);
        console.log(`${chalk.gray('Created:')} ${kgpr.createdAt}`);

        if (kgpr.labels.length > 0) {
          console.log(`${chalk.gray('Labels:')} ${kgpr.labels.map(l => chalk.cyan(`#${l}`)).join(' ')}`);
        }

        console.log();
        if (kgpr.description) {
          console.log(kgpr.description);
          console.log();
        }

        console.log(chalk.bold('📊 Changes:'));
        console.log(`  ${chalk.green('+')} ${kgpr.diff.stats.entitiesAdded} entities`);
        console.log(`  ${chalk.yellow('~')} ${kgpr.diff.stats.entitiesUpdated} updated`);
        console.log(`  ${chalk.red('-')} ${kgpr.diff.stats.entitiesDeleted} deleted`);
        console.log(`  ${chalk.green('+')} ${kgpr.diff.stats.relationshipsAdded} relationships`);

        if (kgpr.reviews.length > 0) {
          console.log();
          console.log(chalk.bold(`💬 Reviews (${kgpr.reviews.length}):`));
          for (const review of kgpr.reviews) {
            const reviewColor = {
              approved: chalk.green,
              changes_requested: chalk.red,
              commented: chalk.gray,
            }[review.status];
            console.log(`  ${reviewColor(review.status)} by ${review.reviewerName}`);
          }
        }

        if (kgpr.qualityScore !== undefined) {
          console.log();
          const scoreColor = kgpr.qualityScore >= 80 ? chalk.green : kgpr.qualityScore >= 50 ? chalk.yellow : chalk.red;
          console.log(`${chalk.gray('Quality Score:')} ${scoreColor(kgpr.qualityScore + '/100')}`);
        }
      } catch (error) {
        console.log(chalk.red(`Error: ${error instanceof Error ? error.message : error}`));
        process.exitCode = 1;
      }
    });

  // kgpr close
  kgpr
    .command('close <id>')
    .description('Close a KGPR without merging')
    .option('-r, --reason <reason>', 'Reason for closing')
    .action(async (id, options) => {
      const spinner = ora('Closing KGPR...').start();

      try {
        let yataGlobalModule: typeof import('@nahisaho/yata-global') | null = null;

        try {
          yataGlobalModule = await import('@nahisaho/yata-global');
        } catch {
          spinner.fail('YATA Global not installed');
          return;
        }

        const { createKGPRManager } = yataGlobalModule;
        const kgprManager = createKGPRManager();

        const success = await kgprManager.close(id, options.reason);

        if (success) {
          spinner.succeed(`KGPR closed: ${chalk.cyan(id)}`);
        } else {
          spinner.fail('Failed to close KGPR');
        }
      } catch (error) {
        spinner.fail(`Error: ${error instanceof Error ? error.message : error}`);
        process.exitCode = 1;
      }
    });
}
