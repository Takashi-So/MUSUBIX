#!/usr/bin/env node
/**
 * @nahisaho/musubix-codegraph CLI
 *
 * Command-line interface for CodeGraph operations
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-codegraph/cli
 *
 * @see REQ-CG-PR-009 - CLI Integration
 */

import { program } from 'commander';
import { readFileSync, existsSync } from 'node:fs';
import { resolve } from 'node:path';

// Read package.json for version
const packageJsonPath = new URL('../package.json', import.meta.url);
const packageJson = JSON.parse(readFileSync(packageJsonPath, 'utf-8'));

program
  .name('cg')
  .description('MUSUBIX CodeGraph - Code Graph Analysis CLI')
  .version(packageJson.version);

// ============================================================================
// Index Command (v2.3.4 NEW)
// @see REQ-CG-v234-002, DES-CG-v234-002, TSK-v234-005
// ============================================================================

program
  .command('index <path>')
  .description('Index a codebase for graph analysis')
  .option('-d, --depth <n>', 'Maximum directory depth (for future use)', '3')
  .option('--json', 'Output as JSON')
  .option('--languages <langs>', 'Target languages (comma-separated, for future use)')
  .action(async (targetPath, options) => {
    try {
      const { CodeGraph } = await import('./codegraph.js');
      const resolvedPath = resolve(targetPath);
      const cg = new CodeGraph({ storage: 'memory' });

      console.log(`🔍 Indexing ${resolvedPath}...`);

      const startTime = Date.now();
      const result = await cg.index(resolvedPath);
      const elapsed = ((Date.now() - startTime) / 1000).toFixed(2);

      if (options.json) {
        console.log(JSON.stringify({ 
          success: result.success, 
          entitiesIndexed: result.entitiesIndexed,
          relationsIndexed: result.relationsIndexed,
          filesProcessed: result.filesProcessed,
          durationMs: result.durationMs,
          elapsedSeconds: parseFloat(elapsed) 
        }, null, 2));
      } else {
        console.log(`✅ Indexing complete in ${elapsed}s`);
        console.log(`   Entities: ${result.entitiesIndexed}`);
        console.log(`   Relations: ${result.relationsIndexed}`);
        console.log(`   Files: ${result.filesProcessed}`);
      }

      await cg.close();
    } catch (error) {
      console.error('❌ Error:', error instanceof Error ? error.message : error);
      process.exit(1);
    }
  });

// ============================================================================
// Query Command (v2.3.4 NEW)
// @see REQ-CG-v234-002, DES-CG-v234-002, TSK-v234-006
// ============================================================================

program
  .command('query <query>')
  .description('Query entities in the code graph')
  .option('--type <type>', 'Entity type filter (function, class, method, etc.)')
  .option('--limit <n>', 'Maximum results', '10')
  .option('--json', 'Output as JSON')
  .action(async (queryText, options) => {
    try {
      const { CodeGraph } = await import('./codegraph.js');
      const cg = new CodeGraph({ storage: 'memory' });

      const limit = parseInt(options.limit, 10);
      
      // Build query object
      const graphQuery = options.type 
        ? { textSearch: queryText, entityType: options.type, limit }
        : { textSearch: queryText, limit };
      
      const result = await cg.query(graphQuery);

      if (options.json) {
        console.log(JSON.stringify(result, null, 2));
      } else {
        if (result.entities.length === 0) {
          console.log(`No entities found for "${queryText}"`);
        } else {
          console.log(`Found ${result.entities.length} entities (total: ${result.totalCount}):`);
          result.entities.slice(0, limit).forEach((e, i) => {
            console.log(`  ${i + 1}. ${e.name} (${e.type})${e.filePath ? ` - ${e.filePath}` : ''}`);
          });
          if (result.hasMore) {
            console.log(`  ... and ${result.totalCount - result.entities.length} more`);
          }
        }
      }

      await cg.close();
    } catch (error) {
      console.error('❌ Error:', error instanceof Error ? error.message : error);
      process.exit(1);
    }
  });

// ============================================================================
// Stats Command (v2.3.4 NEW)
// @see REQ-CG-v234-002, DES-CG-v234-002, TSK-v234-007
// ============================================================================

program
  .command('stats')
  .description('Show code graph statistics')
  .option('--json', 'Output as JSON')
  .action(async (options) => {
    try {
      const { CodeGraph } = await import('./codegraph.js');
      const cg = new CodeGraph({ storage: 'memory' });

      const stats = await cg.getStats();

      if (options.json) {
        console.log(JSON.stringify(stats, null, 2));
      } else {
        console.log('📊 Graph Statistics:');
        console.log(`   Entities: ${stats.entityCount}`);
        console.log(`   Relations: ${stats.relationCount}`);
        console.log(`   Files: ${stats.fileCount}`);
        if (stats.languages && stats.languages.length > 0) {
          console.log(`   Languages: ${stats.languages.join(', ')}`);
        }
      }

      await cg.close();
    } catch (error) {
      console.error('❌ Error:', error instanceof Error ? error.message : error);
      process.exit(1);
    }
  });

// ============================================================================
// PR Commands
// ============================================================================

const prCommand = program
  .command('pr')
  .description('PR creation from refactoring suggestions');

/**
 * cg pr create
 */
prCommand
  .command('create <suggestionFile>')
  .description('Create a PR from a refactoring suggestion JSON file')
  .option('-b, --branch <name>', 'Custom branch name')
  .option('-t, --title <title>', 'Custom PR title')
  .option('--base <branch>', 'Base branch (default: main/master)')
  .option('-l, --labels <labels>', 'Comma-separated labels')
  .option('-r, --reviewers <reviewers>', 'Comma-separated reviewers')
  .option('-a, --assignees <assignees>', 'Comma-separated assignees')
  .option('--draft', 'Create as draft PR')
  .option('--dry-run', 'Preview changes without creating PR')
  .option('--repo <path>', 'Repository path (default: current directory)')
  .action(async (suggestionFile, options) => {
    try {
      const { createPRCreator } = await import('./pr/index.js');

      // Read suggestion file
      const filePath = resolve(suggestionFile);
      if (!existsSync(filePath)) {
        console.error(`❌ Suggestion file not found: ${filePath}`);
        process.exit(1);
      }

      const suggestion = JSON.parse(readFileSync(filePath, 'utf-8'));
      const repoPath = options.repo ?? process.cwd();

      console.log('🚀 Initializing PR Creator...');
      const creator = createPRCreator(repoPath);

      // Event listeners for progress
      creator.on('pr:start', () => console.log('📋 Starting PR creation...'));
      creator.on('pr:branch', ({ name }) => console.log(`🌿 Creating branch: ${name}`));
      creator.on('pr:applying', ({ file }) => console.log(`📝 Applying changes to: ${file}`));
      creator.on('pr:commit', ({ message }) => console.log(`💾 Committing: ${message.split('\n')[0]}`));
      creator.on('pr:push', ({ branch }) => console.log(`⬆️  Pushing branch: ${branch}`));
      creator.on('pr:created', ({ pr }) => console.log(`✅ PR created: ${pr.url}`));

      const initResult = await creator.initialize();
      if (!initResult.success) {
        console.error(`❌ Initialization failed: ${initResult.error}`);
        process.exit(1);
      }

      const result = await creator.create({
        suggestion,
        branchName: options.branch,
        title: options.title,
        baseBranch: options.base,
        labels: options.labels?.split(',').map((s: string) => s.trim()),
        reviewers: options.reviewers?.split(',').map((s: string) => s.trim()),
        assignees: options.assignees?.split(',').map((s: string) => s.trim()),
        draft: options.draft,
        dryRun: options.dryRun,
      });

      if (result.success) {
        if (options.dryRun) {
          console.log('\n📋 Dry Run Preview:');
          console.log(`   Branch: ${result.branchName}`);
          console.log(`   Files: ${result.filesChanged.length}`);
          console.log(`   +${result.linesAdded} / -${result.linesDeleted} lines`);
          if (result.preview) {
            console.log(`\n📝 PR Title: ${result.preview.title}`);
            console.log(`\n📄 Commit Message:\n${result.preview.commitMessage}`);
          }
        } else {
          console.log('\n🎉 PR created successfully!');
          console.log(`   URL: ${result.pr?.url}`);
          console.log(`   Branch: ${result.branchName}`);
          console.log(`   Commit: ${result.commitHash}`);
        }
      } else {
        console.error(`\n❌ PR creation failed: ${result.error}`);
        process.exit(1);
      }

      if (result.warnings && result.warnings.length > 0) {
        console.log('\n⚠️  Warnings:');
        result.warnings.forEach(w => console.log(`   - ${w}`));
      }
    } catch (error) {
      console.error('❌ Error:', error instanceof Error ? error.message : error);
      process.exit(1);
    }
  });

/**
 * cg pr preview
 * 
 * Uses initializeOffline() for GitHub-auth-free preview (v2.3.4)
 * @see REQ-CG-v234-001, DES-CG-v234-001
 */
prCommand
  .command('preview <suggestionFile>')
  .description('Preview PR changes without creating')
  .option('--repo <path>', 'Repository path (default: current directory)')
  .option('--json', 'Output as JSON')
  .action(async (suggestionFile, options) => {
    try {
      const { createPRCreator } = await import('./pr/index.js');

      // Read suggestion file
      const filePath = resolve(suggestionFile);
      if (!existsSync(filePath)) {
        console.error(`❌ Suggestion file not found: ${filePath}`);
        process.exit(1);
      }

      const suggestion = JSON.parse(readFileSync(filePath, 'utf-8'));
      const repoPath = options.repo ?? process.cwd();

      const creator = createPRCreator(repoPath);
      
      // v2.3.4: Use initializeOffline() for preview (no GitHub auth required)
      const initResult = await creator.initializeOffline();
      if (!initResult.success) {
        console.error(`❌ Initialization failed: ${initResult.error}`);
        process.exit(1);
      }

      // v2.3.4: Use previewSuggestion() instead of preview() (sync function)
      const preview = creator.previewSuggestion(suggestion);

      if (options.json) {
        console.log(JSON.stringify(preview, null, 2));
      } else {
        console.log('📋 PR Preview\n');
        console.log(`Branch: ${preview.branchName}`);
        console.log(`Title: ${preview.title}`);
        console.log(`\n📝 Commit Message:\n${preview.commitMessage}`);
        console.log(`\n📄 Files Changed (${preview.diffs.length}):`);
        for (const diff of preview.diffs) {
          console.log(`  ${diff.changeType === 'added' ? '➕' : '📝'} ${diff.filePath} (+${diff.additions}/-${diff.deletions})`);
        }
        console.log('\n📋 PR Body Preview:\n');
        console.log(preview.body.slice(0, 500) + (preview.body.length > 500 ? '...' : ''));
      }
    } catch (error) {
      console.error('❌ Error:', error instanceof Error ? error.message : error);
      process.exit(1);
    }
  });

/**
 * cg pr validate
 */
prCommand
  .command('validate <suggestionFile>')
  .description('Validate that a suggestion can be applied')
  .option('--repo <path>', 'Repository path (default: current directory)')
  .action(async (suggestionFile, options) => {
    try {
      const { createPRCreator } = await import('./pr/index.js');

      // Read suggestion file
      const filePath = resolve(suggestionFile);
      if (!existsSync(filePath)) {
        console.error(`❌ Suggestion file not found: ${filePath}`);
        process.exit(1);
      }

      const suggestion = JSON.parse(readFileSync(filePath, 'utf-8'));
      const repoPath = options.repo ?? process.cwd();

      const creator = createPRCreator(repoPath);
      const initResult = await creator.initialize();
      if (!initResult.success) {
        console.error(`❌ Initialization failed: ${initResult.error}`);
        process.exit(1);
      }

      const result = creator.validate(suggestion);

      if (result.valid) {
        console.log('✅ Suggestion is valid and can be applied');
      } else {
        console.error(`❌ Suggestion validation failed: ${result.reason}`);
        process.exit(1);
      }
    } catch (error) {
      console.error('❌ Error:', error instanceof Error ? error.message : error);
      process.exit(1);
    }
  });

// ============================================================================
// Parse and Execute
// ============================================================================

program.parse();
