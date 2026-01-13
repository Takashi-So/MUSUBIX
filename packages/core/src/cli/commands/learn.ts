/**
 * Learn Command - Self-Learning System CLI
 *
 * CLI commands for managing the self-learning system
 *
 * @see REQ-LEARN-001〜006 - Learning Requirements
 * @see REQ-CLI-007 - Learning CLI
 * @module cli/commands/learn
 */

import type { Command } from 'commander';
import { LearningEngine } from '../../learning/index.js';
import {
  LEARNED_BEST_PRACTICES,
  getBestPracticesByCategory,
  generateBestPracticesReport,
  type BestPractice,
} from '../../learning/best-practices.js';
import type { PatternCategory, FeedbackType, LearnedPattern, Feedback, LearningStats } from '../../learning/types.js';

/**
 * Privacy-sensitive patterns to filter from exports
 */
const PRIVACY_PATTERNS = [
  /api[_-]?key/i,
  /secret/i,
  /password/i,
  /token/i,
  /credential/i,
  /private[_-]?key/i,
  /auth[_-]?key/i,
  /access[_-]?key/i,
  /bearer/i,
  /jwt/i,
];

/**
 * Apply privacy filter to learning data
 * Removes sensitive information like API keys, passwords, etc.
 */
function applyPrivacyFilter(data: {
  feedback: Feedback[];
  patterns: LearnedPattern[];
  stats: LearningStats;
}): {
  feedback: Feedback[];
  patterns: LearnedPattern[];
  stats: LearningStats;
} {
  const filterValue = (value: unknown): unknown => {
    if (typeof value === 'string') {
      for (const pattern of PRIVACY_PATTERNS) {
        if (pattern.test(value)) {
          return '[REDACTED]';
        }
      }
      // Also redact values that look like secrets (long alphanumeric strings)
      if (/^[a-zA-Z0-9]{32,}$/.test(value)) {
        return '[REDACTED]';
      }
    }
    if (Array.isArray(value)) {
      return value.map(filterValue);
    }
    if (typeof value === 'object' && value !== null) {
      const filtered: Record<string, unknown> = {};
      for (const [key, val] of Object.entries(value)) {
        // Redact keys that match privacy patterns
        const isPrivateKey = PRIVACY_PATTERNS.some(p => p.test(key));
        filtered[key] = isPrivateKey ? '[REDACTED]' : filterValue(val);
      }
      return filtered;
    }
    return value;
  };

  return {
    feedback: data.feedback.map(f => filterValue(f) as Feedback),
    patterns: data.patterns.map(p => filterValue(p) as LearnedPattern),
    stats: filterValue(data.stats) as LearningStats,
  };
}

/**
 * Register learn command with all subcommands
 *
 * @see REQ-LEARN-005 - Learning Visualization
 */
export function registerLearnCommand(program: Command): void {
  const learn = program
    .command('learn')
    .description('Self-learning system management')
    .alias('l');

  // Status command
  learn
    .command('status')
    .description('Display learning status dashboard')
    .option('--json', 'Output as JSON')
    .action(async (options) => {
      const engine = new LearningEngine();
      
      if (options.json) {
        const stats = await engine.getStats();
        console.log(JSON.stringify(stats, null, 2));
      } else {
        const report = await engine.generateStatusReport();
        console.log(report);
      }
    });

  // Feedback command
  // @see REQ-CLI-002 - Guidance for required options
  learn
    .command('feedback <artifactId>')
    .description('Record feedback for an artifact')
    .requiredOption('-t, --type <type>', 'Feedback type: accept, reject, modify')
    .requiredOption('-a, --artifact-type <type>', 'Artifact type: requirement, design, code, test')
    .option('-r, --reason <text>', 'Reason for feedback')
    .option('-p, --project <name>', 'Project name')
    .option('-l, --language <lang>', 'Programming language')
    .option('-f, --framework <fw>', 'Framework')
    .addHelpText('after', `
Examples:
  $ musubix learn feedback REQ-001 -t accept -a requirement
  $ musubix learn feedback DES-001 -t reject -a design -r "Missing traceability"
  $ musubix learn feedback src/order.ts -t modify -a code -p my-project

Required Options Explained:
  -t, --type          How you evaluated the artifact:
                        accept  - Artifact is correct, use as positive example
                        reject  - Artifact has issues, learn from mistakes
                        modify  - Artifact was changed, track improvement

  -a, --artifact-type What kind of artifact you're providing feedback on:
                        requirement - EARS format requirements
                        design      - C4 model designs
                        code        - Generated code
                        test        - Generated tests
`)
    .showHelpAfterError('(Use "musubix learn feedback --help" for usage information)')
    .action(async (artifactId, options) => {
      const engine = new LearningEngine();
      
      const validTypes: FeedbackType[] = ['accept', 'reject', 'modify'];
      if (!validTypes.includes(options.type)) {
        console.error(`Error: Invalid feedback type. Must be one of: ${validTypes.join(', ')}`);
        process.exit(1);
      }

      const validArtifactTypes = ['requirement', 'design', 'code', 'test'];
      if (!validArtifactTypes.includes(options.artifactType)) {
        console.error(`Error: Invalid artifact type. Must be one of: ${validArtifactTypes.join(', ')}`);
        process.exit(1);
      }

      const feedback = await engine.recordFeedback({
        type: options.type,
        artifactType: options.artifactType,
        artifactId,
        context: {
          project: options.project,
          language: options.language,
          framework: options.framework,
          tags: [],
        },
        reason: options.reason,
      });

      console.log(`✓ Feedback recorded: ${feedback.id}`);
      console.log(`  Type: ${feedback.type}`);
      console.log(`  Artifact: ${feedback.artifactType}/${feedback.artifactId}`);
      if (feedback.reason) {
        console.log(`  Reason: ${feedback.reason}`);
      }
    });

  // Patterns command
  learn
    .command('patterns')
    .description('List learned patterns')
    .option('-c, --category <cat>', 'Filter by category: code, design, requirement, test')
    .option('--min-confidence <n>', 'Minimum confidence (0-1)', parseFloat)
    .option('--format <fmt>', 'Output format: table, json, markdown', 'table')
    .action(async (options) => {
      const engine = new LearningEngine();
      let patterns = await engine.getPatterns();

      // Filter by category
      if (options.category) {
        patterns = patterns.filter((p) => p.category === options.category);
      }

      // Filter by confidence
      if (options.minConfidence !== undefined) {
        patterns = patterns.filter((p) => p.confidence >= options.minConfidence);
      }

      // Sort by confidence descending
      patterns.sort((a, b) => b.confidence - a.confidence);

      if (options.format === 'json') {
        console.log(JSON.stringify(patterns, null, 2));
      } else if (options.format === 'markdown') {
        console.log('# Learned Patterns\n');
        console.log('| ID | Name | Category | Action | Confidence | Occurrences |');
        console.log('|----|------|----------|--------|------------|-------------|');
        for (const p of patterns) {
          console.log(
            `| ${p.id} | ${p.name} | ${p.category} | ${p.action.type} | ${(p.confidence * 100).toFixed(1)}% | ${p.occurrences} |`
          );
        }
      } else {
        // Table format
        if (patterns.length === 0) {
          console.log('No patterns found.');
          return;
        }
        console.log('\nLearned Patterns:');
        console.log('─'.repeat(80));
        for (const p of patterns) {
          console.log(`  ${p.id} - ${p.name}`);
          console.log(`    Category: ${p.category}, Action: ${p.action.type}`);
          console.log(`    Confidence: ${(p.confidence * 100).toFixed(1)}%, Occurrences: ${p.occurrences}`);
          console.log('');
        }
        console.log(`Total: ${patterns.length} patterns`);
      }
    });

  // Add pattern command
  learn
    .command('add-pattern <name>')
    .description('Manually add a new pattern')
    .requiredOption('-c, --category <cat>', 'Category: code, design, requirement, test')
    .requiredOption('-a, --action <type>', 'Action type: prefer, avoid, suggest')
    .requiredOption('--content <text>', 'Action content/description')
    .option('--confidence <n>', 'Initial confidence (0-1)', parseFloat, 0.5)
    .option('-l, --language <lang>', 'Language context')
    .option('-f, --framework <fw>', 'Framework context')
    .action(async (name, options) => {
      const engine = new LearningEngine();

      const validCategories: PatternCategory[] = ['code', 'design', 'requirement', 'test'];
      if (!validCategories.includes(options.category)) {
        console.error(`Error: Invalid category. Must be one of: ${validCategories.join(', ')}`);
        process.exit(1);
      }

      const validActions = ['prefer', 'avoid', 'suggest'];
      if (!validActions.includes(options.action)) {
        console.error(`Error: Invalid action type. Must be one of: ${validActions.join(', ')}`);
        process.exit(1);
      }

      const context: Record<string, string> = {};
      if (options.language) context.language = options.language;
      if (options.framework) context.framework = options.framework;

      const pattern = await engine.addPattern(
        name,
        options.category,
        { context, conditions: [] },
        { type: options.action, content: options.content },
        options.confidence
      );

      console.log(`✓ Pattern created: ${pattern.id}`);
      console.log(`  Name: ${pattern.name}`);
      console.log(`  Category: ${pattern.category}`);
      console.log(`  Action: ${pattern.action.type}`);
      console.log(`  Confidence: ${(pattern.confidence * 100).toFixed(1)}%`);
    });

  // Remove pattern command
  learn
    .command('remove-pattern <id>')
    .description('Remove a pattern by ID')
    .action(async (id) => {
      const engine = new LearningEngine();
      const removed = await engine.removePattern(id);

      if (removed) {
        console.log(`✓ Pattern removed: ${id}`);
      } else {
        console.error(`Error: Pattern not found: ${id}`);
        process.exit(1);
      }
    });

  // Decay command
  learn
    .command('decay')
    .description('Apply decay to unused patterns')
    .option('-d, --days <n>', 'Days threshold for decay', parseInt, 30)
    .option('-r, --rate <n>', 'Decay rate', parseFloat, 0.1)
    .option('--dry-run', 'Show what would be decayed without applying')
    .action(async (options) => {
      const engine = new LearningEngine();

      if (options.dryRun) {
        const patterns = await engine.getPatterns();
        const threshold = new Date(Date.now() - options.days * 24 * 60 * 60 * 1000);
        const wouldDecay = patterns.filter((p) => p.lastUsed < threshold);
        
        console.log('Patterns that would be decayed:');
        for (const p of wouldDecay) {
          console.log(`  ${p.id} - ${p.name} (confidence: ${(p.confidence * 100).toFixed(1)}%)`);
        }
        console.log(`\nTotal: ${wouldDecay.length} patterns`);
      } else {
        const result = await engine.applyDecay();
        console.log(`✓ Decay applied`);
        console.log(`  Patterns decayed: ${result.decayed}`);
        console.log(`  Patterns archived: ${result.archived}`);
      }
    });

  // Export command
  learn
    .command('export')
    .description('Export learning data (patterns, feedback, stats)')
    .option('-o, --output <file>', 'Output file path')
    .option('--format <fmt>', 'Output format: json, turtle', 'json')
    .option('--privacy-filter', 'Remove sensitive data (API keys, passwords, secrets)')
    .option('--patterns-only', 'Export patterns only (exclude feedback)')
    .option('--feedback-only', 'Export feedback only (exclude patterns)')
    .option('--min-confidence <n>', 'Minimum confidence for patterns (0-1)', parseFloat)
    .action(async (options) => {
      const engine = new LearningEngine();
      let data = await engine.export();

      // Filter by type
      if (options.patternsOnly) {
        data = { ...data, feedback: [] };
      } else if (options.feedbackOnly) {
        data = { ...data, patterns: [] };
      }

      // Filter by confidence
      if (options.minConfidence !== undefined) {
        data.patterns = data.patterns.filter(p => p.confidence >= options.minConfidence);
      }

      // Apply privacy filter
      if (options.privacyFilter) {
        data = applyPrivacyFilter(data);
        console.log('🔒 Privacy filter applied');
      }

      const json = JSON.stringify(data, null, 2);

      if (options.output) {
        const fs = await import('fs/promises');
        await fs.writeFile(options.output, json, 'utf-8');
        console.log(`✓ Learning data exported to: ${options.output}`);
        console.log(`  Patterns: ${data.patterns.length}`);
        console.log(`  Patterns: ${data.patterns.length}`);
        console.log(`  Feedback: ${data.feedback.length}`);
      } else {
        console.log(json);
      }
    });

  // Import command
  learn
    .command('import <file>')
    .description('Import learning data with merge strategy')
    .option('--merge-strategy <strategy>', 'Merge strategy: skip (default), overwrite, merge', 'skip')
    .option('--dry-run', 'Preview import without applying changes')
    .option('--patterns-only', 'Import patterns only')
    .option('--feedback-only', 'Import feedback only')
    .action(async (file, options) => {
      const fs = await import('fs/promises');
      const engine = new LearningEngine();

      // Validate merge strategy
      const validStrategies = ['skip', 'overwrite', 'merge'];
      if (!validStrategies.includes(options.mergeStrategy)) {
        console.error(`Error: Invalid merge strategy. Must be one of: ${validStrategies.join(', ')}`);
        console.error('  skip: Keep existing, skip duplicates');
        console.error('  overwrite: Replace existing with imported');
        console.error('  merge: Merge patterns (combine occurrences, max confidence)');
        process.exit(1);
      }

      try {
        const content = await fs.readFile(file, 'utf-8');
        let data = JSON.parse(content);

        // Filter by type
        if (options.patternsOnly) {
          data = { patterns: data.patterns || [], feedback: [] };
        } else if (options.feedbackOnly) {
          data = { feedback: data.feedback || [], patterns: [] };
        }

        if (options.dryRun) {
          // Preview mode
          const existing = await engine.export();
          const existingPatternIds = new Set(existing.patterns.map(p => p.id));
          const existingFeedbackIds = new Set(existing.feedback.map(f => f.id));

          const newPatterns = (data.patterns || []).filter((p: { id: string }) => !existingPatternIds.has(p.id));
          const duplicatePatterns = (data.patterns || []).filter((p: { id: string }) => existingPatternIds.has(p.id));
          const newFeedback = (data.feedback || []).filter((f: { id: string }) => !existingFeedbackIds.has(f.id));
          const duplicateFeedback = (data.feedback || []).filter((f: { id: string }) => existingFeedbackIds.has(f.id));

          console.log('\n📋 DRY RUN - Import Preview:');
          console.log('─'.repeat(50));
          console.log(`\nPatterns:`);
          console.log(`  New: ${newPatterns.length}`);
          console.log(`  Duplicates: ${duplicatePatterns.length}`);
          console.log(`\nFeedback:`);
          console.log(`  New: ${newFeedback.length}`);
          console.log(`  Duplicates: ${duplicateFeedback.length}`);
          console.log(`\nMerge strategy: ${options.mergeStrategy}`);
          
          if (options.mergeStrategy === 'skip') {
            console.log(`\nResult: ${newPatterns.length} patterns, ${newFeedback.length} feedback would be imported`);
          } else if (options.mergeStrategy === 'overwrite') {
            console.log(`\nResult: All ${(data.patterns || []).length} patterns, ${(data.feedback || []).length} feedback would be imported`);
          } else if (options.mergeStrategy === 'merge') {
            console.log(`\nResult: ${newPatterns.length} new + ${duplicatePatterns.length} merged patterns, ${(data.feedback || []).length} feedback`);
          }
          return;
        }

        // Apply merge strategy
        const result = await engine.importWithStrategy(data, options.mergeStrategy as 'skip' | 'overwrite' | 'merge');

        console.log(`✓ Learning data imported from: ${file}`);
        console.log(`  Strategy: ${options.mergeStrategy}`);
        console.log(`  Feedback imported: ${result.feedbackImported}`);
        console.log(`  Patterns imported: ${result.patternsImported}`);
        if (result.patternsMerged !== undefined && result.patternsMerged > 0) {
          console.log(`  Patterns merged: ${result.patternsMerged}`);
        }
      } catch (error) {
        console.error(`Error importing file: ${error}`);
        process.exit(1);
      }
    });

  // Recommend command
  learn
    .command('recommend')
    .description('Get recommendations for current context')
    .requiredOption('-a, --artifact-type <type>', 'Artifact type: requirement, design, code, test')
    .option('-l, --language <lang>', 'Programming language')
    .option('-f, --framework <fw>', 'Framework')
    .option('-n, --limit <n>', 'Maximum recommendations', parseInt, 5)
    .action(async (options) => {
      const engine = new LearningEngine();

      const recommendations = await engine.getRecommendations(
        {
          artifactType: options.artifactType,
          language: options.language,
          framework: options.framework,
        },
        options.limit
      );

      console.log('\n📚 Recommendations:\n');

      if (recommendations.prefer.length > 0) {
        console.log('✅ PREFER:');
        for (const p of recommendations.prefer) {
          console.log(`   ${p.name} (${(p.confidence * 100).toFixed(0)}%): ${p.action.content}`);
        }
        console.log('');
      }

      if (recommendations.avoid.length > 0) {
        console.log('❌ AVOID:');
        for (const p of recommendations.avoid) {
          console.log(`   ${p.name} (${(p.confidence * 100).toFixed(0)}%): ${p.action.content}`);
        }
        console.log('');
      }

      if (recommendations.suggest.length > 0) {
        console.log('💡 SUGGEST:');
        for (const p of recommendations.suggest) {
          console.log(`   ${p.name} (${(p.confidence * 100).toFixed(0)}%): ${p.action.content}`);
        }
        console.log('');
      }

      const total =
        recommendations.prefer.length +
        recommendations.avoid.length +
        recommendations.suggest.length;

      if (total === 0) {
        console.log('No recommendations available for this context.');
        console.log('Tip: Record more feedback to build patterns.');
      }
    });

  // Best practices command
  learn
    .command('best-practices')
    .description('Display codified best practices from learning')
    .alias('bp')
    .option('-c, --category <cat>', 'Filter by category: code, design, test, requirement')
    .option('--high-confidence', 'Show only high confidence patterns (≥90%)')
    .option('--format <fmt>', 'Output format: table, markdown, json', 'table')
    .action(async (options) => {
      let patterns: BestPractice[] = LEARNED_BEST_PRACTICES;

      // Filter by category
      if (options.category) {
        const validCategories = ['code', 'design', 'test', 'requirement'];
        if (!validCategories.includes(options.category)) {
          console.error(`Error: Invalid category. Must be one of: ${validCategories.join(', ')}`);
          process.exit(1);
        }
        patterns = getBestPracticesByCategory(options.category);
      }

      // Filter by confidence
      if (options.highConfidence) {
        patterns = patterns.filter((p) => p.confidence >= 0.9);
      }

      if (patterns.length === 0) {
        console.log('No best practices found matching criteria.');
        return;
      }

      // Output formatting
      switch (options.format) {
        case 'json':
          console.log(JSON.stringify(patterns, null, 2));
          break;

        case 'markdown':
          console.log(generateBestPracticesReport());
          break;

        case 'table':
        default: {
          console.log('\n📚 MUSUBIX Best Practices\n');
          console.log(`Total: ${patterns.length} patterns\n`);

          // Group by category
          const categories = [...new Set(patterns.map((p) => p.category))];
          for (const cat of categories) {
            const catPatterns = patterns.filter((p) => p.category === cat);
            console.log(`\n## ${cat.toUpperCase()} (${catPatterns.length})\n`);

            for (const bp of catPatterns) {
              const icon = bp.action === 'prefer' ? '✅' : bp.action === 'avoid' ? '❌' : '💡';
              const conf = `${Math.round(bp.confidence * 100)}%`;
              console.log(`${icon} ${bp.id}: ${bp.name} [${conf}]`);
              console.log(`   ${bp.description}`);
              if (bp.antiPattern) {
                console.log(`   ⚠ Anti-pattern: ${bp.antiPattern}`);
              }
              console.log('');
            }
          }
          break;
        }
      }
    });

  // Best practice detail command - show specific BP with example
  learn
    .command('bp-show <id>')
    .description('Show detailed best practice with code example')
    .alias('show')
    .action(async (id) => {
      const bp = LEARNED_BEST_PRACTICES.find(
        (p) => p.id.toLowerCase() === id.toLowerCase()
      );

      if (!bp) {
        console.error(`Error: Best practice not found: ${id}`);
        console.log('\nAvailable IDs:');
        for (const p of LEARNED_BEST_PRACTICES) {
          console.log(`  ${p.id} - ${p.name}`);
        }
        process.exit(1);
      }

      const icon = bp.action === 'prefer' ? '✅' : bp.action === 'avoid' ? '❌' : '💡';
      const conf = `${Math.round(bp.confidence * 100)}%`;

      console.log(`\n${icon} ${bp.id}: ${bp.name}`);
      console.log(`${'─'.repeat(60)}`);
      console.log(`Category: ${bp.category} | Action: ${bp.action} | Confidence: ${conf}`);
      console.log(`Source: ${bp.source}`);
      console.log(`\n📝 Description:\n${bp.description}`);

      if (bp.example) {
        console.log(`\n💻 Example:\n${bp.example}`);
      }

      if (bp.antiPattern) {
        console.log(`\n⚠️  Anti-pattern:\n${bp.antiPattern}`);
      }
      console.log('');
    });

  // List all best practice IDs
  learn
    .command('bp-list')
    .description('List all best practice IDs')
    .alias('bpl')
    .action(async () => {
      console.log('\n📚 MUSUBIX Best Practice IDs\n');
      
      const categories = [...new Set(LEARNED_BEST_PRACTICES.map((p) => p.category))];
      for (const cat of categories) {
        const catPatterns = LEARNED_BEST_PRACTICES.filter((p) => p.category === cat);
        console.log(`\n${cat.toUpperCase()}:`);
        for (const bp of catPatterns) {
          const icon = bp.action === 'prefer' ? '✅' : bp.action === 'avoid' ? '❌' : '💡';
          console.log(`  ${icon} ${bp.id} - ${bp.name} (${Math.round(bp.confidence * 100)}%)`);
        }
      }
      console.log(`\nUse 'musubix learn bp-show <ID>' to see details and examples.`);
    });

  // Dashboard command - Interactive learning dashboard
  learn
    .command('dashboard')
    .description('Display interactive learning dashboard')
    .option('--json', 'Output as JSON')
    .action(async (options: { json?: boolean }) => {
      try {
        // Learning Engine stats
        const engine = new LearningEngine();
        const learningStats = await engine.getStats();
        const patterns = await engine.getPatterns();
        
        if (options.json) {
          console.log(JSON.stringify({
            learning: learningStats,
            patterns: patterns.length,
          }, null, 2));
          return;
        }
        
        // Display dashboard
        console.log('\n╔════════════════════════════════════════════════════════════════╗');
        console.log('║           🧠 MUSUBIX Learning Dashboard                        ║');
        console.log('╠════════════════════════════════════════════════════════════════╣');
        
        // Learning Engine section
        console.log('║ 📚 Learning Engine                                             ║');
        console.log('╟────────────────────────────────────────────────────────────────╢');
        console.log(`║   Total Feedback: ${String(learningStats.totalFeedback).padEnd(44)}║`);
        console.log(`║   Patterns Learned: ${String(patterns.length).padEnd(42)}║`);
        // Calculate acceptance rate from feedbackByType
        const acceptRate = learningStats.totalFeedback > 0 
          ? (learningStats.feedbackByType.accept ?? 0) / learningStats.totalFeedback 
          : 0;
        console.log(`║   Acceptance Rate: ${String((acceptRate * 100).toFixed(1) + '%').padEnd(43)}║`);
        
        console.log('╚════════════════════════════════════════════════════════════════╝\n');
      } catch (error) {
        console.error(`❌ Dashboard error: ${(error as Error).message}`);
        process.exit(1);
      }
    });

  // ==========================================================================
  // Wake-Sleep Learning Commands (TSK-CLI-002)
  // ==========================================================================

  // Wake command - Extract patterns from code
  learn
    .command('wake')
    .description('Run wake phase: extract patterns from code')
    .requiredOption('-t, --target <path>', 'Target directory or file to analyze')
    .option('--task-name <name>', 'Task name for tracking')
    .option('--json', 'Output as JSON')
    .action(async (options: { target: string; taskName?: string; json?: boolean }) => {
      try {
        let wakeSleepModule: typeof import('@nahisaho/musubix-wake-sleep') | null = null;
        
        try {
          wakeSleepModule = await import('@nahisaho/musubix-wake-sleep');
        } catch {
          console.error('Wake-Sleep module not installed. Run: npm install @nahisaho/musubix-wake-sleep');
          process.exit(1);
        }
        
        const { CycleManager } = wakeSleepModule;
        const cycleManager = new CycleManager();
        
        // Read target directory/file
        const { readdir, readFile, stat } = await import('fs/promises');
        const { join, extname, relative } = await import('path');
        
        const targetStat = await stat(options.target);
        const files: string[] = [];
        
        if (targetStat.isDirectory()) {
          const collectFiles = async (dir: string): Promise<void> => {
            const entries = await readdir(dir, { withFileTypes: true });
            for (const entry of entries) {
              const fullPath = join(dir, entry.name);
              if (entry.isDirectory()) {
                // Skip node_modules, .git, etc.
                if (!['node_modules', '.git', 'dist', 'build'].includes(entry.name)) {
                  await collectFiles(fullPath);
                }
              } else if (['.ts', '.js', '.tsx', '.jsx'].includes(extname(entry.name))) {
                files.push(fullPath);
              }
            }
          };
          await collectFiles(options.target);
        } else {
          files.push(options.target);
        }
        
        console.log(`📂 Found ${files.length} files to analyze`);
        
        let totalPatterns = 0;
        for (const file of files) {
          const content = await readFile(file, 'utf-8');
          const relativePath = relative(process.cwd(), file);
          
          await cycleManager.submitTask({
            id: `task-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`,
            type: 'code',
            content: content,
            context: {
              filePath: relativePath,
              language: extname(file).slice(1),
            },
            metadata: {
              taskName: options.taskName ?? relativePath,
            },
          });
          
          totalPatterns++;
        }
        
        const status = cycleManager.getStatus();
        
        if (options.json) {
          console.log(JSON.stringify({
            filesProcessed: files.length,
            tasksQueued: status.taskCount,
            currentPhase: status.currentPhase,
          }, null, 2));
        } else {
          console.log(`\n✅ Wake phase completed`);
          console.log(`   Files analyzed: ${files.length}`);
          console.log(`   Tasks queued: ${status.taskCount}`);
          console.log(`\nUse 'musubix learn sleep' to consolidate patterns.`);
        }
      } catch (error) {
        console.error(`❌ Wake phase failed: ${(error as Error).message}`);
        process.exit(1);
      }
    });

  // Sleep command - Consolidate patterns
  learn
    .command('sleep')
    .description('Run sleep phase: consolidate and abstract patterns')
    .option('--db <path>', 'Knowledge store path', './.knowledge')
    .option('--json', 'Output as JSON')
    .action(async (options: { db?: string; json?: boolean }) => {
      try {
        let wakeSleepModule: typeof import('@nahisaho/musubix-wake-sleep') | null = null;
        
        try {
          wakeSleepModule = await import('@nahisaho/musubix-wake-sleep');
        } catch {
          console.error('Wake-Sleep module not installed. Run: npm install @nahisaho/musubix-wake-sleep');
          process.exit(1);
        }
        
        const { CycleManager } = wakeSleepModule;
        const cycleManager = new CycleManager();
        
        const statusBefore = cycleManager.getStatus();
        await cycleManager.runSleepPhase();
        const statusAfter = cycleManager.getStatus();
        
        if (options.json) {
          console.log(JSON.stringify({
            cycleNumber: statusAfter.cycleNumber,
            patternCount: statusAfter.patternCount,
            lastCycleTime: statusAfter.lastCycleTime,
          }, null, 2));
        } else {
          console.log(`\n✅ Sleep phase completed`);
          console.log(`   Cycle: #${statusAfter.cycleNumber}`);
          console.log(`   Patterns consolidated: ${statusAfter.patternCount - statusBefore.patternCount}`);
          console.log(`   Last run: ${statusAfter.lastCycleTime ?? 'now'}`);
        }
      } catch (error) {
        console.error(`❌ Sleep phase failed: ${(error as Error).message}`);
        process.exit(1);
      }
    });

  // Cycle command - Run complete wake-sleep cycle
  learn
    .command('cycle')
    .description('Run complete wake-sleep learning cycle')
    .requiredOption('-t, --target <path>', 'Target directory or file to analyze')
    .option('--task-name <name>', 'Task name for tracking')
    .option('--db <path>', 'Knowledge store path', './.knowledge')
    .option('--json', 'Output as JSON')
    .action(async (options: { target: string; taskName?: string; db?: string; json?: boolean }) => {
      try {
        let wakeSleepModule: typeof import('@nahisaho/musubix-wake-sleep') | null = null;
        
        try {
          wakeSleepModule = await import('@nahisaho/musubix-wake-sleep');
        } catch {
          console.error('Wake-Sleep module not installed. Run: npm install @nahisaho/musubix-wake-sleep');
          process.exit(1);
        }
        
        const { LearningScheduler } = wakeSleepModule;
        const scheduler = new LearningScheduler();
        const cycleManager = scheduler.getCycleManager();
        
        // Read target directory/file
        const { readdir, readFile, stat } = await import('fs/promises');
        const { join, extname, relative } = await import('path');
        
        const targetStat = await stat(options.target);
        const files: string[] = [];
        
        if (targetStat.isDirectory()) {
          const collectFiles = async (dir: string): Promise<void> => {
            const entries = await readdir(dir, { withFileTypes: true });
            for (const entry of entries) {
              const fullPath = join(dir, entry.name);
              if (entry.isDirectory()) {
                if (!['node_modules', '.git', 'dist', 'build'].includes(entry.name)) {
                  await collectFiles(fullPath);
                }
              } else if (['.ts', '.js', '.tsx', '.jsx'].includes(extname(entry.name))) {
                files.push(fullPath);
              }
            }
          };
          await collectFiles(options.target);
        } else {
          files.push(options.target);
        }
        
        console.log(`📂 Found ${files.length} files to analyze`);
        console.log(`\n🔄 Running wake-sleep cycle...`);
        
        // Wake phase - submit tasks
        for (const file of files) {
          const content = await readFile(file, 'utf-8');
          const relativePath = relative(process.cwd(), file);
          
          await cycleManager.submitTask({
            id: `task-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`,
            type: 'code',
            content: content,
            context: {
              filePath: relativePath,
              language: extname(file).slice(1),
            },
            metadata: {
              taskName: options.taskName ?? relativePath,
            },
          });
        }
        
        // Run the cycle manually
        const result = await scheduler.runCycle();
        
        if (options.json) {
          console.log(JSON.stringify({
            cycleNumber: result.cycleNumber,
            wakeResult: result.wakeResult,
            sleepResult: result.sleepResult,
            durationMs: result.durationMs,
          }, null, 2));
        } else {
          console.log(`\n✅ Wake-Sleep cycle completed`);
          console.log(`   Cycle: #${result.cycleNumber}`);
          console.log(`   Extracted: ${result.wakeResult.extractedPatterns} patterns`);
          console.log(`   Clustered: ${result.sleepResult.clusteredPatterns} patterns`);
          console.log(`   Duration: ${result.durationMs}ms`);
        }
      } catch (error) {
        console.error(`❌ Cycle failed: ${(error as Error).message}`);
        process.exit(1);
      }
    });

  // Compress command - Compress patterns
  learn
    .command('compress')
    .description('Compress and optimize pattern library (runs sleep phase)')
    .option('--db <path>', 'Knowledge store path', './.knowledge')
    .option('--min-frequency <n>', 'Minimum pattern frequency for consolidation', '2')
    .option('--mdl-threshold <n>', 'MDL threshold for abstraction (0-1)', '0.5')
    .option('--json', 'Output as JSON')
    .action(async (options: { db?: string; minFrequency?: string; mdlThreshold?: string; json?: boolean }) => {
      try {
        let wakeSleepModule: typeof import('@nahisaho/musubix-wake-sleep') | null = null;
        
        try {
          wakeSleepModule = await import('@nahisaho/musubix-wake-sleep');
        } catch {
          console.error('Wake-Sleep module not installed. Run: npm install @nahisaho/musubix-wake-sleep');
          process.exit(1);
        }
        
        const { CycleManager } = wakeSleepModule;
        const cycleManager = new CycleManager({
          minPatternFrequency: parseInt(options.minFrequency ?? '2', 10),
          mdlThreshold: parseFloat(options.mdlThreshold ?? '0.5'),
        });
        
        console.log('🔄 Running pattern compression (sleep phase)...\n');
        
        const statusBefore = cycleManager.getStatus();
        await cycleManager.runSleepPhase();
        const statusAfter = cycleManager.getStatus();
        
        if (options.json) {
          console.log(JSON.stringify({
            cycleNumberBefore: statusBefore.cycleNumber,
            cycleNumberAfter: statusAfter.cycleNumber,
            minPatternFrequency: parseInt(options.minFrequency ?? '2', 10),
            mdlThreshold: parseFloat(options.mdlThreshold ?? '0.5'),
            currentPhase: statusAfter.currentPhase,
          }, null, 2));
        } else {
          console.log(`✅ Pattern compression completed`);
          console.log(`   Min frequency: ${options.minFrequency ?? '2'}`);
          console.log(`   MDL threshold: ${options.mdlThreshold ?? '0.5'}`);
          console.log(`   Cycles completed: ${statusAfter.cycleNumber}`);
          console.log(`\nNote: Compression consolidates similar patterns in the library.`);
        }
      } catch (error) {
        console.error(`❌ Compression failed: ${(error as Error).message}`);
        process.exit(1);
      }
    });
}

