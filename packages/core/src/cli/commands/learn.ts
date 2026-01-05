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
  learn
    .command('feedback <artifactId>')
    .description('Record feedback for an artifact')
    .requiredOption('-t, --type <type>', 'Feedback type: accept, reject, modify')
    .requiredOption('-a, --artifact-type <type>', 'Artifact type: requirement, design, code, test')
    .option('-r, --reason <text>', 'Reason for feedback')
    .option('-p, --project <name>', 'Project name')
    .option('-l, --language <lang>', 'Programming language')
    .option('-f, --framework <fw>', 'Framework')
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
}
