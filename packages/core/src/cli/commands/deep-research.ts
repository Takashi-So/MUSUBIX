/**
 * @fileoverview Deep Research CLI command
 * @module @nahisaho/musubix-core/cli/commands
 * @version 1.0.0
 * 
 * REQ: REQ-DR-INT-005 (CLI Integration)
 * TSK: TSK-DR-019 (CLI Tool Integration)
 */

import { Command } from 'commander';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';

/**
 * CLI options for deep-research command
 */
interface DeepResearchOptions {
  maxIterations?: number;
  tokenBudget?: number;
  output?: string;
  format?: 'markdown' | 'json';
  provider?: 'jina' | 'brave' | 'duckduckgo';
  verbose?: boolean;
}

/**
 * Register deep-research command
 */
export function registerDeepResearchCommand(program: Command): void {
  program
    .command('deep-research <query>')
    .description('Perform iterative deep research on a technical topic')
    .option('-i, --max-iterations <number>', 'Maximum research iterations', '5')
    .option('-t, --token-budget <number>', 'Token budget limit', '10000')
    .option('-o, --output <file>', 'Output file path')
    .option('-f, --format <type>', 'Output format (markdown|json)', 'markdown')
    .option('-p, --provider <name>', 'Search provider (jina|brave|duckduckgo)', 'jina')
    .option('-v, --verbose', 'Enable verbose logging', false)
    .action(async (query: string, options: DeepResearchOptions) => {
      await executeDeepResearch(query, options);
    });
}

/**
 * Execute deep research
 */
async function executeDeepResearch(
  query: string,
  options: DeepResearchOptions
): Promise<void> {
  try {
    console.log('🔍 MUSUBIX Deep Research v3.4.0\n');
    console.log(`Query: "${query}"`);
    console.log(`Max Iterations: ${options.maxIterations ?? 5}`);
    console.log(`Token Budget: ${options.tokenBudget ?? 10000}`);
    console.log(`Provider: ${options.provider ?? 'jina'}`);
    console.log('');

    // Check if deep-research package is available
    let ResearchEngine: any;
    let createJinaProvider: any;
    let createBraveProvider: any;
    let createDuckDuckGoProvider: any;
    let createVSCodeLMProvider: any;

    try {
      // Dynamic import to avoid build-time dependency
      const deepResearchModule = await import('@nahisaho/musubix-deep-research').catch(() => null) as any;
      if (!deepResearchModule) {
        throw new Error('Module not found');
      }
      ResearchEngine = deepResearchModule.ResearchEngine;
      createJinaProvider = deepResearchModule.createJinaProvider;
      createBraveProvider = deepResearchModule.createBraveProvider;
      createDuckDuckGoProvider = deepResearchModule.createDuckDuckGoProvider;
      createVSCodeLMProvider = deepResearchModule.createVSCodeLMProvider;
    } catch (error) {
      console.error('❌ Deep Research package not available.');
      console.error('   Run: npm install @nahisaho/musubix-deep-research');
      process.exit(1);
    }

    // Create search provider
    let searchProvider;
    const providerName = options.provider ?? 'jina';

    if (providerName === 'jina') {
      const apiKey = process.env.JINA_API_KEY;
      if (!apiKey) {
        console.error('❌ JINA_API_KEY environment variable not set');
        console.error('   Get your API key: https://jina.ai/');
        process.exit(1);
      }
      searchProvider = createJinaProvider({ apiKey });
    } else if (providerName === 'brave') {
      const apiKey = process.env.BRAVE_API_KEY;
      if (!apiKey) {
        console.error('❌ BRAVE_API_KEY environment variable not set');
        console.error('   Get your API key: https://brave.com/search/api/');
        process.exit(1);
      }
      searchProvider = createBraveProvider({ apiKey });
    } else if (providerName === 'duckduckgo') {
      searchProvider = createDuckDuckGoProvider();
    } else {
      console.error(`❌ Unknown provider: ${providerName}`);
      process.exit(1);
    }

    // Create reasoning provider (VS Code LM)
    let reasoningProvider;
    try {
      reasoningProvider = await createVSCodeLMProvider({
        modelSelector: { vendor: 'copilot', family: 'gpt-4' },
      });

      // Check availability
      const isAvailable = await reasoningProvider.isAvailable();
      if (!isAvailable) {
        console.error('❌ VS Code LM API not available');
        console.error('   Make sure you are running this command from VS Code');
        console.error('   with GitHub Copilot enabled');
        process.exit(1);
      }
    } catch (error) {
      console.error('❌ Failed to initialize reasoning provider:', error);
      process.exit(1);
    }

    // Create research engine
    const engine = new ResearchEngine({
      searchProvider,
      reasoningProvider,
      maxIterations: parseInt(String(options.maxIterations ?? '5'), 10),
      tokenBudget: parseInt(String(options.tokenBudget ?? '10000'), 10),
    });

    console.log('🚀 Starting research...\n');

    // Execute research with progress updates
    const result = await engine.research(query, {
      onIteration: (iteration: number, total: number) => {
        if (options.verbose) {
          console.log(`\n🔍 === Iteration ${iteration}/${total} ===`);
        } else {
          process.stdout.write(`\r🔍 Progress: ${iteration}/${total} iterations`);
        }
      },
      onSearch: (query: string, results: unknown[]) => {
        if (options.verbose) {
          console.log(`[SEARCH] "${query}" → ${results.length} results`);
        }
      },
      onRead: (url: string, content: string) => {
        if (options.verbose) {
          console.log(`[READ] ${url} → ${content.length} chars`);
        }
      },
      onReason: (knowledge: unknown[]) => {
        if (options.verbose) {
          console.log(`[REASON] +${knowledge.length} knowledge items`);
        }
      },
    });

    if (!options.verbose) {
      process.stdout.write('\r✅ Research completed!     \n\n');
    } else {
      console.log('\n\n✅ Research completed!\n');
    }

    // Display summary
    console.log('📊 Summary:');
    console.log(`   Iterations: ${result.iterations}`);
    console.log(`   Tokens used: ${result.tokensUsed}/${options.tokenBudget ?? 10000}`);
    console.log(`   Knowledge items: ${result.knowledge.length}`);
    console.log(`   Duration: ${(result.duration / 1000).toFixed(2)}s`);
    console.log('');

    // Generate output
    const outputFormat = options.format ?? 'markdown';
    let outputContent: string;

    if (outputFormat === 'markdown') {
      outputContent = generateMarkdownReport(query, result);
    } else if (outputFormat === 'json') {
      outputContent = JSON.stringify(result, null, 2);
    } else {
      console.error(`❌ Unknown format: ${outputFormat}`);
      process.exit(1);
    }

    // Write output
    if (options.output) {
      await fs.mkdir(path.dirname(options.output), { recursive: true });
      await fs.writeFile(options.output, outputContent, 'utf-8');
      console.log(`📄 Report saved: ${options.output}`);
    } else {
      console.log('');
      console.log('━'.repeat(80));
      console.log(outputContent);
      console.log('━'.repeat(80));
    }

    console.log('');
    console.log('✨ Deep Research completed successfully!');
  } catch (error) {
    console.error('\n❌ Research failed:', error);
    if (error instanceof Error && options.verbose) {
      console.error(error.stack);
    }
    process.exit(1);
  }
}

/**
 * Generate markdown report from research result
 */
function generateMarkdownReport(query: string, result: any): string {
  const lines: string[] = [];

  lines.push(`# Deep Research Report: ${query}`);
  lines.push('');
  lines.push(`**Generated**: ${new Date().toISOString()}`);
  lines.push(`**Iterations**: ${result.iterations}`);
  lines.push(`**Tokens Used**: ${result.tokensUsed}`);
  lines.push(`**Duration**: ${(result.duration / 1000).toFixed(2)}s`);
  lines.push('');

  lines.push('## Summary');
  lines.push('');
  if (result.summary) {
    lines.push(result.summary);
  } else {
    lines.push(`Research completed with ${result.knowledge.length} knowledge items discovered.`);
  }
  lines.push('');

  if (result.knowledge.length > 0) {
    lines.push('## Findings');
    lines.push('');

    for (const [index, item] of result.knowledge.entries()) {
      lines.push(`### ${index + 1}. ${item.title || 'Finding'}`);
      lines.push('');
      lines.push(item.content);
      lines.push('');
      if (item.source) {
        lines.push(`**Source**: ${item.source}`);
        lines.push('');
      }
      if (item.confidence !== undefined) {
        lines.push(`**Confidence**: ${(item.confidence * 100).toFixed(0)}%`);
        lines.push('');
      }
    }
  }

  if (result.trajectory && result.trajectory.length > 0) {
    lines.push('## Research Trajectory');
    lines.push('');
    lines.push('```');
    for (const log of result.trajectory) {
      lines.push(log);
    }
    lines.push('```');
    lines.push('');
  }

  return lines.join('\n');
}
