/**
 * REPL Command
 * 
 * Starts the interactive REPL shell for MUSUBIX
 * 
 * @packageDocumentation
 * @module cli/commands/repl
 * 
 * @see REQ-CLI-v1.5.0 - Interactive CLI Mode
 * @see DES-CLI-v1.5.0 - REPL設計
 */

import type { Command } from 'commander';
import { ExitCode, getGlobalOptions, outputResult } from '../base.js';
import { ReplEngine, type ReplConfig } from '../repl/index.js';
import { VERSION } from '../../version.js';

/**
 * REPL command options
 */
export interface ReplOptions {
  history?: string;
  noColor: boolean;
  prompt?: string;
}

/**
 * Register the REPL command
 * 
 * @param program - Commander program instance
 * 
 * @example
 * ```bash
 * # Start REPL with default settings
 * npx musubix repl
 * 
 * # Start REPL with custom history file
 * npx musubix repl --history ~/.musubix_history
 * 
 * # Start REPL without colors
 * npx musubix repl --no-color
 * ```
 */
export function registerReplCommand(program: Command): void {
  program
    .command('repl')
    .description('Start interactive REPL shell')
    .option('--history <file>', 'History file path', '.musubix_history')
    .option('--no-color', 'Disable colored output')
    .option('--prompt <string>', 'Custom prompt string')
    .action(async (options: ReplOptions) => {
      const globalOpts = getGlobalOptions(program);
      
      try {
        // Display welcome banner
        if (!globalOpts.quiet) {
          displayWelcomeBanner(options.noColor);
        }
        
        // Create REPL configuration
        const config: Partial<ReplConfig> = {
          history: {
            maxSize: 1000,
            filePath: options.history ?? '.musubix_history',
          },
          prompt: {
            showProject: true,
            showPhase: false,
            useColor: !options.noColor,
            defaultPrompt: options.prompt ?? 'musubix> ',
          },
        };
        
        // Create and start REPL engine
        const repl = new ReplEngine(config);
        
        // Handle graceful shutdown
        process.on('SIGINT', () => {
          console.log('\n\nGoodbye!');
          repl.stop();
        });
        
        // Start the REPL
        await repl.start();
        
        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        outputResult({
          success: false,
          error: error instanceof Error ? error.message : String(error),
        }, globalOpts);
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });
}

/**
 * Display welcome banner
 */
function displayWelcomeBanner(noColor: boolean): void {
  const cyan = noColor ? '' : '\x1b[36m';
  const yellow = noColor ? '' : '\x1b[33m';
  const green = noColor ? '' : '\x1b[32m';
  const reset = noColor ? '' : '\x1b[0m';
  
  console.log(`
${cyan}╔══════════════════════════════════════════════════════════╗
║                                                          ║
║   ${yellow}███╗   ███╗██╗   ██╗███████╗██╗   ██╗██████╗ ██╗${cyan}        ║
║   ${yellow}████╗ ████║██║   ██║██╔════╝██║   ██║██╔══██╗██║${cyan}        ║
║   ${yellow}██╔████╔██║██║   ██║███████╗██║   ██║██████╔╝██║${cyan}        ║
║   ${yellow}██║╚██╔╝██║██║   ██║╚════██║██║   ██║██╔══██╗██║${cyan}        ║
║   ${yellow}██║ ╚═╝ ██║╚██████╔╝███████║╚██████╔╝██████╔╝██║${cyan}        ║
║   ${yellow}╚═╝     ╚═╝ ╚═════╝ ╚══════╝ ╚═════╝ ╚═════╝ ╚═╝${cyan}        ║
║                                                          ║
║   ${green}Neuro-Symbolic AI Integration System v${VERSION}${cyan}         ║
║                                                          ║
╚══════════════════════════════════════════════════════════╝${reset}

Type ${green}help${reset} for available commands, ${green}exit${reset} to quit.
Press ${yellow}TAB${reset} for auto-completion, ${yellow}↑/↓${reset} for history navigation.
`);
}
