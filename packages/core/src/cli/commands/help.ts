/**
 * Help Command
 * 
 * Provides extended help information for MUSUBIX CLI
 * 
 * @packageDocumentation
 * @module cli/commands/help
 * 
 * @see REQ-ARC-002 - CLI Interface
 * @see DES-MUSUBIX-001 Section 3.2.2 - CLI Commands
 */

import type { Command } from 'commander';
import { VERSION } from '../../index.js';

/**
 * Command help information
 */
interface CommandHelp {
  name: string;
  description: string;
  usage: string;
  examples: string[];
  options?: string[];
}

/**
 * Extended help content
 */
const COMMAND_HELP: Record<string, CommandHelp> = {
  init: {
    name: 'init',
    description: 'Initialize a new MUSUBIX project with steering documents and configuration',
    usage: 'musubix init [path] [options]',
    examples: [
      'musubix init                    # Initialize in current directory',
      'musubix init my-project         # Initialize in my-project directory',
      'musubix init . --name "MyApp"   # Initialize with custom name',
      'musubix init . --force          # Overwrite existing configuration',
    ],
    options: [
      '-n, --name <name>      Project name',
      '-t, --template <name>  Project template (default: default)',
      '-f, --force            Overwrite existing files',
    ],
  },
  requirements: {
    name: 'requirements',
    description: 'Analyze and validate requirements using EARS format',
    usage: 'musubix requirements <subcommand> [options]',
    examples: [
      'musubix requirements analyze input.md    # Analyze natural language requirements',
      'musubix requirements validate spec.md   # Validate EARS syntax',
      'musubix requirements map spec.md        # Map to ontology',
      'musubix requirements search "login"     # Search related requirements',
    ],
    options: [
      'analyze <file>    Analyze natural language → EARS',
      'validate <file>   Validate EARS syntax',
      'map <file>        Map to ontology',
      'search <query>    Search related requirements',
    ],
  },
  design: {
    name: 'design',
    description: 'Generate and validate system designs',
    usage: 'musubix design <subcommand> [options]',
    examples: [
      'musubix design generate req.md     # Generate design from requirements',
      'musubix design patterns context    # Detect applicable patterns',
      'musubix design validate design.md  # Validate SOLID compliance',
      'musubix design c4 design.md        # Generate C4 diagrams',
    ],
    options: [
      'generate <file>   Generate design from requirements',
      'patterns <ctx>    Detect applicable patterns',
      'validate <file>   Validate SOLID compliance',
      'c4 <file>         Generate C4 diagrams',
      'adr <decision>    Generate ADR',
    ],
  },
  codegen: {
    name: 'codegen',
    description: 'Generate and analyze code',
    usage: 'musubix codegen <subcommand> [options]',
    examples: [
      'musubix codegen generate design.md    # Generate code from design',
      'musubix codegen analyze src/index.ts  # Static analysis',
      'musubix codegen security src/         # Security scan',
    ],
    options: [
      'generate <file>   Generate code from design',
      'analyze <file>    Static analysis',
      'security <path>   Security scan',
    ],
  },
  test: {
    name: 'test',
    description: 'Generate tests and measure coverage',
    usage: 'musubix test <subcommand> [options]',
    examples: [
      'musubix test generate src/index.ts   # Generate tests for file',
      'musubix test coverage tests/         # Measure coverage',
    ],
    options: [
      'generate <file>   Generate tests',
      'coverage <dir>    Measure coverage',
    ],
  },
  trace: {
    name: 'trace',
    description: 'Manage traceability between artifacts',
    usage: 'musubix trace <subcommand> [options]',
    examples: [
      'musubix trace matrix              # Generate traceability matrix',
      'musubix trace impact REQ-001      # Impact analysis',
      'musubix trace validate            # Validate all links',
    ],
    options: [
      'matrix            Generate traceability matrix',
      'impact <id>       Impact analysis',
      'validate          Validate links',
    ],
  },
  explain: {
    name: 'explain',
    description: 'Generate explanations for decisions',
    usage: 'musubix explain <subcommand> [options]',
    examples: [
      'musubix explain why DES-001        # Explain design decision',
      'musubix explain graph DES-001      # Generate reasoning graph',
    ],
    options: [
      'why <id>          Explain reasoning',
      'graph <id>        Generate reasoning graph',
    ],
  },
};

/**
 * Register help command
 */
export function registerHelpCommand(program: Command): void {
  program
    .command('help')
    .description('Display help for a specific command')
    .argument('[command]', 'Command to get help for')
    .action((commandName?: string) => {
      if (commandName) {
        displayCommandHelp(commandName);
      } else {
        displayGeneralHelp();
      }
    });
}

/**
 * Display help for a specific command
 */
function displayCommandHelp(commandName: string): void {
  const help = COMMAND_HELP[commandName];
  
  if (!help) {
    console.log(`Unknown command: ${commandName}`);
    console.log('');
    console.log('Available commands:');
    Object.keys(COMMAND_HELP).forEach(cmd => {
      console.log(`  ${cmd}`);
    });
    return;
  }

  console.log(`
${bold('Command:')} ${help.name}
${bold('Description:')} ${help.description}

${bold('Usage:')}
  ${help.usage}

${bold('Examples:')}
${help.examples.map(ex => `  ${ex}`).join('\n')}
`);

  if (help.options && help.options.length > 0) {
    console.log(`${bold('Options/Subcommands:')}`);
    help.options.forEach(opt => {
      console.log(`  ${opt}`);
    });
  }
}

/**
 * Display general help
 */
function displayGeneralHelp(): void {
  console.log(`
${bold('MUSUBIX')} - Neuro-Symbolic AI Coding System
${dim(`Version ${VERSION}`)}

${bold('Usage:')}
  musubix <command> [options]

${bold('Commands:')}
  init           Initialize a new MUSUBIX project
  requirements   Analyze and validate requirements (EARS format)
  design         Generate and validate system designs
  codegen        Generate and analyze code
  test           Generate tests and measure coverage
  trace          Manage traceability between artifacts
  explain        Generate explanations for decisions
  help           Display help for a specific command

${bold('Global Options:')}
  -v, --version      Display version number
  --verbose          Enable verbose output
  --json             Output in JSON format
  --config <path>    Path to configuration file
  -q, --quiet        Suppress non-essential output
  -h, --help         Display help

${bold('Examples:')}
  musubix init my-project
  musubix requirements analyze spec.md
  musubix design generate requirements.md
  musubix help requirements

${bold('Documentation:')}
  https://github.com/nahisaho/MUSUBIX

${bold('Constitutional Articles:')}
  This project follows 9 Constitutional Articles
  See: steering/rules/constitution.md
`);
}

/**
 * Bold text formatting
 */
function bold(text: string): string {
  return `\x1b[1m${text}\x1b[0m`;
}

/**
 * Dim text formatting
 */
function dim(text: string): string {
  return `\x1b[2m${text}\x1b[0m`;
}
