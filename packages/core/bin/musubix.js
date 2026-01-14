#!/usr/bin/env node
/**
 * MUSUBIX CLI Entry Point
 * 
 * @see REQ-ARC-002 - CLI Interface
 * @see REQ-BUGFIX-005-03 - Custom version action with verbose support
 * 
 * Usage:
 *   npx @musubix/core
 *   npx musubix
 *   musubix <command> [options]
 */

import { createProgram } from '../dist/cli/base.js';
import { registerCommands } from '../dist/cli/commands/index.js';
import { VERSION, formatVerboseVersion } from '../dist/version.js';

// Handle --version with --verbose before Commander processes it
// REQ-BUGFIX-005-03: Custom version action with verbose support
const args = process.argv.slice(2);
if (args.includes('-v') || args.includes('--version')) {
  if (args.includes('--verbose')) {
    console.log(formatVerboseVersion());
  } else {
    console.log(`musubix v${VERSION}`);
  }
  process.exit(0);
}

const program = createProgram();
registerCommands(program);
program.parse();
