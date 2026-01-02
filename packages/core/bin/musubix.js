#!/usr/bin/env node
/**
 * MUSUBIX CLI Entry Point
 * 
 * @see REQ-ARC-002 - CLI Interface
 * 
 * Usage:
 *   npx @musubix/core
 *   npx musubix
 *   musubix <command> [options]
 */

import { createProgram } from '../dist/cli/base.js';
import { registerCommands } from '../dist/cli/commands/index.js';

const program = createProgram();
registerCommands(program);
program.parse();
