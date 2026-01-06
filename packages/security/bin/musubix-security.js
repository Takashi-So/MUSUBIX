#!/usr/bin/env node
/**
 * @fileoverview MUSUBIX Security CLI entry point
 * @module @nahisaho/musubix-security/bin
 */

import { runCLI } from '../dist/cli/index.js';

runCLI().catch((error) => {
  console.error('Fatal error:', error.message);
  process.exit(1);
});
