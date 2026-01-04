#!/usr/bin/env node
/**
 * MUSUBI CLI - Wrapper for MUSUBIX
 * 
 * This is an alias package that re-exports @nahisaho/musubix-core
 * 
 * Usage:
 *   npx @nahisaho/musubi init
 *   npx @nahisaho/musubi requirements analyze <file>
 *   npx @nahisaho/musubi design generate <file>
 */

import { createRequire } from 'module';
import { spawn } from 'child_process';
import { dirname, join } from 'path';
import { fileURLToPath } from 'url';

const __dirname = dirname(fileURLToPath(import.meta.url));

// Find musubix-core bin
const musubixBin = join(__dirname, '..', 'node_modules', '@nahisaho', 'musubix-core', 'bin', 'musubix.js');

// Forward all arguments to musubix
const child = spawn('node', [musubixBin, ...process.argv.slice(2)], {
  stdio: 'inherit',
  cwd: process.cwd(),
});

child.on('close', (code) => {
  process.exit(code || 0);
});
