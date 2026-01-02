#!/usr/bin/env node
/**
 * MUSUBIX CLI Entry Point (Root Package)
 * 
 * This file re-exports the CLI from @nahisaho/musubix-core package.
 * 
 * @see REQ-ARC-002 - CLI Interface
 * 
 * Usage:
 *   npx musubix
 *   musubix <command> [options]
 */

// Forward to the core package's CLI
import '@nahisaho/musubix-core/bin/musubix.js';
