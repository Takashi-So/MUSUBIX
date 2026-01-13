/**
 * CLI Index
 * 
 * @packageDocumentation
 * @module cli
 */

export * from './base.js';
export * from './commands/index.js';
export * from './performance.js';
export * from './lazy-loader.js';

// Scaffold Generators (v3.3.0) - namespace export to avoid name collisions
import * as generators from './generators/index.js';
export { generators };
