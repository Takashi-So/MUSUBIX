/**
 * @nahisaho/musubix-dfg
 *
 * Data Flow Graph (DFG) and Control Flow Graph (CFG) analysis
 * for MUSUBIX neuro-symbolic code understanding.
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-dfg
 *
 * @example
 * ```typescript
 * import { DataFlowAnalyzer, ControlFlowAnalyzer } from '@nahisaho/musubix-dfg';
 *
 * // Analyze TypeScript code
 * const dfgAnalyzer = new DataFlowAnalyzer();
 * const dfg = await dfgAnalyzer.analyze('src/user-service.ts');
 *
 * // Get data dependencies
 * const deps = dfg.getDataDependencies('userId');
 *
 * // Analyze control flow
 * const cfgAnalyzer = new ControlFlowAnalyzer();
 * const cfg = await cfgAnalyzer.analyze('src/user-service.ts');
 *
 * // Get all paths from entry to exit
 * const paths = cfg.getAllPaths();
 * ```
 *
 * @traces REQ-DFG-001, REQ-DFG-002, REQ-DFG-003
 */

// Types
export * from './types/index.js';

// Graph structures
export * from './graph/index.js';

// Analyzers
export * from './analyzers/index.js';

// YATA integration
export * from './yata/index.js';
