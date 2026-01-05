/**
 * @fileoverview Pattern extraction module
 * @traceability TSK-PATTERN-001
 */

export { PatternExtractor } from './pattern-extractor.js';export { TypeScriptParser, type FunctionInfo, type ClassInfo, type ImportInfo } from './typescript-parser.js';
export { SubtreeFinder, type SubtreeCandidate, type SubtreeLocation } from './subtree-finder.js';
export { AntiUnifier, type AntiUnificationResult } from './anti-unifier.js';