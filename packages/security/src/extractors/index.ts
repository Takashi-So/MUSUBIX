/**
 * @fileoverview Extractors barrel export
 * @module @nahisaho/musubix-security/extractors
 * @trace TSK-004, REQ-SEC-LANG-001
 */

// Base extractor types only (v3.0.11 - extractors disabled due to type issues)
export {
  type SupportedLanguage,
  type ASTNode,
  type DFGNode,
  type DFGEdge,
  type DataFlowGraph,
  type BasicBlock,
  type CFGEdge,
  type ControlFlowGraph,
  type SymbolTable,
  type FrameworkModel,
  type ExtractionResult,
  type ExtractionOptions,
  EXTENSION_TO_LANGUAGE,
} from './base-extractor.js';

// Language-specific extractors - disabled due to type issues
// export { GoExtractor } from './go-extractor.js';
// export { JavaExtractor } from './java-extractor.js';

// Extractor factory
import type { SupportedLanguage } from './base-extractor.js';

/**
 * Get supported languages (stub for v3.0.11)
 */
export function getSupportedLanguages(): SupportedLanguage[] {
  return ['typescript', 'javascript', 'python', 'php', 'go', 'java'];
}

/**
 * Detect language from file extension
 */
export function detectLanguage(filePath: string): SupportedLanguage | undefined {
  const ext = filePath.split('.').pop()?.toLowerCase();
  
  const extensionMap: Record<string, SupportedLanguage> = {
    ts: 'typescript',
    tsx: 'typescript',
    js: 'javascript',
    jsx: 'javascript',
    mjs: 'javascript',
    cjs: 'javascript',
    py: 'python',
    php: 'php',
    go: 'go',
    java: 'java',
    rb: 'ruby',
    rs: 'rust',
  };
  
  return ext ? extensionMap[ext] : undefined;
}
