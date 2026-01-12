/**
 * @fileoverview Extractors barrel export
 * @module @nahisaho/musubix-security/extractors
 * @trace TSK-004, REQ-SEC-LANG-001, REQ-SEC-LANG-005, REQ-SEC-LANG-006
 */

// Base extractor and types
export {
  BaseExtractor,
  type SupportedLanguage,
  type ASTNode,
  type ASTEdge,
  type DFGNode,
  type DFGEdge,
  type DataFlowGraph,
  type BasicBlock,
  type CFGEdge,
  type ControlFlowGraph,
  type SymbolTable,
  type Symbol,
  type FunctionSymbol,
  type ClassSymbol,
  type ScopeInfo,
  type FrameworkModel,
  type FrameworkSource,
  type FrameworkSink,
  type FrameworkSanitizer,
  type ExtractionResult,
  type ExtractionOptions,
  EXTENSION_TO_LANGUAGE,
} from './base-extractor.js';

// Language-specific extractors
export { RubyExtractor, createRubyExtractor } from './ruby-extractor.js';
export { RustExtractor, createRustExtractor } from './rust-extractor.js';

// Extractor factory
import type { SupportedLanguage } from './base-extractor.js';
import { RubyExtractor } from './ruby-extractor.js';
import { RustExtractor } from './rust-extractor.js';

/**
 * Get supported languages
 * @trace REQ-SEC-LANG-001
 */
export function getSupportedLanguages(): SupportedLanguage[] {
  return ['typescript', 'javascript', 'python', 'php', 'go', 'java', 'ruby', 'rust'];
}

/**
 * Create extractor for a language
 * @trace REQ-SEC-LANG-001
 */
export function createExtractor(
  language: SupportedLanguage
): RubyExtractor | RustExtractor | null {
  switch (language) {
    case 'ruby':
      return new RubyExtractor();
    case 'rust':
      return new RustExtractor();
    default:
      // Other languages not yet implemented
      return null;
  }
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
