/**
 * @fileoverview Extractors barrel export
 * @module @nahisaho/musubix-security/extractors
 * @trace TSK-004, REQ-SEC-LANG-001
 */

// Base extractor
export {
  BaseExtractor,
  type SupportedLanguage,
  type ASTNode,
  type DFGNode,
  type DFGEdge,
  type DataFlowGraph,
  type BasicBlock,
  type CFGEdge,
  type ControlFlowGraph,
  type SymbolEntry,
  type SymbolTable,
  type FrameworkModel,
  type ExtractionResult,
  type ExtractorOptions,
} from './base-extractor.js';

// Language-specific extractors
export { GoExtractor } from './go-extractor.js';
export { JavaExtractor } from './java-extractor.js';
// export { RubyExtractor } from './ruby-extractor.js';
// export { RustExtractor } from './rust-extractor.js';

// Extractor factory
import { BaseExtractor, type SupportedLanguage, type ExtractorOptions } from './base-extractor.js';
import { GoExtractor } from './go-extractor.js';
import { JavaExtractor } from './java-extractor.js';

/**
 * Registry of language extractors
 */
const extractorRegistry: Map<SupportedLanguage, new (options?: ExtractorOptions) => BaseExtractor> = new Map([
  ['go', GoExtractor],
  ['java', JavaExtractor],
]);

/**
 * Register an extractor for a language
 */
export function registerExtractor(
  language: SupportedLanguage,
  extractor: new (options?: ExtractorOptions) => BaseExtractor,
): void {
  extractorRegistry.set(language, extractor);
}

/**
 * Get extractor for a language
 */
export function getExtractor(
  language: SupportedLanguage,
  options?: ExtractorOptions,
): BaseExtractor | undefined {
  const ExtractorClass = extractorRegistry.get(language);
  if (ExtractorClass) {
    return new ExtractorClass(options);
  }
  return undefined;
}

/**
 * Get supported languages
 */
export function getSupportedLanguages(): SupportedLanguage[] {
  return Array.from(extractorRegistry.keys());
}

/**
 * Check if language is supported
 */
export function isLanguageSupported(language: string): language is SupportedLanguage {
  return extractorRegistry.has(language as SupportedLanguage);
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
    c: 'c',
    cpp: 'cpp',
    cc: 'cpp',
    cxx: 'cpp',
    h: 'c',
    hpp: 'cpp',
  };
  
  return ext ? extensionMap[ext] : undefined;
}

/**
 * Extract code information from a file
 */
export async function extractFromFile(
  filePath: string,
  content: string,
  options?: ExtractorOptions,
): Promise<ExtractionResult | undefined> {
  const language = detectLanguage(filePath);
  if (!language) {
    return undefined;
  }
  
  const extractor = getExtractor(language, options);
  if (!extractor) {
    return undefined;
  }
  
  return extractor.extract(content, filePath);
}

// Re-export ExtractionResult type
import type { ExtractionResult } from './base-extractor.js';
export type { ExtractionResult as ExtractResult };
