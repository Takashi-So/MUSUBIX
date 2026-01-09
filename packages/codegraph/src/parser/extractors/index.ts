/**
 * @nahisaho/musubix-codegraph - Extractor Registry
 *
 * Registry for language-specific extractors with lazy loading support
 *
 * @see REQ-CG-REG-001
 * @see DES-CG-REGISTRY
 * @see TSK-CG-002
 */

import type { Language } from '../../types.js';
import type { BaseExtractor } from './base-extractor.js';

// Type for lazy extractor factory
type ExtractorFactory = () => Promise<BaseExtractor>;

/**
 * Registry for language extractors
 *
 * Supports lazy loading to minimize memory footprint
 */
class ExtractorRegistry {
  private readonly extractors = new Map<Language, BaseExtractor>();
  private readonly factories = new Map<Language, ExtractorFactory>();
  private readonly loading = new Map<Language, Promise<BaseExtractor>>();

  /**
   * Register an extractor instance directly
   */
  register(language: Language, extractor: BaseExtractor): void {
    this.extractors.set(language, extractor);
  }

  /**
   * Register a lazy extractor factory
   * The factory will be called only when the extractor is first requested
   */
  registerFactory(language: Language, factory: ExtractorFactory): void {
    this.factories.set(language, factory);
  }

  /**
   * Get an extractor for a language
   * Returns undefined if not registered
   */
  async getExtractor(language: Language): Promise<BaseExtractor | undefined> {
    // Check if already loaded
    const existing = this.extractors.get(language);
    if (existing) return existing;

    // Check if currently loading
    const loadingPromise = this.loading.get(language);
    if (loadingPromise) return loadingPromise;

    // Check if factory exists
    const factory = this.factories.get(language);
    if (!factory) return undefined;

    // Load via factory
    const promise = factory();
    this.loading.set(language, promise);

    try {
      const extractor = await promise;
      this.extractors.set(language, extractor);
      return extractor;
    } finally {
      this.loading.delete(language);
    }
  }

  /**
   * Get an extractor synchronously (returns undefined if not yet loaded)
   */
  getExtractorSync(language: Language): BaseExtractor | undefined {
    return this.extractors.get(language);
  }

  /**
   * Check if an extractor is registered for a language
   */
  hasExtractor(language: Language): boolean {
    return this.extractors.has(language) || this.factories.has(language);
  }

  /**
   * Get all registered languages
   */
  getRegisteredLanguages(): Language[] {
    const languages = new Set<Language>();
    for (const lang of this.extractors.keys()) {
      languages.add(lang);
    }
    for (const lang of this.factories.keys()) {
      languages.add(lang);
    }
    return Array.from(languages);
  }

  /**
   * Get all loaded extractors
   */
  getLoadedExtractors(): Map<Language, BaseExtractor> {
    return new Map(this.extractors);
  }

  /**
   * Preload all extractors
   */
  async preloadAll(): Promise<void> {
    const languages = this.getRegisteredLanguages();
    await Promise.all(languages.map((lang) => this.getExtractor(lang)));
  }

  /**
   * Clear all registered extractors
   */
  clear(): void {
    this.extractors.clear();
    this.factories.clear();
    this.loading.clear();
  }
}

// Singleton instance
export const extractorRegistry = new ExtractorRegistry();

/**
 * Register all language extractors
 * Uses lazy loading to minimize initial load time
 */
export function registerAllExtractors(): void {
  // TypeScript/JavaScript (existing support)
  extractorRegistry.registerFactory('typescript', async () => {
    const { TypeScriptExtractor } = await import('./typescript.js');
    return new TypeScriptExtractor();
  });

  extractorRegistry.registerFactory('javascript', async () => {
    const { JavaScriptExtractor } = await import('./typescript.js');
    return new JavaScriptExtractor();
  });

  // Python (existing support)
  extractorRegistry.registerFactory('python', async () => {
    const { PythonExtractor } = await import('./python.js');
    return new PythonExtractor();
  });

  // P0 Languages: Rust, Go, Java
  extractorRegistry.registerFactory('rust', async () => {
    const { RustExtractor } = await import('./rust.js');
    return new RustExtractor();
  });

  extractorRegistry.registerFactory('go', async () => {
    const { GoExtractor } = await import('./go.js');
    return new GoExtractor();
  });

  extractorRegistry.registerFactory('java', async () => {
    const { JavaExtractor } = await import('./java.js');
    return new JavaExtractor();
  });

  // P1 Languages: PHP, C#, C, C++, Ruby
  extractorRegistry.registerFactory('php', async () => {
    const { PhpExtractor } = await import('./php.js');
    return new PhpExtractor();
  });

  extractorRegistry.registerFactory('csharp', async () => {
    const { CSharpExtractor } = await import('./csharp.js');
    return new CSharpExtractor();
  });

  extractorRegistry.registerFactory('c', async () => {
    const { CExtractor } = await import('./c-cpp.js');
    return new CExtractor();
  });

  extractorRegistry.registerFactory('cpp', async () => {
    const { CppExtractor } = await import('./c-cpp.js');
    return new CppExtractor();
  });

  extractorRegistry.registerFactory('ruby', async () => {
    const { RubyExtractor } = await import('./ruby.js');
    return new RubyExtractor();
  });

  // P2 Languages: HCL, Kotlin, Swift, Scala, Lua
  extractorRegistry.registerFactory('hcl', async () => {
    const { HclExtractor } = await import('./hcl.js');
    return new HclExtractor();
  });

  extractorRegistry.registerFactory('kotlin', async () => {
    const { KotlinExtractor } = await import('./kotlin.js');
    return new KotlinExtractor();
  });

  extractorRegistry.registerFactory('swift', async () => {
    const { SwiftExtractor } = await import('./swift.js');
    return new SwiftExtractor();
  });

  extractorRegistry.registerFactory('scala', async () => {
    const { ScalaExtractor } = await import('./scala.js');
    return new ScalaExtractor();
  });

  extractorRegistry.registerFactory('lua', async () => {
    const { LuaExtractor } = await import('./lua.js');
    return new LuaExtractor();
  });
}

// Auto-register on import
registerAllExtractors();

// Re-export types
export type { BaseExtractor, LanguageConfig, SyntaxTree, SyntaxNode } from './base-extractor.js';
