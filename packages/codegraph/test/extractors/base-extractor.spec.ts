/**
 * @nahisaho/musubix-codegraph - BaseExtractor Unit Tests
 *
 * Unit tests for the BaseExtractor abstract class and ExtractorRegistry
 *
 * @see REQ-CG-MULTILANG-001
 * @see TSK-CG-040
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { extractorRegistry, registerAllExtractors } from '../../src/parser/extractors/index.js';
import type { Language } from '../../src/types.js';

describe('ExtractorRegistry', () => {
  beforeEach(() => {
    // Clear and re-register all extractors
    extractorRegistry.clear();
    registerAllExtractors();
  });

  describe('getRegisteredLanguages', () => {
    it('should return all 16 supported languages', () => {
      const languages = extractorRegistry.getRegisteredLanguages();
      
      expect(languages).toContain('typescript');
      expect(languages).toContain('javascript');
      expect(languages).toContain('python');
      expect(languages).toContain('rust');
      expect(languages).toContain('go');
      expect(languages).toContain('java');
      expect(languages).toContain('php');
      expect(languages).toContain('csharp');
      expect(languages).toContain('c');
      expect(languages).toContain('cpp');
      expect(languages).toContain('ruby');
      expect(languages).toContain('hcl');
      expect(languages).toContain('kotlin');
      expect(languages).toContain('swift');
      expect(languages).toContain('scala');
      expect(languages).toContain('lua');
      
      expect(languages.length).toBe(16);
    });
  });

  describe('isLanguageSupported (hasExtractor)', () => {
    it('should return true for supported languages', () => {
      expect(extractorRegistry.hasExtractor('typescript')).toBe(true);
      expect(extractorRegistry.hasExtractor('python')).toBe(true);
      expect(extractorRegistry.hasExtractor('rust')).toBe(true);
      expect(extractorRegistry.hasExtractor('go')).toBe(true);
      expect(extractorRegistry.hasExtractor('java')).toBe(true);
    });

    it('should return false for unsupported languages', () => {
      expect(extractorRegistry.hasExtractor('cobol' as Language)).toBe(false);
      expect(extractorRegistry.hasExtractor('fortran' as Language)).toBe(false);
    });
  });

  describe('getExtractor', () => {
    it('should return an extractor for TypeScript', async () => {
      const extractor = await extractorRegistry.getExtractor('typescript');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('typescript');
      expect(extractor?.getConfig()).toBeDefined();
    });

    it('should return an extractor for Python', async () => {
      const extractor = await extractorRegistry.getExtractor('python');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('python');
    });

    it('should return an extractor for Rust', async () => {
      const extractor = await extractorRegistry.getExtractor('rust');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('rust');
    });

    it('should return an extractor for Go', async () => {
      const extractor = await extractorRegistry.getExtractor('go');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('go');
    });

    it('should return an extractor for Java', async () => {
      const extractor = await extractorRegistry.getExtractor('java');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('java');
    });

    it('should return an extractor for PHP', async () => {
      const extractor = await extractorRegistry.getExtractor('php');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('php');
    });

    it('should return an extractor for C#', async () => {
      const extractor = await extractorRegistry.getExtractor('csharp');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('csharp');
    });

    it('should return an extractor for C', async () => {
      const extractor = await extractorRegistry.getExtractor('c');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('c');
    });

    it('should return an extractor for C++', async () => {
      const extractor = await extractorRegistry.getExtractor('cpp');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('cpp');
    });

    it('should return an extractor for Ruby', async () => {
      const extractor = await extractorRegistry.getExtractor('ruby');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('ruby');
    });

    it('should return an extractor for HCL/Terraform', async () => {
      const extractor = await extractorRegistry.getExtractor('hcl');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('hcl');
    });

    it('should return an extractor for Kotlin', async () => {
      const extractor = await extractorRegistry.getExtractor('kotlin');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('kotlin');
    });

    it('should return an extractor for Swift', async () => {
      const extractor = await extractorRegistry.getExtractor('swift');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('swift');
    });

    it('should return an extractor for Scala', async () => {
      const extractor = await extractorRegistry.getExtractor('scala');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('scala');
    });

    it('should return an extractor for Lua', async () => {
      const extractor = await extractorRegistry.getExtractor('lua');
      
      expect(extractor).toBeDefined();
      expect(extractor?.getLanguage()).toBe('lua');
    });

    it('should return null for unsupported language', async () => {
      const extractor = await extractorRegistry.getExtractor('cobol' as Language);
      
      expect(extractor).toBeUndefined();
    });
  });

  describe('Extractor Configuration', () => {
    it('TypeScript extractor should have correct file extensions', async () => {
      const extractor = await extractorRegistry.getExtractor('typescript');
      const config = extractor?.getConfig();
      
      expect(config?.extensions).toContain('.ts');
      expect(config?.extensions).toContain('.tsx');
    });

    it('Python extractor should have correct file extensions', async () => {
      const extractor = await extractorRegistry.getExtractor('python');
      const config = extractor?.getConfig();
      
      expect(config?.extensions).toContain('.py');
      // Note: .pyi is Python stub file, .pyw is Windows Python
    });

    it('Rust extractor should have correct file extensions', async () => {
      const extractor = await extractorRegistry.getExtractor('rust');
      const config = extractor?.getConfig();
      
      expect(config?.extensions).toContain('.rs');
    });

    it('Go extractor should have correct file extensions', async () => {
      const extractor = await extractorRegistry.getExtractor('go');
      const config = extractor?.getConfig();
      
      expect(config?.extensions).toContain('.go');
    });

    it('Java extractor should have correct file extensions', async () => {
      const extractor = await extractorRegistry.getExtractor('java');
      const config = extractor?.getConfig();
      
      expect(config?.extensions).toContain('.java');
    });

    it('HCL extractor should have correct file extensions', async () => {
      const extractor = await extractorRegistry.getExtractor('hcl');
      const config = extractor?.getConfig();
      
      expect(config?.extensions).toContain('.tf');
      expect(config?.extensions).toContain('.hcl');
    });
  });
});
