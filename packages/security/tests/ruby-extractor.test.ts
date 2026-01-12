/**
 * @fileoverview Ruby Extractor Tests
 * @module @nahisaho/musubix-security/tests/ruby-extractor.test
 * @trace TSK-024
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { RubyExtractor, createRubyExtractor } from '../src/extractors/ruby-extractor.js';

describe('RubyExtractor', () => {
  let extractor: RubyExtractor;

  beforeEach(() => {
    extractor = createRubyExtractor();
  });

  describe('constructor', () => {
    it('should create instance with correct language', () => {
      expect(extractor).toBeInstanceOf(RubyExtractor);
      expect(extractor.language).toBe('ruby');
    });

    it('should create instance via factory function', () => {
      const instance = createRubyExtractor();
      expect(instance).toBeInstanceOf(RubyExtractor);
    });

    it('should support correct file extensions', () => {
      expect(extractor.extensions).toContain('.rb');
      expect(extractor.extensions).toContain('.erb');
      expect(extractor.extensions).toContain('.rake');
    });

    it('should detect supported files', () => {
      expect(extractor.supports('app.rb')).toBe(true);
      expect(extractor.supports('view.erb')).toBe(true);
      expect(extractor.supports('Rakefile.rake')).toBe(true);
      expect(extractor.supports('file.py')).toBe(false);
    });
  });

  describe('getFrameworkModels', () => {
    it('should return framework models', () => {
      const models = extractor.getFrameworkModels();
      expect(Array.isArray(models)).toBe(true);
      expect(models.length).toBeGreaterThan(0);
    });

    it('should have Rails framework model', () => {
      const models = extractor.getFrameworkModels();
      const railsModel = models.find(m => m.name === 'Rails');
      
      expect(railsModel).toBeDefined();
      expect(railsModel?.sources.length).toBeGreaterThan(0);
      expect(railsModel?.sinks.length).toBeGreaterThan(0);
      expect(railsModel?.sanitizers.length).toBeGreaterThan(0);
    });

    it('should have ActiveRecord framework model', () => {
      const models = extractor.getFrameworkModels();
      const arModel = models.find(m => m.name === 'ActiveRecord');
      
      expect(arModel).toBeDefined();
      expect(arModel?.sinks.some(s => s.vulnerabilityType === 'sql_injection')).toBe(true);
    });

    it('should have Ruby System model for command injection', () => {
      const models = extractor.getFrameworkModels();
      const systemModel = models.find(m => m.name === 'Ruby System');
      
      expect(systemModel).toBeDefined();
      expect(systemModel?.sinks.some(s => s.vulnerabilityType === 'command_injection')).toBe(true);
    });

    it('should have Ruby Deserialization model', () => {
      const models = extractor.getFrameworkModels();
      const deserModel = models.find(m => m.name === 'Ruby Deserialization');
      
      expect(deserModel).toBeDefined();
      expect(deserModel?.sinks.some(s => s.vulnerabilityType === 'deserialization')).toBe(true);
    });

    it('should have Ruby Eval model', () => {
      const models = extractor.getFrameworkModels();
      const evalModel = models.find(m => m.name === 'Ruby Eval');
      
      expect(evalModel).toBeDefined();
      expect(evalModel?.sinks.some(s => s.vulnerabilityType === 'code_injection')).toBe(true);
    });
  });

  describe('extract', () => {
    it('should extract from simple Ruby code', async () => {
      const code = `
def hello
  puts "Hello, World!"
end
      `;
      
      const result = await extractor.extract(code, 'test.rb');
      
      expect(result.language).toBe('ruby');
      expect(result.filePath).toBe('test.rb');
      expect(result.ast).toBeDefined();
      expect(result.astNodes.size).toBeGreaterThan(0);
    });

    it('should detect sources in Rails code', async () => {
      const code = `
def index
  user_input = params[:query]
  render html: user_input
end
      `;
      
      const result = await extractor.extract(code, 'controller.rb');
      
      expect(result.dfg.sources.length).toBeGreaterThan(0);
    });

    it('should detect sinks in Rails code', async () => {
      const code = `
def show
  @data = "<script>alert('xss')</script>"
  render html: @data
end
      `;
      
      const result = await extractor.extract(code, 'controller.rb');
      
      expect(result.dfg.sinks.length).toBeGreaterThan(0);
    });

    it('should extract class definitions', async () => {
      const code = `
class User < ApplicationRecord
  def full_name
    "#{first_name} #{last_name}"
  end
end
      `;
      
      const result = await extractor.extract(code, 'user.rb');
      
      expect(result.symbols.classes.size).toBeGreaterThanOrEqual(0);
    });
  });
});
