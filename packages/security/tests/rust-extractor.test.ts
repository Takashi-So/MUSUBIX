/**
 * @fileoverview Rust Extractor Tests
 * @module @nahisaho/musubix-security/tests/rust-extractor.test
 * @trace TSK-026
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { RustExtractor, createRustExtractor } from '../src/extractors/rust-extractor.js';

describe('RustExtractor', () => {
  let extractor: RustExtractor;

  beforeEach(() => {
    extractor = createRustExtractor();
  });

  describe('constructor', () => {
    it('should create instance with correct language', () => {
      expect(extractor).toBeInstanceOf(RustExtractor);
      expect(extractor.language).toBe('rust');
    });

    it('should create instance via factory function', () => {
      const instance = createRustExtractor();
      expect(instance).toBeInstanceOf(RustExtractor);
    });

    it('should support correct file extensions', () => {
      expect(extractor.extensions).toContain('.rs');
    });

    it('should detect supported files', () => {
      expect(extractor.supports('main.rs')).toBe(true);
      expect(extractor.supports('lib.rs')).toBe(true);
      expect(extractor.supports('file.go')).toBe(false);
    });
  });

  describe('getFrameworkModels', () => {
    it('should return framework models', () => {
      const models = extractor.getFrameworkModels();
      expect(Array.isArray(models)).toBe(true);
      expect(models.length).toBeGreaterThan(0);
    });

    it('should have Rust Unsafe model', () => {
      const models = extractor.getFrameworkModels();
      const unsafeModel = models.find(m => m.name === 'Rust Unsafe');
      
      expect(unsafeModel).toBeDefined();
      expect(unsafeModel?.sinks.some(s => s.vulnerabilityType === 'unsafe_code')).toBe(true);
    });

    it('should have Rust Process model', () => {
      const models = extractor.getFrameworkModels();
      const processModel = models.find(m => m.name === 'Rust Process');
      
      expect(processModel).toBeDefined();
      expect(processModel?.sources.length).toBeGreaterThan(0);
      expect(processModel?.sinks.some(s => s.vulnerabilityType === 'command_injection')).toBe(true);
    });

    it('should have Rust FS model', () => {
      const models = extractor.getFrameworkModels();
      const fsModel = models.find(m => m.name === 'Rust FS');
      
      expect(fsModel).toBeDefined();
      expect(fsModel?.sinks.some(s => s.vulnerabilityType === 'path_traversal')).toBe(true);
    });

    it('should have Actix-web model', () => {
      const models = extractor.getFrameworkModels();
      const actixModel = models.find(m => m.name === 'Actix-web');
      
      expect(actixModel).toBeDefined();
      expect(actixModel?.sources.length).toBeGreaterThan(0);
    });

    it('should have SQLx model', () => {
      const models = extractor.getFrameworkModels();
      const sqlxModel = models.find(m => m.name === 'SQLx');
      
      expect(sqlxModel).toBeDefined();
      expect(sqlxModel?.sinks.some(s => s.vulnerabilityType === 'sql_injection')).toBe(true);
    });

    it('should have Rust Panic model', () => {
      const models = extractor.getFrameworkModels();
      const panicModel = models.find(m => m.name === 'Rust Panic');
      
      expect(panicModel).toBeDefined();
      expect(panicModel?.sinks.some(s => s.vulnerabilityType === 'panic')).toBe(true);
      expect(panicModel?.sanitizers.length).toBeGreaterThan(0);
    });
  });

  describe('extract', () => {
    it('should extract from simple Rust code', async () => {
      const code = `
fn main() {
    println!("Hello, World!");
}
      `;
      
      const result = await extractor.extract(code, 'main.rs');
      
      expect(result.language).toBe('rust');
      expect(result.filePath).toBe('main.rs');
      expect(result.ast).toBeDefined();
      expect(result.astNodes.size).toBeGreaterThan(0);
    });

    it('should detect sources in command line args', async () => {
      const code = `
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
}
      `;
      
      const result = await extractor.extract(code, 'main.rs');
      
      expect(result.dfg.sources.length).toBeGreaterThan(0);
    });

    it('should detect sinks in unsafe code', async () => {
      const code = `
fn danger() {
    unsafe {
        let ptr = std::mem::transmute::<u64, *const u8>(0);
    }
}
      `;
      
      const result = await extractor.extract(code, 'danger.rs');
      
      expect(result.dfg.sinks.length).toBeGreaterThan(0);
    });

    it('should detect sinks in command execution', async () => {
      const code = `
use std::process::Command;

fn run_command(cmd: &str) {
    Command::new(cmd).spawn();
}
      `;
      
      const result = await extractor.extract(code, 'exec.rs');
      
      expect(result.dfg.sinks.length).toBeGreaterThan(0);
    });
  });

  describe('isUnsafe', () => {
    it('should detect unsafe blocks', async () => {
      const code = `
fn danger() {
    unsafe {
        // dangerous code
    }
}
      `;
      
      const result = await extractor.extract(code, 'test.rs');
      
      // Find the unsafe block
      let foundUnsafe = false;
      for (const [_id, node] of result.astNodes) {
        if (extractor.isUnsafe(node)) {
          foundUnsafe = true;
          break;
        }
      }
      
      expect(foundUnsafe).toBe(true);
    });
  });
});
