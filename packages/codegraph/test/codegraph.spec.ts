/**
 * @nahisaho/musubix-codegraph - CodeGraph Facade Tests
 *
 * @see TSK-CG-080
 * @see REQ-CG-API-001
 * @see REQ-CG-API-002
 * @see DES-CG-001
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { CodeGraph, createCodeGraph } from '../src/index.js';

describe('CodeGraph', () => {
  let codeGraph: CodeGraph;

  beforeEach(() => {
    codeGraph = createCodeGraph({ storage: 'memory' });
  });

  afterEach(async () => {
    if (codeGraph) {
      await codeGraph.close();
    }
  });

  describe('instantiation', () => {
    it('should create instance with default options', () => {
      const instance = new CodeGraph();
      expect(instance).toBeInstanceOf(CodeGraph);
      expect(instance.isInitialized()).toBe(false);
    });

    it('should create instance via factory function', () => {
      const instance = createCodeGraph({ storage: 'memory' });
      expect(instance).toBeInstanceOf(CodeGraph);
    });

    it('should accept memory storage option', () => {
      const instance = new CodeGraph({ storage: 'memory' });
      expect(instance).toBeInstanceOf(CodeGraph);
    });

    it('should accept sqlite storage option', () => {
      const instance = new CodeGraph({
        storage: 'sqlite',
        sqlitePath: '.codegraph/test.db',
      });
      expect(instance).toBeInstanceOf(CodeGraph);
    });
  });

  describe('lifecycle', () => {
    it('should not be initialized before first operation', () => {
      expect(codeGraph.isInitialized()).toBe(false);
    });

    it('should close cleanly', async () => {
      await codeGraph.close();
      expect(codeGraph.isInitialized()).toBe(false);
    });
  });

  describe('events', () => {
    it('should emit indexing events', async () => {
      const events: string[] = [];

      codeGraph.onIndexingStart((path) => {
        events.push(`start:${path}`);
      });

      codeGraph.onIndexingComplete((result) => {
        events.push(`complete:${result.entitiesIndexed}`);
      });

      // Will fail because indexer not implemented yet, but events should be emitted
      try {
        await codeGraph.index('./test-fixtures');
      } catch {
        // Expected to fail until indexer is implemented
      }

      // At least start event should be emitted
      expect(events.length).toBeGreaterThan(0);
      expect(events[0]).toMatch(/^start:/);
    });

    it('should emit query events', async () => {
      const events: string[] = [];

      codeGraph.onQueryStart((query) => {
        events.push(`query:${JSON.stringify(query)}`);
      });

      try {
        await codeGraph.query('test');
      } catch {
        // Expected to fail until graph engine is implemented
      }

      expect(events.length).toBeGreaterThan(0);
    });
  });
});

describe('exports', () => {
  it('should export CodeGraph class', async () => {
    const mod = await import('../src/index.js');
    expect(mod.CodeGraph).toBeDefined();
  });

  it('should export createCodeGraph factory', async () => {
    const mod = await import('../src/index.js');
    expect(mod.createCodeGraph).toBeDefined();
    expect(typeof mod.createCodeGraph).toBe('function');
  });

  it('should export TypedEventEmitter', async () => {
    const mod = await import('../src/index.js');
    expect(mod.TypedEventEmitter).toBeDefined();
  });

  it('should export CodeGraphEventEmitter', async () => {
    const mod = await import('../src/index.js');
    expect(mod.CodeGraphEventEmitter).toBeDefined();
  });

  it('should export LANGUAGE_EXTENSIONS', async () => {
    const mod = await import('../src/index.js');
    expect(mod.LANGUAGE_EXTENSIONS).toBeDefined();
    expect(mod.LANGUAGE_EXTENSIONS['.ts']).toBe('typescript');
  });

  it('should export DEFAULT_CODEGRAPH_OPTIONS', async () => {
    const mod = await import('../src/index.js');
    expect(mod.DEFAULT_CODEGRAPH_OPTIONS).toBeDefined();
  });

  it('should export utility functions', async () => {
    const mod = await import('../src/index.js');
    expect(mod.generateEntityId).toBeDefined();
    expect(mod.generateRelationId).toBeDefined();
    expect(mod.isSupportedLanguage).toBeDefined();
    expect(mod.getLanguageFromExtension).toBeDefined();
  });
});
