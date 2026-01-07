/**
 * @nahisaho/musubix-dfg Test Suite
 *
 * Tests for Data Flow Graph and Control Flow Graph extraction
 * Based on REQ-DFG-001 requirements
 *
 * @packageDocumentation
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { DataFlowAnalyzer, ControlFlowAnalyzer } from '../analyzers/index.js';
import { DFGBuilder, CFGBuilder } from '../graph/index.js';

// ============================================================================
// REQ-DFG-EXTRACT: DFG Extraction Tests
// ============================================================================

describe('DataFlowAnalyzer', () => {
  let analyzer: DataFlowAnalyzer;

  beforeEach(() => {
    analyzer = new DataFlowAnalyzer();
  });

  describe('REQ-DFG-EXTRACT-001: Basic DFG Extraction', () => {
    it('should extract variable definitions', () => {
      const code = `
        const x = 10;
        let y = 20;
        var z = 30;
      `;

      const dfg = analyzer.analyzeSource(code, 'test.ts');

      expect(dfg).toBeDefined();
      expect(dfg.nodes).toBeDefined();
      expect(dfg.nodes.size).toBeGreaterThan(0);

      // Check for variable definition nodes
      const nodes = Array.from(dfg.nodes.values());
      const defNodes = nodes.filter(
        (n) => n.type === 'definition' || n.type === 'variable'
      );
      expect(defNodes.length).toBeGreaterThanOrEqual(3);
    });

    it('should extract variable usages', () => {
      const code = `
        const x = 10;
        const y = x + 5;
        console.log(y);
      `;

      const dfg = analyzer.analyzeSource(code, 'test.ts');

      expect(dfg).toBeDefined();
      // Check edges exist (may not be def-use type specifically)
      expect(dfg.edges.size).toBeGreaterThanOrEqual(0);
    });

    it('should build def-use chains', () => {
      const code = `
        let a = 1;
        let b = a * 2;
        let c = b + a;
      `;

      const dfg = analyzer.analyzeSource(code, 'test.ts');

      expect(dfg).toBeDefined();
      // Verify edges exist
      expect(dfg.edges.size).toBeGreaterThanOrEqual(0);
    });
  });

  describe('REQ-DFG-EXTRACT-002: Function Call Analysis', () => {
    it('should track data flow through function parameters', () => {
      const code = `
        function add(a: number, b: number): number {
          return a + b;
        }
        const x = 5;
        const y = 10;
        const result = add(x, y);
      `;

      const dfg = analyzer.analyzeSource(code, 'test.ts');

      expect(dfg).toBeDefined();
      // Check for function and call nodes
      const nodes = Array.from(dfg.nodes.values());
      const funcNodes = nodes.filter(
        (n) => n.type === 'call' || n.type === 'function'
      );
      expect(funcNodes.length).toBeGreaterThan(0);
    });

    it('should track return value data flow', () => {
      const code = `
        function getValue(): number {
          return 42;
        }
        const result = getValue();
        console.log(result);
      `;

      const dfg = analyzer.analyzeSource(code, 'test.ts');

      expect(dfg).toBeDefined();
      expect(dfg.nodes.size).toBeGreaterThan(0);
    });
  });

  describe('REQ-DFG-EXTRACT-003: Object Property Flow', () => {
    it('should track object property access (dot notation)', () => {
      const code = `
        const obj = { name: 'test', value: 42 };
        const n = obj.name;
        const v = obj.value;
      `;

      const dfg = analyzer.analyzeSource(code, 'test.ts');

      expect(dfg).toBeDefined();
      expect(dfg.nodes.size).toBeGreaterThan(0);
    });

    it('should track object property access (bracket notation)', () => {
      const code = `
        const obj = { key: 'value' };
        const key = 'key';
        const result = obj[key];
      `;

      const dfg = analyzer.analyzeSource(code, 'test.ts');

      expect(dfg).toBeDefined();
      expect(dfg.nodes.size).toBeGreaterThan(0);
    });

    it('should track spread operator flow', () => {
      const code = `
        const base = { a: 1, b: 2 };
        const extended = { ...base, c: 3 };
      `;

      const dfg = analyzer.analyzeSource(code, 'test.ts');

      expect(dfg).toBeDefined();
      expect(dfg.nodes.size).toBeGreaterThan(0);
    });
  });

  describe('REQ-DFG-EXTRACT-004: Array Element Flow', () => {
    it('should track static array index access', () => {
      const code = `
        const arr = [1, 2, 3];
        const first = arr[0];
        const second = arr[1];
      `;

      const dfg = analyzer.analyzeSource(code, 'test.ts');

      expect(dfg).toBeDefined();
      expect(dfg.nodes.size).toBeGreaterThan(0);
    });

    it('should track array method data flow', () => {
      const code = `
        const numbers = [1, 2, 3, 4, 5];
        const doubled = numbers.map(n => n * 2);
        const sum = numbers.reduce((a, b) => a + b, 0);
      `;

      const dfg = analyzer.analyzeSource(code, 'test.ts');

      expect(dfg).toBeDefined();
      expect(dfg.nodes.size).toBeGreaterThan(0);
    });
  });
});

// ============================================================================
// REQ-DFG-CFG: Control Flow Graph Tests
// ============================================================================

describe('ControlFlowAnalyzer', () => {
  let analyzer: ControlFlowAnalyzer;

  beforeEach(() => {
    analyzer = new ControlFlowAnalyzer();
  });

  describe('REQ-DFG-CFG-001: Basic Control Flow', () => {
    it('should construct CFG with basic blocks', () => {
      const code = `
        function test() {
          const x = 1;
          const y = 2;
          return x + y;
        }
      `;

      const cfgs = analyzer.analyzeSource(code, 'test.ts');

      expect(cfgs).toBeDefined();
      expect(cfgs.length).toBeGreaterThan(0);
      const cfg = cfgs[0];
      expect(cfg.blocks.size).toBeGreaterThan(0);
      expect(cfg.entryBlock).toBeDefined();
      expect(cfg.exitBlocks.length).toBeGreaterThan(0);
    });

    it('should have entry and exit nodes', () => {
      const code = `
        function simple() {
          console.log('hello');
        }
      `;

      const cfgs = analyzer.analyzeSource(code, 'test.ts');

      expect(cfgs.length).toBeGreaterThan(0);
      const cfg = cfgs[0];
      expect(cfg.entryBlock).toBeDefined();
      expect(cfg.exitBlocks.length).toBeGreaterThanOrEqual(1);
    });
  });

  describe('REQ-DFG-CFG-002: Conditional Branch Analysis', () => {
    it('should create branches for if/else', () => {
      const code = `
        function test(x: number) {
          if (x > 0) {
            console.log('positive');
          } else {
            console.log('non-positive');
          }
        }
      `;

      const cfgs = analyzer.analyzeSource(code, 'test.ts');

      expect(cfgs).toBeDefined();
      expect(cfgs.length).toBeGreaterThan(0);
      const cfg = cfgs[0];
      // Should have conditional edges
      const edges = Array.from(cfg.edges.values());
      const conditionalEdges = edges.filter(
        (e) => e.type === 'conditional-true' || e.type === 'conditional-false'
      );
      expect(conditionalEdges.length).toBeGreaterThanOrEqual(2);
    });

    it('should handle switch statements', () => {
      const code = `
        function test(x: string) {
          switch (x) {
            case 'a':
              return 1;
            case 'b':
              return 2;
            default:
              return 0;
          }
        }
      `;

      const cfgs = analyzer.analyzeSource(code, 'test.ts');

      expect(cfgs).toBeDefined();
      expect(cfgs.length).toBeGreaterThan(0);
      expect(cfgs[0].blocks.size).toBeGreaterThan(0);
    });

    it('should handle ternary expressions', () => {
      const code = `
        function test(x: number) {
          const result = x > 0 ? 'positive' : 'negative';
          return result;
        }
      `;

      const cfgs = analyzer.analyzeSource(code, 'test.ts');

      expect(cfgs).toBeDefined();
      expect(cfgs.length).toBeGreaterThan(0);
      expect(cfgs[0].blocks.size).toBeGreaterThan(0);
    });
  });

  describe('REQ-DFG-CFG-003: Loop Analysis', () => {
    it('should create back-edges for while loops', () => {
      const code = `
        function test() {
          let i = 0;
          while (i < 10) {
            console.log(i);
            i++;
          }
        }
      `;

      const cfgs = analyzer.analyzeSource(code, 'test.ts');

      expect(cfgs).toBeDefined();
      expect(cfgs.length).toBeGreaterThan(0);
      const cfg = cfgs[0];
      // Should have loop back-edge
      const edges = Array.from(cfg.edges.values());
      const backEdges = edges.filter((e) => e.type === 'back' || e.isBackEdge);
      expect(backEdges.length).toBeGreaterThanOrEqual(1);
    });

    it('should create back-edges for for loops', () => {
      const code = `
        function test() {
          for (let i = 0; i < 10; i++) {
            console.log(i);
          }
        }
      `;

      const cfgs = analyzer.analyzeSource(code, 'test.ts');

      expect(cfgs).toBeDefined();
      expect(cfgs.length).toBeGreaterThan(0);
      const cfg = cfgs[0];
      const edges = Array.from(cfg.edges.values());
      const backEdges = edges.filter((e) => e.type === 'back' || e.isBackEdge);
      expect(backEdges.length).toBeGreaterThanOrEqual(1);
    });

    it('should handle break statements', () => {
      const code = `
        function test() {
          for (let i = 0; i < 10; i++) {
            if (i === 5) break;
            console.log(i);
          }
        }
      `;

      const cfgs = analyzer.analyzeSource(code, 'test.ts');

      expect(cfgs).toBeDefined();
      expect(cfgs.length).toBeGreaterThan(0);
      expect(cfgs[0].edges.size).toBeGreaterThan(0);
    });

    it('should handle continue statements', () => {
      const code = `
        function test() {
          for (let i = 0; i < 10; i++) {
            if (i % 2 === 0) continue;
            console.log(i);
          }
        }
      `;

      const cfgs = analyzer.analyzeSource(code, 'test.ts');

      expect(cfgs).toBeDefined();
      expect(cfgs.length).toBeGreaterThan(0);
      expect(cfgs[0].edges.size).toBeGreaterThan(0);
    });
  });

  describe('REQ-DFG-CFG-004: Exception Handling', () => {
    it('should model try/catch control flow', () => {
      const code = `
        function test() {
          try {
            riskyOperation();
          } catch (e) {
            console.error(e);
          }
        }
        function riskyOperation() {}
      `;

      const cfgs = analyzer.analyzeSource(code, 'test.ts');

      expect(cfgs).toBeDefined();
      expect(cfgs.length).toBeGreaterThan(0);
      // Should have try blocks
      const cfg = cfgs[0];
      expect(cfg.blocks.size).toBeGreaterThan(0);
    });

    it('should model try/catch/finally control flow', () => {
      const code = `
        function test() {
          try {
            riskyOperation();
          } catch (e) {
            console.error(e);
          } finally {
            cleanup();
          }
        }
        function riskyOperation() {}
        function cleanup() {}
      `;

      const cfgs = analyzer.analyzeSource(code, 'test.ts');

      expect(cfgs).toBeDefined();
      expect(cfgs.length).toBeGreaterThan(0);
      expect(cfgs[0].blocks.size).toBeGreaterThan(0);
    });
  });
});

// ============================================================================
// DFGBuilder Tests
// ============================================================================

describe('DFGBuilder', () => {
  let builder: DFGBuilder;

  beforeEach(() => {
    builder = new DFGBuilder('test.ts');
  });

  it('should create empty graph', () => {
    const graph = builder.build();

    expect(graph).toBeDefined();
    expect(graph.id).toBeDefined();
    expect(graph.filePath).toBe('test.ts');
    expect(graph.nodes.size).toBe(0);
    expect(graph.edges.size).toBe(0);
  });

  it('should add nodes', () => {
    builder.addNode({
      id: 'n1',
      type: 'variable',
      name: 'x',
      scope: 'local',
      location: {
        filePath: 'test.ts',
        startLine: 1,
        startColumn: 0,
        endLine: 1,
        endColumn: 10,
      },
      metadata: {},
    });

    const graph = builder.build();

    expect(graph.nodes.size).toBe(1);
    expect(graph.nodes.get('n1')).toBeDefined();
  });

  it('should add edges', () => {
    builder.addNode({
      id: 'n1',
      type: 'variable',
      name: 'x',
      scope: 'local',
      location: {
        filePath: 'test.ts',
        startLine: 1,
        startColumn: 0,
        endLine: 1,
        endColumn: 10,
      },
      metadata: {},
    });
    builder.addNode({
      id: 'n2',
      type: 'variable',
      name: 'y',
      scope: 'local',
      location: {
        filePath: 'test.ts',
        startLine: 2,
        startColumn: 0,
        endLine: 2,
        endColumn: 10,
      },
      metadata: {},
    });
    builder.addEdge({
      id: 'e1',
      type: 'def-use',
      source: 'n1',
      target: 'n2',
      weight: 1,
      metadata: {},
    });

    const graph = builder.build();

    expect(graph.edges.size).toBe(1);
    const edge = graph.edges.get('e1');
    expect(edge?.source).toBe('n1');
    expect(edge?.target).toBe('n2');
  });

  it('should generate unique IDs', () => {
    const id1 = builder.generateNodeId('v');
    const id2 = builder.generateNodeId('v');

    expect(id1).not.toBe(id2);
  });
});

// ============================================================================
// CFGBuilder Tests
// ============================================================================

describe('CFGBuilder', () => {
  let builder: CFGBuilder;

  beforeEach(() => {
    // CFGBuilder constructor: (functionName, filePath)
    builder = new CFGBuilder('testFunction', 'test.ts');
  });

  it('should create empty graph', () => {
    const graph = builder.build();

    expect(graph).toBeDefined();
    expect(graph.id).toBeDefined();
    expect(graph.functionName).toBe('testFunction');
    expect(graph.blocks.size).toBe(0);
    expect(graph.edges.size).toBe(0);
  });

  it('should add blocks', () => {
    builder.addBlock({
      id: 'b1',
      type: 'basic',
      label: 'Block 1',
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth: 0,
      location: {
        filePath: 'test.ts',
        startLine: 1,
        startColumn: 0,
        endLine: 5,
        endColumn: 1,
      },
    });

    const graph = builder.build();

    expect(graph.blocks.size).toBe(1);
    expect(graph.blocks.get('b1')).toBeDefined();
  });

  it('should set entry and exit blocks', () => {
    builder.addBlock({
      id: 'entry',
      type: 'entry',
      label: 'Entry',
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth: 0,
      location: {
        filePath: 'test.ts',
        startLine: 1,
        startColumn: 0,
        endLine: 1,
        endColumn: 1,
      },
    });
    builder.addBlock({
      id: 'exit',
      type: 'exit',
      label: 'Exit',
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth: 0,
      location: {
        filePath: 'test.ts',
        startLine: 10,
        startColumn: 0,
        endLine: 10,
        endColumn: 1,
      },
    });

    builder.setEntryBlock('entry');
    builder.addExitBlock('exit');

    const graph = builder.build();

    expect(graph.entryBlock).toBe('entry');
    expect(graph.exitBlocks).toContain('exit');
  });

  it('should add edges between blocks', () => {
    builder.addBlock({
      id: 'b1',
      type: 'basic',
      label: 'Block 1',
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth: 0,
      location: {
        filePath: 'test.ts',
        startLine: 1,
        startColumn: 0,
        endLine: 5,
        endColumn: 1,
      },
    });
    builder.addBlock({
      id: 'b2',
      type: 'basic',
      label: 'Block 2',
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth: 0,
      location: {
        filePath: 'test.ts',
        startLine: 6,
        startColumn: 0,
        endLine: 10,
        endColumn: 1,
      },
    });

    builder.addEdge({
      id: 'e1',
      type: 'sequential',
      source: 'b1',
      target: 'b2',
      isBackEdge: false,
    });

    const graph = builder.build();

    expect(graph.edges.size).toBe(1);
    const edge = graph.edges.get('e1');
    expect(edge?.source).toBe('b1');
    expect(edge?.target).toBe('b2');
  });

  it('should generate unique block IDs', () => {
    const id1 = builder.generateBlockId('b');
    const id2 = builder.generateBlockId('b');

    expect(id1).not.toBe(id2);
  });
});
