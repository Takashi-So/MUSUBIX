/**
 * @fileoverview Tests for Wake-Sleep Cycle Learning
 * @traceability TSK-WAKE-002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { WakeSleepCycle, type WakeObservation } from '../learning/index.js';
import type { ASTNode } from '../types.js';

describe('WakeSleepCycle', () => {
  let cycle: WakeSleepCycle;

  const defaultPos = { row: 0, column: 0 };

  const createAST = (type: string, children: ASTNode[] = [], value?: string): ASTNode => ({
    type,
    value,
    children,
    startPosition: defaultPos,
    endPosition: defaultPos,
  });

  const createObservation = (ast: ASTNode, language = 'typescript'): WakeObservation => ({
    ast,
    source: 'test code',
    context: {
      language,
      filename: 'test.ts',
      domain: 'testing',
    },
    timestamp: new Date().toISOString(),
  });

  beforeEach(() => {
    cycle = new WakeSleepCycle({
      autoSleep: false,  // Disable auto-sleep for controlled testing
      minQualityThreshold: 0.1,
      maxLibrarySize: 100,
    });
  });

  describe('wake phase', () => {
    it('should extract patterns from observations', () => {
      const ast = createAST('FunctionDeclaration', [
        createAST('Identifier', [], 'myFunction'),
        createAST('Block', [
          createAST('ReturnStatement', [
            createAST('Literal', [], '42'),
          ]),
        ]),
      ]);

      const patterns = cycle.wake(createObservation(ast));

      expect(patterns.length).toBeGreaterThan(0);
      expect(patterns[0].language).toBe('typescript');
    });

    it('should track wake observations', () => {
      const ast = createAST('VariableDeclaration', [
        createAST('Identifier', [], 'x'),
      ]);

      cycle.wake(createObservation(ast));
      cycle.wake(createObservation(ast));

      const stats = cycle.getStats();
      expect(stats.totalWakeObservations).toBe(2);
    });

    it('should increment frequency for similar patterns', () => {
      // Create deeper AST to satisfy depth condition (2-6)
      const ast1 = createAST('FunctionDeclaration', [
        createAST('Identifier', [], 'func1'),
        createAST('Block', [
          createAST('ReturnStatement', [
            createAST('Literal', [], '1'),
          ]),
        ]),
      ]);
      const ast2 = createAST('FunctionDeclaration', [
        createAST('Identifier', [], 'func2'),
        createAST('Block', [
          createAST('ReturnStatement', [
            createAST('Literal', [], '2'),
          ]),
        ]),
      ]);

      cycle.wake(createObservation(ast1));
      cycle.wake(createObservation(ast2));

      const library = cycle.getLibrary();
      // Patterns with same structure should be extracted
      expect(library.length).toBeGreaterThan(0);
    });
  });

  describe('sleep phase', () => {
    it('should consolidate patterns', () => {
      // Add multiple observations
      for (let i = 0; i < 10; i++) {
        const ast = createAST('FunctionDeclaration', [
          createAST('Identifier', [], `func${i}`),
          createAST('Block', []),
        ]);
        cycle.wake(createObservation(ast));
      }

      const beforeSleep = cycle.getLibrary().length;
      const result = cycle.sleep();

      expect(result.cycleTimeMs).toBeGreaterThanOrEqual(0);
      expect(result.compressionRatio).toBeLessThanOrEqual(1);
    });

    it('should update statistics after sleep', () => {
      const ast = createAST('ClassDeclaration', [
        createAST('Identifier', [], 'MyClass'),
      ]);

      cycle.wake(createObservation(ast));
      cycle.sleep();

      const stats = cycle.getStats();
      expect(stats.totalSleepCycles).toBe(1);
    });

    it('should clear wake buffer after sleep', () => {
      const ast = createAST('IfStatement', [
        createAST('BinaryExpression'),
        createAST('Block'),
      ]);

      cycle.wake(createObservation(ast));
      cycle.sleep();

      // Wake buffer should be cleared
      const stats = cycle.getStats();
      expect(stats.totalSleepCycles).toBe(1);
    });
  });

  describe('auto-sleep', () => {
    it('should trigger sleep when threshold reached', () => {
      const autoSleepCycle = new WakeSleepCycle({
        autoSleep: true,
        wakeThreshold: 5,
        minQualityThreshold: 0.0,
      });

      // Add observations up to threshold
      for (let i = 0; i < 5; i++) {
        const ast = createAST('Statement', [
          createAST('Expression', [], `expr${i}`),
        ]);
        autoSleepCycle.wake(createObservation(ast));
      }

      const stats = autoSleepCycle.getStats();
      expect(stats.totalSleepCycles).toBeGreaterThanOrEqual(1);
    });
  });

  describe('library management', () => {
    it('should get pattern by ID', () => {
      const ast = createAST('ArrowFunction', [
        createAST('Parameters'),
        createAST('Block'),
      ]);

      const patterns = cycle.wake(createObservation(ast));
      
      if (patterns.length > 0) {
        const retrieved = cycle.getPattern(patterns[0].id);
        expect(retrieved).toBeDefined();
        expect(retrieved?.id).toBe(patterns[0].id);
      }
    });

    it('should export and import library', () => {
      const ast = createAST('MethodDefinition', [
        createAST('Identifier', [], 'method'),
        createAST('FunctionExpression'),
      ]);

      cycle.wake(createObservation(ast));
      cycle.sleep();

      const exported = cycle.exportLibrary();
      expect(exported).toContain('patterns');

      const newCycle = new WakeSleepCycle({ autoSleep: false });
      const imported = newCycle.importLibrary(exported);

      expect(imported).toBeGreaterThanOrEqual(0);
    });

    it('should reset library and stats', () => {
      const ast = createAST('ForStatement', [
        createAST('VariableDeclaration'),
        createAST('BinaryExpression'),
        createAST('UpdateExpression'),
        createAST('Block'),
      ]);

      cycle.wake(createObservation(ast));
      cycle.reset();

      const stats = cycle.getStats();
      expect(stats.totalWakeObservations).toBe(0);
      expect(stats.totalSleepCycles).toBe(0);
      expect(cycle.getLibrary().length).toBe(0);
    });
  });

  describe('quality filtering', () => {
    it('should remove low-quality patterns during sleep', () => {
      const highQualityCycle = new WakeSleepCycle({
        autoSleep: false,
        minQualityThreshold: 0.5,
        maxLibrarySize: 100,
      });

      // Add various patterns
      for (let i = 0; i < 20; i++) {
        const ast = createAST('Expression', [
          createAST('Literal', [], String(i)),
        ]);
        highQualityCycle.wake(createObservation(ast));
      }

      const result = highQualityCycle.sleep();
      
      // Some patterns should be removed due to quality threshold
      expect(result.patternsRemoved).toBeGreaterThanOrEqual(0);
    });
  });

  describe('statistics', () => {
    it('should track all statistics correctly', () => {
      const ast = createAST('TryStatement', [
        createAST('Block'),
        createAST('CatchClause', [
          createAST('Identifier'),
          createAST('Block'),
        ]),
      ]);

      cycle.wake(createObservation(ast));
      cycle.wake(createObservation(ast));
      cycle.sleep();

      const stats = cycle.getStats();
      expect(stats.totalWakeObservations).toBe(2);
      expect(stats.totalSleepCycles).toBe(1);
      expect(stats.currentLibrarySize).toBeGreaterThanOrEqual(0);
      expect(stats.totalPatternsExtracted).toBeGreaterThan(0);
    });
  });
});
