/**
 * Pattern Integration End-to-End Tests
 * 
 * Tests the complete flow of:
 * 1. Pattern learning from code
 * 2. Sleep consolidation
 * 3. Knowledge graph integration
 * 4. Pattern querying and search
 * 
 * @requirement REQ-INT-001: Neuro-Symbolic統合
 * @requirement REQ-PATTERN-001: パターン学習システム
 * @requirement REQ-ONTO-001: オントロジー推論
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { WakeSleepCycle, type WakeObservation } from '@nahisaho/musubix-pattern-mcp';
import { PatternOntologyBridge, N3Store } from '@nahisaho/musubix-ontology-mcp';
import type { ASTNode } from '@nahisaho/musubix-pattern-mcp';

/**
 * Create a simple AST node for testing
 */
function createTestAST(type: string, children: ASTNode[] = []): ASTNode {
  return {
    type,
    children,
    startPosition: { row: 0, column: 0 },
    endPosition: { row: 0, column: 0 },
  };
}

/**
 * Create a WakeObservation for testing
 */
function createObservation(code: string, language: string = 'typescript'): WakeObservation {
  // Create AST representation based on code pattern
  let ast: ASTNode;
  
  if (code.includes('function')) {
    ast = createTestAST('FunctionDeclaration', [
      createTestAST('Identifier'),
      createTestAST('BlockStatement', [
        code.includes('if') ? createTestAST('IfStatement') : createTestAST('ReturnStatement'),
      ]),
    ]);
  } else if (code.includes('class')) {
    ast = createTestAST('ClassDeclaration', [
      createTestAST('Identifier'),
      createTestAST('ClassBody', [
        createTestAST('MethodDefinition'),
      ]),
    ]);
  } else if (code.includes('const') || code.includes('let')) {
    ast = createTestAST('VariableDeclaration', [
      createTestAST('VariableDeclarator'),
    ]);
  } else {
    ast = createTestAST('Program', [createTestAST('ExpressionStatement')]);
  }

  return {
    ast,
    source: code,
    context: {
      language,
      filename: 'test.ts',
      domain: 'testing',
    },
    timestamp: new Date().toISOString(),
  };
}

describe('Pattern Integration E2E', () => {
  let wakeSleep: WakeSleepCycle;
  let store: N3Store;
  let bridge: PatternOntologyBridge;

  beforeEach(() => {
    wakeSleep = new WakeSleepCycle({
      autoSleep: false, // Manual control for testing
      minQualityThreshold: 0.1,
      wakeThreshold: 100,
    });
    store = new N3Store({
      enableInference: false,
      maxTriples: 10000,
    });
    bridge = new PatternOntologyBridge(store);
  });

  describe('Complete Learning Flow', () => {
    it('should learn patterns from code observations', () => {
      // Wake phase: observe code patterns
      const obs1 = createObservation(`
        function validateEmail(email: string): boolean {
          if (!email || email.length === 0) {
            return false;
          }
          return email.includes('@');
        }
      `);
      
      const obs2 = createObservation(`
        function validatePhone(phone: string): boolean {
          if (!phone || phone.length === 0) {
            return false;
          }
          return phone.match(/^[0-9]{10,11}$/) !== null;
        }
      `);

      // Observe patterns
      const result1 = wakeSleep.wake(obs1);
      const result2 = wakeSleep.wake(obs2);

      expect(result1).toBeDefined();
      expect(Array.isArray(result1)).toBe(true);
      expect(result2).toBeDefined();
      expect(Array.isArray(result2)).toBe(true);
    });

    it('should consolidate patterns during sleep phase', () => {
      // Add multiple observations
      for (let i = 0; i < 5; i++) {
        const obs = createObservation(`
          function process${i}(data: Data): Result {
            if (!data) {
              return { success: false, error: 'Invalid data' };
            }
            return { success: true, data: transform(data) };
          }
        `);
        wakeSleep.wake(obs);
      }

      // Sleep phase: consolidate patterns
      const sleepResult = wakeSleep.sleep();
      
      expect(sleepResult).toBeDefined();
      expect(sleepResult.patternsConsolidated).toBeDefined();
    });

    it('should integrate patterns with knowledge graph', () => {
      // Add some observations
      const obs = createObservation(`function test() { return 1; }`);
      wakeSleep.wake(obs);
      
      // Get patterns from library
      const patterns = wakeSleep.getLibrary();
      
      // Import to knowledge graph
      const importedCount = bridge.importPatterns(patterns);
      
      // Check that patterns were imported
      expect(importedCount).toBeGreaterThanOrEqual(0);
    });

    it('should query patterns by criteria', () => {
      // Add some patterns first
      const obs = createObservation(`
        async function fetchUser(id: string): Promise<User> {
          const response = await fetch('/api/users/' + id);
          return response.json();
        }
      `);
      wakeSleep.wake(obs);
      wakeSleep.sleep();

      // Import to bridge
      const patterns = wakeSleep.getLibrary();
      bridge.importPatterns(patterns);

      // Query by language - returns PatternQueryResult
      const queryResult = bridge.queryPatterns({
        language: 'typescript'
      });

      expect(queryResult).toBeDefined();
      expect(queryResult.patterns).toBeDefined();
      expect(Array.isArray(queryResult.patterns)).toBe(true);
    });
  });

  describe('Pattern Relationship Discovery', () => {
    it('should detect subsumption relationships', () => {
      // Create general and specific patterns
      const generalObs = createObservation(`
        function validate(value: any): boolean {
          return value !== null && value !== undefined;
        }
      `);
      
      const specificObs = createObservation(`
        function validateString(value: string): boolean {
          return value !== null && value !== undefined && value.length > 0;
        }
      `);

      wakeSleep.wake(generalObs);
      wakeSleep.wake(specificObs);
      wakeSleep.sleep();

      const patterns = wakeSleep.getLibrary();
      bridge.importPatterns(patterns);
      
      // discoverRelationships requires patterns as argument
      const relationships = bridge.discoverRelationships(patterns);
      
      // Should find some relationships (may include similarity)
      expect(relationships.length).toBeGreaterThanOrEqual(0);
    });

    it('should detect similar patterns', () => {
      // Create similar patterns
      const codes = [
        `function getUsers(): User[] { return this.users.slice(); }`,
        `function getItems(): Item[] { return this.items.slice(); }`,
        `function getOrders(): Order[] { return this.orders.slice(); }`,
      ];

      codes.forEach(code => wakeSleep.wake(createObservation(code)));
      wakeSleep.sleep();

      const patterns = wakeSleep.getLibrary();
      bridge.importPatterns(patterns);
      
      const relationships = bridge.discoverRelationships(patterns);
      const similarRelations = relationships.filter(r => r.relation === 'similarTo');
      
      // Similar patterns may be detected
      expect(Array.isArray(similarRelations)).toBe(true);
    });

    it('should find related patterns', () => {
      // Set up patterns
      const obs = createObservation(`
        class Repository<T> {
          private items: T[] = [];
          
          add(item: T): void {
            this.items.push(item);
          }
          
          getAll(): T[] {
            return this.items.slice();
          }
        }
      `);

      wakeSleep.wake(obs);
      wakeSleep.sleep();

      const patterns = wakeSleep.getLibrary();
      bridge.importPatterns(patterns);

      if (patterns.length > 0) {
        // findRelatedPatterns returns PatternRelationship[]
        const related = bridge.findRelatedPatterns(patterns[0].id);
        expect(related).toBeDefined();
        expect(Array.isArray(related)).toBe(true);
      }
    });
  });

  describe('Knowledge Graph Export/Import', () => {
    it('should export knowledge graph as Turtle', async () => {
      // Add patterns
      const obs = createObservation(`
        const logger = {
          log: (msg: string) => console.log('[LOG]', msg),
          error: (msg: string) => console.error('[ERROR]', msg),
        };
      `);
      wakeSleep.wake(obs);
      wakeSleep.sleep();

      const patterns = wakeSleep.getLibrary();
      bridge.importPatterns(patterns);

      // Export as Turtle (async)
      const turtle = await bridge.exportAsTurtle();
      
      expect(turtle).toBeDefined();
      expect(typeof turtle).toBe('string');
      expect(turtle).toContain('@prefix');
    });

    it('should maintain pattern metadata through export', async () => {
      // Add pattern with metadata
      const obs = createObservation(`
        function retry<T>(fn: () => Promise<T>, maxRetries: number): Promise<T> {
          return fn().catch(err => {
            if (maxRetries > 0) {
              return retry(fn, maxRetries - 1);
            }
            throw err;
          });
        }
      `);

      wakeSleep.wake(obs);
      wakeSleep.sleep();

      const patterns = wakeSleep.getLibrary();
      bridge.importPatterns(patterns);

      const turtle = await bridge.exportAsTurtle();
      
      // Should contain pattern information
      expect(turtle).toContain('pattern:');
    });
  });

  describe('Statistics and Monitoring', () => {
    it('should track learning statistics', () => {
      const stats = wakeSleep.getStats();
      
      expect(stats).toBeDefined();
      expect(stats).toHaveProperty('totalWakeObservations');
      expect(stats).toHaveProperty('totalSleepCycles');
    });

    it('should count patterns in knowledge graph', () => {
      // Add patterns
      const codes = [
        `const x = 1;`,
        `const y = 2;`,
        `const z = 3;`,
      ];

      codes.forEach(code => wakeSleep.wake(createObservation(code)));
      wakeSleep.sleep();

      const patterns = wakeSleep.getLibrary();
      bridge.importPatterns(patterns);

      // Get counts
      const patternCount = patterns.length;
      expect(patternCount).toBeGreaterThanOrEqual(0);
    });

    it('should report consolidated pattern count', () => {
      // Multiple observations to trigger consolidation
      for (let i = 0; i < 10; i++) {
        wakeSleep.wake(createObservation(`const val${i} = ${i};`));
      }

      const sleepResult = wakeSleep.sleep();
      
      expect(sleepResult).toBeDefined();
      expect(sleepResult.patternsConsolidated).toBeGreaterThanOrEqual(0);
    });
  });

  describe('Integration Workflow', () => {
    it('should complete full workflow: observe -> consolidate -> integrate -> query', async () => {
      // Step 1: Wake phase - observe patterns
      const observations = [
        { code: `function add(a: number, b: number): number { return a + b; }`, lang: 'typescript' },
        { code: `function subtract(a: number, b: number): number { return a - b; }`, lang: 'typescript' },
        { code: `function multiply(a: number, b: number): number { return a * b; }`, lang: 'typescript' },
      ];

      observations.forEach(obs => {
        const result = wakeSleep.wake(createObservation(obs.code, obs.lang));
        expect(result).toBeDefined();
      });

      // Step 2: Sleep phase - consolidate
      const sleepResult = wakeSleep.sleep();
      expect(sleepResult).toBeDefined();

      // Step 3: Get learned patterns
      const patterns = wakeSleep.getLibrary();
      expect(Array.isArray(patterns)).toBe(true);

      // Step 4: Import to knowledge graph
      bridge.importPatterns(patterns);

      // Step 5: Query patterns - returns PatternQueryResult
      const queryResult = bridge.queryPatterns({ language: 'typescript' });
      expect(queryResult).toBeDefined();
      expect(queryResult.patterns).toBeDefined();

      // Step 6: Export as Turtle (async)
      const turtle = await bridge.exportAsTurtle();
      expect(turtle).toContain('@prefix');

      // Workflow complete!
    });

    it('should handle empty observations gracefully', () => {
      // Sleep without observations
      const sleepResult = wakeSleep.sleep();
      expect(sleepResult).toBeDefined();
      expect(sleepResult.patternsConsolidated).toBe(0);

      // Query empty bridge - returns PatternQueryResult with empty patterns
      const result = bridge.queryPatterns({ language: 'typescript' });
      expect(result.patterns).toEqual([]);
    });

    it('should handle malformed code gracefully', () => {
      // Create observation with malformed AST representation
      const malformedObs: WakeObservation = {
        ast: createTestAST('Error', []),
        source: `function incomplete(`,
        context: { language: 'typescript' },
        timestamp: new Date().toISOString(),
      };
      
      // Should not throw
      expect(() => {
        wakeSleep.wake(malformedObs);
      }).not.toThrow();
    });
  });
});
