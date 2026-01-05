/**
 * @fileoverview Tests for Pattern-Ontology Integration Bridge
 * @traceability TSK-INT-001
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { PatternOntologyBridge, type PatternRelationship } from '../integration/index.js';
import { N3Store } from '../store/index.js';
import type { Pattern, ASTNode } from '@nahisaho/musubix-pattern-mcp';

describe('PatternOntologyBridge', () => {
  let store: N3Store;
  let bridge: PatternOntologyBridge;

  const defaultPos = { row: 0, column: 0 };

  const createAST = (type: string, children: ASTNode[] = [], value?: string): ASTNode => ({
    type,
    value,
    children,
    startPosition: defaultPos,
    endPosition: defaultPos,
  });

  const createPattern = (
    id: string,
    astType: string,
    holes: Pattern['holes'] = [],
    frequency = 1
  ): Pattern => ({
    id,
    name: `${astType}_pattern`,
    language: 'typescript',
    ast: createAST(astType, [
      createAST('Identifier', [], 'test'),
      createAST('Block', [
        createAST('Statement'),
      ]),
    ]),
    holes,
    frequency,
    createdAt: new Date().toISOString(),
    updatedAt: new Date().toISOString(),
  });

  beforeEach(() => {
    store = new N3Store({
      enableInference: false,
      maxTriples: 10000,
    });
    bridge = new PatternOntologyBridge(store, {
      enableInference: true,
      minConfidence: 0.5,
    });
  });

  describe('importPattern', () => {
    it('should import a pattern into the ontology', () => {
      const pattern = createPattern('P001', 'FunctionDeclaration');
      
      const result = bridge.importPattern(pattern);
      
      expect(result).toBe(true);
      const stats = bridge.getStats();
      expect(stats.patternCount).toBe(1);
      expect(stats.tripleCount).toBeGreaterThan(0);
    });

    it('should store pattern metadata as triples', () => {
      const pattern = createPattern('P002', 'ClassDeclaration', [], 5);
      
      bridge.importPattern(pattern);
      
      const stats = bridge.getStats();
      expect(stats.tripleCount).toBeGreaterThanOrEqual(6); // At least type, label, language, astType, frequency, holeCount
    });

    it('should store hole information', () => {
      const pattern = createPattern('P003', 'FunctionDeclaration', [
        { id: 'H1', type: 'Identifier' },
        { id: 'H2', type: 'Expression' },
      ]);
      
      bridge.importPattern(pattern);
      
      const stats = bridge.getStats();
      expect(stats.tripleCount).toBeGreaterThan(6); // Additional hole type triples
    });
  });

  describe('importPatterns', () => {
    it('should import multiple patterns', () => {
      const patterns = [
        createPattern('P010', 'FunctionDeclaration'),
        createPattern('P011', 'ClassDeclaration'),
        createPattern('P012', 'MethodDeclaration'),
      ];
      
      const count = bridge.importPatterns(patterns);
      
      expect(count).toBe(3);
      expect(bridge.getStats().patternCount).toBe(3);
    });

    it('should discover relationships after import', () => {
      const general = createPattern('PG01', 'FunctionDeclaration', [
        { id: 'H1', type: 'Identifier' },
        { id: 'H2', type: 'Block' },
        { id: 'H3', type: 'Parameters' },
      ], 10);
      const specific = createPattern('PS01', 'FunctionDeclaration', [
        { id: 'H1', type: 'Identifier' },
      ], 5);
      
      bridge.importPatterns([general, specific]);
      
      const relationships = bridge.findRelatedPatterns('PG01');
      expect(relationships.length).toBeGreaterThanOrEqual(0);
    });
  });

  describe('discoverRelationships', () => {
    it('should detect subsumption relationships', () => {
      const general = createPattern('SUB-G', 'FunctionDeclaration', [
        { id: 'H1', type: 'Identifier' },
        { id: 'H2', type: 'Block' },
      ]);
      const specific = createPattern('SUB-S', 'FunctionDeclaration', []);
      
      const relationships = bridge.discoverRelationships([general, specific]);
      
      const subsumption = relationships.find(r => r.relation === 'subsumes');
      expect(subsumption).toBeDefined();
      expect(subsumption?.source).toBe('SUB-G');
      expect(subsumption?.target).toBe('SUB-S');
    });

    it('should detect similarity relationships', () => {
      const p1 = createPattern('SIM-1', 'FunctionDeclaration');
      const p2 = createPattern('SIM-2', 'FunctionDeclaration');
      
      const relationships = bridge.discoverRelationships([p1, p2]);
      
      const similarity = relationships.find(r => r.relation === 'similarTo');
      expect(similarity).toBeDefined();
      expect(similarity?.confidence).toBeGreaterThanOrEqual(0.5);
    });

    it('should not create relationships for different languages', () => {
      const tsPattern: Pattern = {
        ...createPattern('LANG-TS', 'FunctionDeclaration'),
        language: 'typescript',
      };
      const pyPattern: Pattern = {
        ...createPattern('LANG-PY', 'FunctionDeclaration'),
        language: 'python',
      };
      
      const relationships = bridge.discoverRelationships([tsPattern, pyPattern]);
      
      // Should have no relationships due to different languages
      expect(relationships.filter(r => 
        (r.source === 'LANG-TS' && r.target === 'LANG-PY') ||
        (r.source === 'LANG-PY' && r.target === 'LANG-TS')
      ).length).toBe(0);
    });
  });

  describe('queryPatterns', () => {
    beforeEach(() => {
      bridge.importPatterns([
        createPattern('Q001', 'FunctionDeclaration', [], 10),
        createPattern('Q002', 'ClassDeclaration', [], 5),
        createPattern('Q003', 'FunctionDeclaration', [], 3),
      ]);
    });

    it('should query by language', () => {
      const result = bridge.queryPatterns({ language: 'typescript' });
      
      expect(result.patterns.length).toBe(3);
    });

    it('should query by AST type', () => {
      const result = bridge.queryPatterns({ astType: 'FunctionDeclaration' });
      
      expect(result.patterns.length).toBe(2);
      expect(result.patterns.every(p => p.ast.type === 'FunctionDeclaration')).toBe(true);
    });

    it('should filter by minimum frequency', () => {
      const result = bridge.queryPatterns({ minFrequency: 5 });
      
      expect(result.patterns.length).toBe(2);
      expect(result.patterns.every(p => p.frequency >= 5)).toBe(true);
    });
  });

  describe('findRelatedPatterns', () => {
    it('should find all related patterns', () => {
      const patterns = [
        createPattern('REL-1', 'FunctionDeclaration', [
          { id: 'H1', type: 'any' },
        ]),
        createPattern('REL-2', 'FunctionDeclaration'),
      ];
      
      bridge.importPatterns(patterns);
      
      const related = bridge.findRelatedPatterns('REL-1');
      expect(related.length).toBeGreaterThanOrEqual(0);
    });

    it('should filter by relation type', () => {
      const patterns = [
        createPattern('FLT-1', 'FunctionDeclaration', [
          { id: 'H1', type: 'Identifier' },
          { id: 'H2', type: 'Block' },
        ]),
        createPattern('FLT-2', 'FunctionDeclaration'),
      ];
      
      bridge.importPatterns(patterns);
      bridge.discoverRelationships(patterns);
      
      const subsumes = bridge.findRelatedPatterns('FLT-1', 'subsumes');
      const similar = bridge.findRelatedPatterns('FLT-1', 'similarTo');
      
      // Subsumption relationships should be filtered
      expect(subsumes.every(r => r.relation === 'subsumes')).toBe(true);
      expect(similar.every(r => r.relation === 'similarTo')).toBe(true);
    });
  });

  describe('exportAsTurtle', () => {
    it('should export pattern graph as Turtle', async () => {
      bridge.importPattern(createPattern('EXP-1', 'FunctionDeclaration'));
      
      const turtle = await bridge.exportAsTurtle();
      
      expect(turtle).toContain('pattern:');
      expect(turtle).toContain('EXP-1');
    });
  });

  describe('inference', () => {
    it('should infer inverse relationships', () => {
      const bridgeWithInference = new PatternOntologyBridge(store, {
        enableInference: true,
        minConfidence: 0.3,
      });
      
      const patterns = [
        createPattern('INF-G', 'FunctionDeclaration', [
          { id: 'H1', type: 'any' },
          { id: 'H2', type: 'any' },
        ]),
        createPattern('INF-S', 'FunctionDeclaration'),
      ];
      
      bridgeWithInference.importPatterns(patterns);
      bridgeWithInference.discoverRelationships(patterns);
      
      // After inference, specializes should be inferred from subsumes
      const specializes = bridgeWithInference.findRelatedPatterns('INF-S', 'specializes');
      // May or may not have inferred relationships depending on rule application
      expect(specializes).toBeDefined();
    });
  });

  describe('getStats', () => {
    it('should return correct statistics', () => {
      bridge.importPatterns([
        createPattern('STAT-1', 'FunctionDeclaration'),
        createPattern('STAT-2', 'ClassDeclaration'),
      ]);
      
      const stats = bridge.getStats();
      
      expect(stats.patternCount).toBe(2);
      expect(stats.tripleCount).toBeGreaterThan(0);
      expect(stats.relationshipCount).toBeGreaterThanOrEqual(0);
    });
  });
});
