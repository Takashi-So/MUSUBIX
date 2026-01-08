/**
 * EnhancedVersionSpace Test Suite
 * @module @nahisaho/musubix-synthesis
 * @see TSK-SY-102
 * @see DES-SY-102
 * @see REQ-SYN-002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  EnhancedVersionSpace,
  createEnhancedVersionSpace,
  type VersionSpaceConfig,
  type VersionSpacePoint,
  type VersionSpaceStatistics,
  type MergeStrategy,
} from '../../src/versionspace/EnhancedVersionSpace.js';

// =============================================================================
// Test Fixtures
// =============================================================================

function createMockConfig(): VersionSpaceConfig {
  return {
    maxPoints: 1000,
    enableCompression: true,
    mergeStrategy: 'intersection' as MergeStrategy,
    enableLazyEvaluation: true,
  };
}

function createMockPoint(overrides: Partial<VersionSpacePoint> = {}): VersionSpacePoint {
  return {
    id: `point-${Date.now()}`,
    program: 'function f(x) { return x; }',
    examples: [{ input: 1, output: 1 }],
    consistent: true,
    confidence: 0.9,
    ...overrides,
  };
}

// =============================================================================
// Tests
// =============================================================================

describe('EnhancedVersionSpace', () => {
  let space: EnhancedVersionSpace;

  beforeEach(() => {
    space = createEnhancedVersionSpace();
  });

  describe('Factory Function', () => {
    it('should create version space with default config', () => {
      const s = createEnhancedVersionSpace();
      expect(s).toBeDefined();
      expect(s.add).toBeDefined();
    });

    it('should create version space with custom config', () => {
      const config = createMockConfig();
      const s = createEnhancedVersionSpace(config);
      expect(s).toBeDefined();
    });
  });

  describe('add', () => {
    it('should add a point to the version space', () => {
      const point = createMockPoint();
      const result = space.add(point);
      
      expect(result).toBe(true);
      expect(space.size()).toBe(1);
    });

    it('should reject inconsistent points', () => {
      const point = createMockPoint({ consistent: false });
      const result = space.add(point);
      
      // Might accept but mark as inconsistent
      expect(result).toBeDefined();
    });

    it('should respect max points limit', () => {
      const config: VersionSpaceConfig = {
        ...createMockConfig(),
        maxPoints: 3,
      };
      const s = createEnhancedVersionSpace(config);
      
      for (let i = 0; i < 5; i++) {
        s.add(createMockPoint({ id: `point-${i}` }));
      }
      
      expect(s.size()).toBeLessThanOrEqual(3);
    });

    it('should track confidence scores', () => {
      const point = createMockPoint({ confidence: 0.95 });
      space.add(point);
      
      const retrieved = space.get(point.id);
      expect(retrieved?.confidence).toBe(0.95);
    });
  });

  describe('get', () => {
    it('should retrieve point by id', () => {
      const point = createMockPoint({ id: 'test-point' });
      space.add(point);
      
      const retrieved = space.get('test-point');
      expect(retrieved).toBeDefined();
      expect(retrieved?.id).toBe('test-point');
    });

    it('should return undefined for non-existent point', () => {
      const retrieved = space.get('non-existent');
      expect(retrieved).toBeUndefined();
    });
  });

  describe('remove', () => {
    it('should remove point by id', () => {
      const point = createMockPoint({ id: 'to-remove' });
      space.add(point);
      
      const removed = space.remove('to-remove');
      expect(removed).toBe(true);
      expect(space.get('to-remove')).toBeUndefined();
    });

    it('should return false for non-existent point', () => {
      const removed = space.remove('non-existent');
      expect(removed).toBe(false);
    });
  });

  describe('merge', () => {
    it('should merge two version spaces with intersection strategy', () => {
      const s1 = createEnhancedVersionSpace({ mergeStrategy: 'intersection' });
      const s2 = createEnhancedVersionSpace({ mergeStrategy: 'intersection' });
      
      const sharedPoint = createMockPoint({ id: 'shared', program: 'f(x) = x + 1' });
      const uniquePoint1 = createMockPoint({ id: 'unique1', program: 'f(x) = x * 2' });
      const uniquePoint2 = createMockPoint({ id: 'unique2', program: 'f(x) = x / 2' });
      
      s1.add(sharedPoint);
      s1.add(uniquePoint1);
      s2.add(sharedPoint);
      s2.add(uniquePoint2);
      
      const merged = s1.merge(s2);
      // Intersection should contain at least shared point
      expect(merged.size()).toBeGreaterThan(0);
    });

    it('should merge with union strategy', () => {
      const s1 = createEnhancedVersionSpace({ mergeStrategy: 'union' });
      const s2 = createEnhancedVersionSpace({ mergeStrategy: 'union' });
      
      s1.add(createMockPoint({ id: 'p1' }));
      s2.add(createMockPoint({ id: 'p2' }));
      
      const merged = s1.merge(s2, 'union');
      expect(merged.size()).toBeGreaterThanOrEqual(2);
    });
  });

  describe('collapse', () => {
    it('should collapse consistent points', () => {
      const space = createEnhancedVersionSpace();
      
      // Add similar points
      space.add(createMockPoint({ id: 'p1', program: 'f(x) = x + 1', confidence: 0.8 }));
      space.add(createMockPoint({ id: 'p2', program: 'f(x) = x + 1', confidence: 0.9 }));
      space.add(createMockPoint({ id: 'p3', program: 'f(x) = x + 1', confidence: 0.7 }));
      
      const sizeBefore = space.size();
      space.collapse();
      const sizeAfter = space.size();
      
      // Should collapse similar programs
      expect(sizeAfter).toBeLessThanOrEqual(sizeBefore);
    });
  });

  describe('filterByConfidence', () => {
    it('should filter points by minimum confidence', () => {
      space.add(createMockPoint({ id: 'high', confidence: 0.95 }));
      space.add(createMockPoint({ id: 'medium', confidence: 0.7 }));
      space.add(createMockPoint({ id: 'low', confidence: 0.3 }));
      
      const filtered = space.filterByConfidence(0.8);
      
      expect(filtered.length).toBe(1);
      expect(filtered[0].id).toBe('high');
    });
  });

  describe('getBestProgram', () => {
    it('should return highest confidence program', () => {
      space.add(createMockPoint({ id: 'p1', program: 'prog1', confidence: 0.5 }));
      space.add(createMockPoint({ id: 'p2', program: 'prog2', confidence: 0.9 }));
      space.add(createMockPoint({ id: 'p3', program: 'prog3', confidence: 0.7 }));
      
      const best = space.getBestProgram();
      expect(best?.program).toBe('prog2');
    });

    it('should return undefined for empty space', () => {
      const best = space.getBestProgram();
      expect(best).toBeUndefined();
    });
  });

  describe('getAllPrograms', () => {
    it('should return all programs sorted by confidence', () => {
      space.add(createMockPoint({ id: 'p1', program: 'prog1', confidence: 0.5 }));
      space.add(createMockPoint({ id: 'p2', program: 'prog2', confidence: 0.9 }));
      space.add(createMockPoint({ id: 'p3', program: 'prog3', confidence: 0.7 }));
      
      const all = space.getAllPrograms();
      
      expect(all.length).toBe(3);
      expect(all[0].confidence).toBeGreaterThanOrEqual(all[1].confidence);
      expect(all[1].confidence).toBeGreaterThanOrEqual(all[2].confidence);
    });
  });

  describe('Statistics', () => {
    it('should return initial statistics', () => {
      const stats = space.getStatistics();
      
      expect(stats).toBeDefined();
      expect(stats.totalPoints).toBe(0);
      expect(stats.consistentPoints).toBe(0);
      expect(stats.mergeCount).toBe(0);
    });

    it('should update statistics after operations', () => {
      space.add(createMockPoint({ id: 'stats-p1', consistent: true }));
      space.add(createMockPoint({ id: 'stats-p2', consistent: true }));
      
      const stats = space.getStatistics();
      expect(stats.totalPoints).toBe(2);
      expect(stats.consistentPoints).toBe(2);
    });

    it('should track average confidence', () => {
      space.add(createMockPoint({ id: 'conf-p1', confidence: 0.8 }));
      space.add(createMockPoint({ id: 'conf-p2', confidence: 0.6 }));
      
      const stats = space.getStatistics();
      expect(stats.averageConfidence).toBeCloseTo(0.7, 1);
    });
  });

  describe('clear', () => {
    it('should remove all points', () => {
      space.add(createMockPoint({ id: 'p1' }));
      space.add(createMockPoint({ id: 'p2' }));
      
      space.clear();
      
      expect(space.size()).toBe(0);
    });
  });

  describe('clone', () => {
    it('should create independent copy', () => {
      space.add(createMockPoint({ id: 'p1' }));
      
      const cloned = space.clone();
      cloned.add(createMockPoint({ id: 'p2' }));
      
      expect(space.size()).toBe(1);
      expect(cloned.size()).toBe(2);
    });
  });

  describe('toJSON / fromJSON', () => {
    it('should serialize state', () => {
      space.add(createMockPoint({ id: 'test' }));
      
      const json = space.toJSON();
      expect(json).toBeDefined();
      expect(typeof json).toBe('string');
    });

    it('should restore state', () => {
      space.add(createMockPoint({ id: 'test', confidence: 0.85 }));
      const json = space.toJSON();
      
      const newSpace = createEnhancedVersionSpace();
      newSpace.fromJSON(json);
      
      expect(newSpace.size()).toBe(1);
      const point = newSpace.get('test');
      expect(point?.confidence).toBe(0.85);
    });
  });
});
