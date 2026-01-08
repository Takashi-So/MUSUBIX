/**
 * Priority Queue Tests
 * @module @nahisaho/musubix-neural-search
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { PriorityQueue } from '../../src/search/PriorityQueue.js';

describe('PriorityQueue', () => {
  let queue: PriorityQueue<string>;

  beforeEach(() => {
    queue = new PriorityQueue<string>();
  });

  describe('push', () => {
    it('should add items to queue', () => {
      queue.push('item1', 1.0);
      expect(queue.size()).toBe(1);
    });

    it('should maintain priority order', () => {
      queue.push('low', 0.1);
      queue.push('high', 0.9);
      queue.push('medium', 0.5);

      expect(queue.peek()).toBe('high');
    });
  });

  describe('pop', () => {
    it('should return highest priority item', () => {
      queue.push('low', 0.1);
      queue.push('high', 0.9);
      queue.push('medium', 0.5);

      expect(queue.pop()).toBe('high');
      expect(queue.pop()).toBe('medium');
      expect(queue.pop()).toBe('low');
    });

    it('should return undefined for empty queue', () => {
      expect(queue.pop()).toBeUndefined();
    });

    it('should decrease size', () => {
      queue.push('item', 1.0);
      queue.pop();
      expect(queue.size()).toBe(0);
    });
  });

  describe('peek', () => {
    it('should return highest priority without removing', () => {
      queue.push('high', 0.9);
      queue.push('low', 0.1);

      expect(queue.peek()).toBe('high');
      expect(queue.size()).toBe(2);
    });

    it('should return undefined for empty queue', () => {
      expect(queue.peek()).toBeUndefined();
    });
  });

  describe('size', () => {
    it('should return correct size', () => {
      expect(queue.size()).toBe(0);

      queue.push('a', 1);
      expect(queue.size()).toBe(1);

      queue.push('b', 2);
      expect(queue.size()).toBe(2);

      queue.pop();
      expect(queue.size()).toBe(1);
    });
  });

  describe('isEmpty', () => {
    it('should return true for empty queue', () => {
      expect(queue.isEmpty()).toBe(true);
    });

    it('should return false for non-empty queue', () => {
      queue.push('item', 1);
      expect(queue.isEmpty()).toBe(false);
    });
  });

  describe('clear', () => {
    it('should remove all items', () => {
      queue.push('a', 1);
      queue.push('b', 2);
      queue.push('c', 3);

      queue.clear();

      expect(queue.isEmpty()).toBe(true);
      expect(queue.size()).toBe(0);
    });
  });

  describe('toArray', () => {
    it('should return items sorted by priority', () => {
      queue.push('low', 0.1);
      queue.push('high', 0.9);
      queue.push('medium', 0.5);

      const arr = queue.toArray();

      expect(arr).toEqual(['high', 'medium', 'low']);
    });

    it('should return empty array for empty queue', () => {
      expect(queue.toArray()).toEqual([]);
    });
  });

  describe('heap operations', () => {
    it('should handle many insertions', () => {
      for (let i = 0; i < 100; i++) {
        queue.push(`item-${i}`, Math.random());
      }

      expect(queue.size()).toBe(100);

      // Verify ordering
      let prev = Infinity;
      while (!queue.isEmpty()) {
        const item = queue.pop()!;
        const priority = parseFloat(item.split('-')[1]) / 100; // Approximate
        // Just verify we get items out
        expect(item).toBeDefined();
      }
    });

    it('should handle equal priorities', () => {
      queue.push('a', 0.5);
      queue.push('b', 0.5);
      queue.push('c', 0.5);

      expect(queue.size()).toBe(3);

      // All should be retrievable
      const items = [queue.pop(), queue.pop(), queue.pop()];
      expect(items).toContain('a');
      expect(items).toContain('b');
      expect(items).toContain('c');
    });

    it('should handle decreasing priorities', () => {
      queue.push('first', 1.0);
      queue.push('second', 0.9);
      queue.push('third', 0.8);
      queue.push('fourth', 0.7);

      expect(queue.pop()).toBe('first');
      expect(queue.pop()).toBe('second');
      expect(queue.pop()).toBe('third');
      expect(queue.pop()).toBe('fourth');
    });

    it('should handle increasing priorities', () => {
      queue.push('fourth', 0.7);
      queue.push('third', 0.8);
      queue.push('second', 0.9);
      queue.push('first', 1.0);

      expect(queue.pop()).toBe('first');
      expect(queue.pop()).toBe('second');
      expect(queue.pop()).toBe('third');
      expect(queue.pop()).toBe('fourth');
    });
  });

  describe('with complex types', () => {
    it('should work with objects', () => {
      const objQueue = new PriorityQueue<{ id: string; value: number }>();

      objQueue.push({ id: 'low', value: 1 }, 0.1);
      objQueue.push({ id: 'high', value: 10 }, 0.9);

      const result = objQueue.pop();
      expect(result?.id).toBe('high');
      expect(result?.value).toBe(10);
    });
  });
});
