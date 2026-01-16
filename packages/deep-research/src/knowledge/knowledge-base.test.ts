// Knowledge Base Tests
// TSK-DR-002

import { describe, it, expect, beforeEach } from 'vitest';
import { KnowledgeBase } from './knowledge-base.js';
import type { KnowledgeItem } from '../types/index.js';

describe('KnowledgeBase', () => {
  let kb: KnowledgeBase;

  beforeEach(() => {
    kb = new KnowledgeBase();
  });

  it('should add single knowledge item', () => {
    const item: KnowledgeItem = {
      type: 'fact',
      content: 'TypeScript is a typed superset of JavaScript',
      sources: ['https://typescriptlang.org'],
      relevance: 0.9,
      iteration: 0,
      timestamp: Date.now(),
    };

    kb.add(item);
    expect(kb.size()).toBe(1);
    expect(item.id).toBeTruthy();
  });

  it('should add multiple knowledge items', () => {
    const items: KnowledgeItem[] = [
      { type: 'fact', content: 'Fact 1', sources: [], relevance: 0.8, iteration: 0, timestamp: Date.now() },
      { type: 'opinion', content: 'Opinion 1', sources: [], relevance: 0.6, iteration: 0, timestamp: Date.now() },
      { type: 'question', content: 'Question 1', sources: [], relevance: 0.5, iteration: 0, timestamp: Date.now() },
    ];

    kb.addAll(items);
    expect(kb.size()).toBe(3);
  });

  it('should get findings sorted by relevance', () => {
    kb.addAll([
      { type: 'fact', content: 'Low relevance', sources: [], relevance: 0.3, iteration: 0, timestamp: Date.now() },
      { type: 'fact', content: 'High relevance', sources: [], relevance: 0.9, iteration: 0, timestamp: Date.now() },
      { type: 'fact', content: 'Medium relevance', sources: [], relevance: 0.6, iteration: 0, timestamp: Date.now() },
      { type: 'opinion', content: 'Not a fact', sources: [], relevance: 1.0, iteration: 0, timestamp: Date.now() },
    ]);

    const findings = kb.getFindings();
    expect(findings).toHaveLength(3); // Only facts
    expect(findings[0].content).toBe('High relevance');
    expect(findings[1].content).toBe('Medium relevance');
    expect(findings[2].content).toBe('Low relevance');
  });

  it('should get items by iteration', () => {
    kb.addAll([
      { type: 'fact', content: 'Iteration 0', sources: [], relevance: 0.8, iteration: 0, timestamp: Date.now() },
      { type: 'fact', content: 'Iteration 1', sources: [], relevance: 0.8, iteration: 1, timestamp: Date.now() },
      { type: 'fact', content: 'Iteration 0 again', sources: [], relevance: 0.8, iteration: 0, timestamp: Date.now() },
    ]);

    const iter0Items = kb.getByIteration(0);
    const iter1Items = kb.getByIteration(1);

    expect(iter0Items).toHaveLength(2);
    expect(iter1Items).toHaveLength(1);
  });

  it('should generate summary', () => {
    kb.addAll([
      { type: 'fact', content: 'Fact 1', sources: [], relevance: 0.9, iteration: 0, timestamp: Date.now() },
      { type: 'fact', content: 'Fact 2', sources: [], relevance: 0.8, iteration: 0, timestamp: Date.now() },
    ]);

    const summary = kb.getSummary();
    expect(summary).toContain('Fact 1');
    expect(summary).toContain('Fact 2');
  });

  it('should return empty summary for empty kb', () => {
    const summary = kb.getSummary();
    expect(summary).toContain('No knowledge');
  });

  it('should clear all knowledge', () => {
    kb.addAll([
      { type: 'fact', content: 'Test', sources: [], relevance: 0.8, iteration: 0, timestamp: Date.now() },
    ]);

    expect(kb.size()).toBe(1);
    kb.clear();
    expect(kb.size()).toBe(0);
  });
});
