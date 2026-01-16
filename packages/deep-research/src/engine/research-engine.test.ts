// Research Engine Tests
// TSK-DR-001

import { describe, it, expect, beforeEach } from 'vitest';
import { ResearchEngine } from './research-engine.js';
import type { ResearchConfig, ReflectiveQuestion, SearchResult, WebContent, KnowledgeItem } from '../types/index.js';

describe('ResearchEngine', () => {
  let config: ResearchConfig;

  beforeEach(() => {
    config = {
      query: 'How to implement authentication in TypeScript?',
      maxIterations: 3,
      tokenBudget: 5000,
    };
  });

  it('should initialize with valid config', () => {
    const engine = new ResearchEngine(config);
    expect(engine.getKnowledge().size()).toBe(0);
    expect(engine.getTokenTracker().getBudget()).toBe(5000);
  });

  it('should throw error for invalid config', () => {
    expect(() => new ResearchEngine({ query: '' })).toThrow('Query is required');
    expect(() => new ResearchEngine({ query: 'test', maxIterations: 0 })).toThrow('maxIterations must be positive');
    expect(() => new ResearchEngine({ query: 'test', tokenBudget: -100 })).toThrow('tokenBudget must be positive');
  });

  it('should stop at max iterations', async () => {
    const engine = new ResearchEngine({ ...config, maxIterations: 2 });
    const report = await engine.research();
    
    expect(report.metadata.iterations).toBeLessThanOrEqual(2);
    expect(report.query).toBe(config.query);
  });

  it('should stop when definitive answer found', async () => {
    // Extend ResearchEngine to inject knowledge
    class TestEngine extends ResearchEngine {
      protected async reason(contents: WebContent[]): Promise<KnowledgeItem[]> {
        // Inject 15 knowledge items to trigger definitive answer
        return Array.from({ length: 15 }, (_, i) => ({
          type: 'fact' as const,
          content: `Test fact ${i + 1}`,
          sources: ['https://example.com'],
          relevance: 0.8,
          iteration: this.iteration,
          timestamp: Date.now(),
        }));
      }
    }
    
    const engine = new TestEngine({ ...config, maxIterations: 10 });
    const report = await engine.research();
    
    // Should stop early due to definitive answer (10+ knowledge items)
    expect(report.metadata.iterations).toBeLessThan(10);
    expect(engine.getKnowledge().size()).toBeGreaterThanOrEqual(10);
  });

  it('should accumulate knowledge across iterations', async () => {
    class TestEngine extends ResearchEngine {
      protected async reason(contents: WebContent[]): Promise<KnowledgeItem[]> {
        return [
          {
            type: 'fact',
            content: `Fact from iteration ${this.iteration}`,
            sources: ['https://example.com'],
            relevance: 0.7,
            iteration: this.iteration,
            timestamp: Date.now(),
          },
        ];
      }
    }
    
    const engine = new TestEngine({ ...config, maxIterations: 3 });
    await engine.research();
    
    expect(engine.getKnowledge().size()).toBeGreaterThan(0);
  });

  it('should generate report with metadata', async () => {
    const engine = new ResearchEngine({ ...config, maxIterations: 1 });
    const report = await engine.research();
    
    expect(report.query).toBe(config.query);
    expect(report.summary).toBeTruthy();
    expect(report.metadata.iterations).toBe(1);
    expect(report.metadata.tokensUsed).toBeGreaterThanOrEqual(0);
    expect(report.metadata.duration).toBeGreaterThanOrEqual(0); // Can be 0 for fast tests
  });

  it('should handle errors gracefully', async () => {
    class ErrorEngine extends ResearchEngine {
      protected async search(questions: ReflectiveQuestion[]): Promise<SearchResult[]> {
        if (this.iteration === 0) {
          throw new Error('Simulated search error');
        }
        return [];
      }
    }
    
    const engine = new ErrorEngine({ ...config, maxIterations: 2 });
    const report = await engine.research();
    
    // Should continue after error and complete
    expect(report.metadata.iterations).toBe(2);
  });

  it('should track trajectory logs', async () => {
    const engine = new ResearchEngine({ ...config, maxIterations: 2 });
    await engine.research();
    
    const logs = engine.getLogger().getLogs();
    expect(logs.length).toBeGreaterThan(0);
    
    const summary = engine.getLogger().getSummary();
    expect(summary.totalIterations).toBeGreaterThan(0);
  });
});
