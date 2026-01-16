// Report Generator Tests
// TSK-DR-005

import { describe, it, expect, beforeEach } from 'vitest';
import { ReportGenerator } from './report-generator.js';
import { KnowledgeBase } from '../knowledge/knowledge-base.js';
import type { IterationLog } from '../types/index.js';

describe('ReportGenerator', () => {
  let generator: ReportGenerator;
  let knowledge: KnowledgeBase;

  beforeEach(() => {
    generator = new ReportGenerator();
    knowledge = new KnowledgeBase();
  });

  it('should generate basic report', async () => {
    knowledge.addAll([
      { type: 'fact', content: 'TypeScript is typed', sources: ['https://ts.org'], relevance: 0.9, iteration: 0, timestamp: Date.now() },
      { type: 'fact', content: 'TypeScript compiles to JS', sources: ['https://ts.org'], relevance: 0.8, iteration: 0, timestamp: Date.now() },
    ]);

    const report = await generator.generate(
      'What is TypeScript?',
      knowledge,
      [],
      { totalTokens: 500, durationMs: 5000, iterations: 1 }
    );

    expect(report.query).toBe('What is TypeScript?');
    expect(report.summary).toBeTruthy();
    expect(report.findings).toHaveLength(2);
    expect(report.metadata.iterations).toBe(1);
    expect(report.metadata.tokensUsed).toBe(500);
    expect(report.metadata.duration).toBe(5000);
  });

  it('should generate report with no findings', async () => {
    const report = await generator.generate(
      'Empty query',
      knowledge,
      [],
      { totalTokens: 0, durationMs: 1000, iterations: 1 }
    );

    expect(report.findings).toHaveLength(0);
    expect(report.summary).toContain('no conclusive facts');
    expect(report.metadata.confidence).toBe(0);
  });

  it('should convert report to Markdown', async () => {
    knowledge.addAll([
      { type: 'fact', content: 'Test fact', sources: ['https://example.com'], relevance: 0.8, iteration: 0, timestamp: Date.now() },
    ]);

    const report = await generator.generate(
      'Test query',
      knowledge,
      [],
      { totalTokens: 100, durationMs: 1000, iterations: 1 }
    );

    const markdown = generator.toMarkdown(report);
    
    expect(markdown).toContain('# Research Report: Test query');
    expect(markdown).toContain('## Executive Summary');
    expect(markdown).toContain('## Key Findings');
    expect(markdown).toContain('Test fact');
  });

  it('should convert report to JSON', async () => {
    const report = await generator.generate(
      'Test query',
      knowledge,
      [],
      { totalTokens: 100, durationMs: 1000, iterations: 1 }
    );

    const json = generator.toJSON(report);
    const parsed = JSON.parse(json);
    
    expect(parsed.query).toBe('Test query');
    expect(parsed.metadata).toBeTruthy();
  });

  it('should collect references from knowledge', async () => {
    knowledge.addAll([
      { type: 'fact', content: 'Fact 1', sources: ['https://example.com/page1'], relevance: 0.8, iteration: 0, timestamp: Date.now() },
      { type: 'fact', content: 'Fact 2', sources: ['https://example.com/page2', 'https://other.com'], relevance: 0.7, iteration: 0, timestamp: Date.now() },
    ]);

    const report = await generator.generate(
      'Test query',
      knowledge,
      [],
      { totalTokens: 100, durationMs: 1000, iterations: 1 }
    );

    expect(report.references).toHaveLength(3);
    expect(report.references[0].url).toBe('https://example.com/page1');
  });

  it('should calculate overall confidence', async () => {
    knowledge.addAll([
      { type: 'fact', content: 'High confidence', sources: [], relevance: 0.9, iteration: 0, timestamp: Date.now() },
      { type: 'fact', content: 'Low confidence', sources: [], relevance: 0.5, iteration: 0, timestamp: Date.now() },
    ]);

    const report = await generator.generate(
      'Test query',
      knowledge,
      [],
      { totalTokens: 100, durationMs: 1000, iterations: 1 }
    );

    expect(report.metadata.confidence).toBeGreaterThan(0);
    expect(report.metadata.confidence).toBeLessThan(1);
  });
});
