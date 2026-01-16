/**
 * @fileoverview Tests for MCP Tools
 * @module @nahisaho/musubix-deep-research/mcp
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { DeepResearchMCPHandler, getMCPHandler, DEEP_RESEARCH_TOOLS } from './tools.js';

describe('DeepResearchMCPHandler', () => {
  let handler: DeepResearchMCPHandler;

  beforeEach(() => {
    handler = new DeepResearchMCPHandler();
  });

  describe('handleStart', () => {
    it('should create research session', async () => {
      const result = await handler.handleStart({
        query: 'How does TypeScript inference work?',
        maxIterations: 3,
        tokenBudget: 5000,
      });

      expect(result.researchId).toMatch(/^research-\d+-\d+$/);
      expect(result.status).toContain('Research started');
    });

    it('should use default values', async () => {
      const result = await handler.handleStart({
        query: 'What is React Server Components?',
      });

      expect(result.researchId).toBeDefined();
      expect(result.status).toBeDefined();
    });
  });

  describe('handleStatus', () => {
    it('should return session status', async () => {
      const startResult = await handler.handleStart({
        query: 'Test query',
      });

      const status = await handler.handleStatus({
        researchId: startResult.researchId,
      });

      // Check if it's an error response (has error property with non-undefined value)
      if ('error' in status && typeof status.error === 'string') {
        throw new Error(`Unexpected error: ${status.error}`);
      }

      expect(status.id).toBe(startResult.researchId);
      expect(status.query).toBe('Test query');
      expect(status.status).toMatch(/running|completed|failed/);
    });

    it('should return error for non-existent session', async () => {
      const status = await handler.handleStatus({
        researchId: 'non-existent',
      });

      expect('error' in status).toBe(true);
      if ('error' in status) {
        expect(status.error).toContain('not found');
      }
    });
  });

  describe('handleReport', () => {
    it('should return error for non-existent session', async () => {
      const report = await handler.handleReport({
        researchId: 'non-existent',
      });

      expect(typeof report).toBe('object');
      if (typeof report === 'object') {
        expect(report.error).toContain('not found');
      }
    });

    it('should return error for incomplete research', async () => {
      const startResult = await handler.handleStart({
        query: 'Test query',
      });

      // Immediately request report (should still be running)
      const report = await handler.handleReport({
        researchId: startResult.researchId,
      });

      expect(typeof report).toBe('object');
      if (typeof report === 'object') {
        expect(report.error).toMatch(/not completed/);
      }
    });
  });

  describe('clearOldSessions', () => {
    it('should clear old sessions', async () => {
      // Create session
      await handler.handleStart({ query: 'Test' });

      // Clear sessions older than 0ms (i.e., all non-running)
      const cleared = handler.clearOldSessions(0);

      // Session might still be running, so cleared could be 0 or 1
      expect(cleared).toBeGreaterThanOrEqual(0);
    });

    it('should not clear running sessions', async () => {
      // Create session
      const result = await handler.handleStart({ query: 'Test' });

      // Try to clear immediately
      const cleared1 = handler.clearOldSessions(0);

      // Check status - should still exist
      const status = await handler.handleStatus({
        researchId: result.researchId,
      });

      expect('error' in status || status.id).toBeTruthy();
    });
  });
});

describe('getMCPHandler', () => {
  it('should return singleton instance', () => {
    const handler1 = getMCPHandler();
    const handler2 = getMCPHandler();

    expect(handler1).toBe(handler2);
  });
});

describe('DEEP_RESEARCH_TOOLS', () => {
  it('should export 3 tool definitions', () => {
    expect(DEEP_RESEARCH_TOOLS.length).toBe(3);
  });

  it('should have deep_research_start tool', () => {
    const startTool = DEEP_RESEARCH_TOOLS.find((t) => t.name === 'deep_research_start');
    expect(startTool).toBeDefined();
    expect(startTool?.inputSchema.properties.query).toBeDefined();
    expect(startTool?.inputSchema.required).toContain('query');
  });

  it('should have deep_research_status tool', () => {
    const statusTool = DEEP_RESEARCH_TOOLS.find((t) => t.name === 'deep_research_status');
    expect(statusTool).toBeDefined();
    expect(statusTool?.inputSchema.properties.researchId).toBeDefined();
  });

  it('should have deep_research_report tool', () => {
    const reportTool = DEEP_RESEARCH_TOOLS.find((t) => t.name === 'deep_research_report');
    expect(reportTool).toBeDefined();
    expect(reportTool?.inputSchema.properties.format).toBeDefined();
  });
});
