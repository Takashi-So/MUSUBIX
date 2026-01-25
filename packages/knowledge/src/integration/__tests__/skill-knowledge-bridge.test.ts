/**
 * @fileoverview Tests for Skill-Knowledge Bridge
 * @traceability TSK-INT-003
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import * as os from 'node:os';
import {
  createSkillKnowledgeBridge,
  formatSessionAsMarkdown,
  formatContextAsMarkdown,
} from '../skill-knowledge-bridge.js';
import type {
  SkillEntity,
  SessionProperties,
  EvalResultProperties,
  SkillQueryContext,
} from '../types.js';

describe('SkillKnowledgeBridge', () => {
  let bridge: ReturnType<typeof createSkillKnowledgeBridge>;
  let tempDir: string;

  beforeEach(async () => {
    tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'skill-knowledge-test-'));
    bridge = createSkillKnowledgeBridge({
      basePath: tempDir,
      autoSave: true,
    });
  });

  afterEach(async () => {
    try {
      await fs.rm(tempDir, { recursive: true, force: true });
    } catch {
      // Ignore cleanup errors
    }
  });

  describe('storeSkillEntity / getSkillEntity', () => {
    it('should store and retrieve skill entity', async () => {
      const entity: SkillEntity = {
        id: 'test-skill-001',
        type: 'skill',
        name: 'Test Skill',
        description: 'A test skill',
        properties: {
          kind: 'skill',
          version: '1.0.0',
          triggers: ['on_error'],
          commands: ['fix'],
        },
        tags: ['test', 'skill'],
      };

      await bridge.storeSkillEntity(entity);
      const retrieved = await bridge.getSkillEntity('test-skill-001');

      expect(retrieved).toBeDefined();
      expect(retrieved?.name).toBe('Test Skill');
      expect(retrieved?.type).toBe('skill');
    });

    it('should return undefined for non-existent entity', async () => {
      const result = await bridge.getSkillEntity('non-existent');
      expect(result).toBeUndefined();
    });
  });

  describe('deleteSkillEntity', () => {
    it('should delete existing entity', async () => {
      const entity: SkillEntity = {
        id: 'to-delete',
        type: 'skill',
        name: 'To Delete',
        properties: { kind: 'skill', version: '1.0.0', triggers: [], commands: [] },
        tags: [],
      };

      await bridge.storeSkillEntity(entity);
      const deleted = await bridge.deleteSkillEntity('to-delete');
      const retrieved = await bridge.getSkillEntity('to-delete');

      expect(deleted).toBe(true);
      expect(retrieved).toBeUndefined();
    });

    it('should return false for non-existent entity', async () => {
      const deleted = await bridge.deleteSkillEntity('non-existent');
      expect(deleted).toBe(false);
    });
  });

  describe('startSession / endSession', () => {
    it('should start and end session', async () => {
      const sessionId = await bridge.startSession('Test task');

      expect(sessionId).toMatch(/^session-/);

      const session = await bridge.getSkillEntity(sessionId);
      expect(session).toBeDefined();
      expect(session?.type).toBe('session');
      
      const props = session?.properties as SessionProperties;
      expect(props.status).toBe('active');
      expect(props.taskDescription).toBe('Test task');

      await bridge.endSession(sessionId, 'completed', ['skill1', 'skill2']);

      const endedSession = await bridge.getSkillEntity(sessionId);
      const endedProps = endedSession?.properties as SessionProperties;
      expect(endedProps.status).toBe('completed');
      expect(endedProps.skillsUsed).toContain('skill1');
      expect(endedProps.endedAt).toBeDefined();
    });

    it('should throw error for non-existent session', async () => {
      await expect(
        bridge.endSession('non-existent', 'completed', [])
      ).rejects.toThrow('Session not found');
    });
  });

  describe('recordCheckpoint', () => {
    it('should record checkpoint for session', async () => {
      const sessionId = await bridge.startSession('Checkpoint test');
      const checkpointId = await bridge.recordCheckpoint(
        sessionId,
        'implementation',
        '/tmp/snapshot-001'
      );

      expect(checkpointId).toMatch(/^checkpoint-/);

      const checkpoint = await bridge.getSkillEntity(checkpointId);
      expect(checkpoint?.type).toBe('checkpoint');
      expect(checkpoint?.tags).toContain('implementation');

      const session = await bridge.getSkillEntity(sessionId);
      const props = session?.properties as SessionProperties;
      expect(props.checkpointCount).toBe(1);
    });
  });

  describe('recordEvalResult', () => {
    it('should record evaluation result', async () => {
      const sessionId = await bridge.startSession('Eval test');
      const evalId = await bridge.recordEvalResult(
        sessionId,
        'capability',
        {
          passAt1: 0.85,
          passAt3: 0.95,
          testsPassed: 17,
          testsFailed: 3,
          notes: 'Good progress',
        }
      );

      expect(evalId).toMatch(/^eval-/);

      const evalResult = await bridge.getSkillEntity(evalId);
      expect(evalResult?.type).toBe('eval_result');
      
      const props = evalResult?.properties as EvalResultProperties;
      expect(props.evalType).toBe('capability');
      expect(props.passAt1).toBe(0.85);
      expect(props.testsPassed).toBe(17);
    });
  });

  describe('querySkillContext', () => {
    beforeEach(async () => {
      // Create test data
      await bridge.startSession('Context test session');
      
      const patternEntity: SkillEntity = {
        id: 'pattern-001',
        type: 'learned_pattern',
        name: 'Null Check Pattern',
        description: 'Pattern for null checking',
        properties: {
          kind: 'learned_pattern',
          category: 'error_resolution',
          problem: 'null pointer exception',
          solution: 'add null check',
          confidence: 0.9,
          usageCount: 5,
        },
        tags: ['pattern', 'error'],
      };
      await bridge.storeSkillEntity(patternEntity);
    });

    it('should query by error context', async () => {
      const context: SkillQueryContext = {
        errorContext: 'null pointer',
      };

      const result = await bridge.querySkillContext(context);

      expect(result.entities.length).toBeGreaterThan(0);
      expect(result.querySource).toBe('pattern');
    });

    it('should query by keywords', async () => {
      const context: SkillQueryContext = {
        taskKeywords: ['null', 'check'],
      };

      const result = await bridge.querySkillContext(context);

      expect(result.entities.length).toBeGreaterThan(0);
    });
  });

  describe('getSessionHistory', () => {
    it('should return session history', async () => {
      await bridge.startSession('Session 1');
      await bridge.startSession('Session 2');
      await bridge.startSession('Session 3');

      const history = await bridge.getSessionHistory(2);

      expect(history.length).toBeLessThanOrEqual(2);
      history.forEach(s => expect(s.type).toBe('session'));
    });
  });

  describe('getStatistics', () => {
    it('should return correct statistics', async () => {
      const session1 = await bridge.startSession('Stats test 1');
      const session2 = await bridge.startSession('Stats test 2');
      
      await bridge.endSession(session1, 'completed', ['skill1']);
      await bridge.endSession(session2, 'failed', ['skill2']);
      
      await bridge.recordCheckpoint(session1, 'phase1', '/tmp/cp1');

      const stats = await bridge.getStatistics();

      expect(stats.totalSessions).toBe(2);
      expect(stats.completedSessions).toBe(1);
      expect(stats.failedSessions).toBe(1);
      expect(stats.totalCheckpoints).toBe(1);
    });
  });
});

describe('formatSessionAsMarkdown', () => {
  it('should format session correctly', () => {
    const session: SkillEntity = {
      id: 'session-123',
      type: 'session',
      name: 'Test Session',
      properties: {
        kind: 'session',
        startedAt: '2024-01-15T10:00:00Z',
        endedAt: '2024-01-15T11:30:00Z',
        status: 'completed',
        taskDescription: 'Implement feature X',
        skillsUsed: ['eval-harness', 'build-fix'],
        checkpointCount: 3,
      } as SessionProperties,
      tags: ['session', 'completed'],
    };

    const markdown = formatSessionAsMarkdown(session);

    expect(markdown).toContain('Session: session-123');
    expect(markdown).toContain('**Status**: completed');
    expect(markdown).toContain('Implement feature X');
    expect(markdown).toContain('eval-harness');
    expect(markdown).toContain('**Checkpoints**: 3');
  });

  it('should throw for non-session entity', () => {
    const entity: SkillEntity = {
      id: 'skill-001',
      type: 'skill',
      name: 'Test',
      properties: { kind: 'skill', version: '1.0.0', triggers: [], commands: [] },
      tags: [],
    };

    expect(() => formatSessionAsMarkdown(entity)).toThrow('not a session');
  });
});

describe('formatContextAsMarkdown', () => {
  it('should format empty result', () => {
    const markdown = formatContextAsMarkdown({
      entities: [],
      scores: new Map(),
      querySource: 'related',
    });

    expect(markdown).toContain('No relevant context found');
  });

  it('should format context with entities', () => {
    const entities: SkillEntity[] = [
      {
        id: 'pattern-001',
        type: 'learned_pattern',
        name: 'Test Pattern',
        description: 'A test pattern',
        properties: {
          kind: 'learned_pattern',
          category: 'error_resolution',
          problem: 'test',
          solution: 'solution',
          confidence: 0.9,
          usageCount: 1,
        },
        tags: [],
      },
    ];

    const markdown = formatContextAsMarkdown({
      entities,
      scores: new Map([['pattern-001', 0.85]]),
      querySource: 'pattern',
    });

    expect(markdown).toContain('Context Query Result (pattern)');
    expect(markdown).toContain('Test Pattern');
    expect(markdown).toContain('85.0%');
  });
});
