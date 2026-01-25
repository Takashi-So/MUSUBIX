/**
 * Session Store Tests
 *
 * @see REQ-SM-001 - SessionStart Hook
 * @see REQ-SM-002 - SessionEnd Hook
 * @see REQ-SM-003 - Pre-Compact State Saving
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import { tmpdir } from 'node:os';

import {
  createSessionStore,
  createNewSession,
  addPreCompactSnapshot,
  type SessionStore,
  type SessionData,
} from '../../src/skills/session-manager/index.js';

describe('SessionStore', () => {
  let testDir: string;
  let store: SessionStore;

  beforeEach(async () => {
    // Create temp directory for tests
    testDir = path.join(tmpdir(), `musubix-session-test-${Date.now()}`);
    await fs.mkdir(testDir, { recursive: true });

    store = createSessionStore({
      sessionsDir: testDir,
      retentionDays: 7,
      maxFileSizeBytes: 1024 * 1024,
      maxFileCount: 10,
    });
  });

  afterEach(async () => {
    // Cleanup
    await fs.rm(testDir, { recursive: true, force: true });
  });

  describe('createNewSession', () => {
    it('should create a new session with correct format', () => {
      const session = createNewSession('test-project');

      expect(session.id).toMatch(/^\d{4}-\d{2}-\d{2}-\d{2}-\d{2}$/);
      expect(session.projectName).toBe('test-project');
      expect(session.completedTasks).toEqual([]);
      expect(session.inProgressTasks).toEqual([]);
      expect(session.blockedTasks).toEqual([]);
      expect(session.notesForNextSession).toEqual([]);
      expect(session.contextToLoad).toEqual([]);
      expect(session.summary.tasksCompleted).toBe(0);
    });

    it('should create session without project name', () => {
      const session = createNewSession();

      expect(session.projectName).toBeUndefined();
    });
  });

  describe('saveSession', () => {
    it('should save session to file', async () => {
      const session = createNewSession('test-project');
      const result = await store.saveSession(session);

      expect(result.success).toBe(true);
      expect(result.filePath).toBeDefined();

      // Verify file exists
      const files = await fs.readdir(testDir);
      expect(files).toContain(`${session.id}.md`);
    });

    it('should save session with tasks', async () => {
      const session: SessionData = {
        ...createNewSession('test-project'),
        completedTasks: [
          {
            id: 'task-1',
            title: 'Task 1',
            status: 'completed',
            order: 0,
            createdAt: new Date(),
            updatedAt: new Date(),
          },
        ],
        inProgressTasks: [
          {
            id: 'task-2',
            title: 'Task 2',
            status: 'in-progress',
            order: 1,
            createdAt: new Date(),
            updatedAt: new Date(),
          },
        ],
        notesForNextSession: ['Note 1', 'Note 2'],
        contextToLoad: ['path/to/file1.ts', 'path/to/file2.ts'],
      };

      const result = await store.saveSession(session);
      expect(result.success).toBe(true);

      // Read and verify content
      const content = await fs.readFile(result.filePath!, 'utf-8');
      expect(content).toContain('Task 1');
      expect(content).toContain('Task 2');
      expect(content).toContain('Note 1');
      expect(content).toContain('path/to/file1.ts');
    });

    it('should reject oversized sessions', async () => {
      const store = createSessionStore({
        sessionsDir: testDir,
        maxFileSizeBytes: 100, // Very small limit
      });

      const session: SessionData = {
        ...createNewSession('test-project'),
        notesForNextSession: Array(100).fill('This is a very long note that will exceed the limit'),
      };

      const result = await store.saveSession(session);
      expect(result.success).toBe(false);
      expect(result.error).toContain('exceeds maximum size');
    });
  });

  describe('getSession', () => {
    it('should retrieve saved session', async () => {
      const original = createNewSession('test-project');
      await store.saveSession(original);

      const retrieved = await store.getSession(original.id);

      expect(retrieved).not.toBeNull();
      expect(retrieved!.id).toBe(original.id);
      expect(retrieved!.projectName).toBe('test-project');
    });

    it('should return null for non-existent session', async () => {
      const result = await store.getSession('non-existent');
      expect(result).toBeNull();
    });
  });

  describe('searchSessions', () => {
    it('should find recent sessions', async () => {
      // Create multiple sessions
      const session1 = createNewSession('project-1');
      const session2 = createNewSession('project-2');

      await store.saveSession(session1);
      await store.saveSession(session2);

      const results = await store.searchSessions({ daysBack: 7 });

      expect(results.length).toBeGreaterThanOrEqual(1);
    });

    it('should filter by project name', async () => {
      const session1: SessionData = { ...createNewSession(), projectName: 'project-a' };
      const session2: SessionData = { ...createNewSession(), projectName: 'project-b' };

      // Modify IDs to be unique
      const now = new Date();
      session1.id = `${session1.id.slice(0, -2)}01`;
      session2.id = `${session2.id.slice(0, -2)}02`;

      await store.saveSession(session1);
      await store.saveSession(session2);

      const results = await store.searchSessions({ projectName: 'project-a' });

      expect(results.every((s) => s.projectName === 'project-a')).toBe(true);
    });

    it('should respect limit', async () => {
      // Create 5 sessions
      for (let i = 0; i < 5; i++) {
        const session = createNewSession();
        session.id = `2026-01-25-14-${String(i).padStart(2, '0')}`;
        await store.saveSession(session as SessionData);
      }

      const results = await store.searchSessions({ limit: 3 });

      expect(results.length).toBeLessThanOrEqual(3);
    });
  });

  describe('getStartNotification', () => {
    it('should return empty notification when no sessions exist', async () => {
      const notification = await store.getStartNotification();

      expect(notification.previousSession).toBeNull();
      expect(notification.unfinishedTasks).toEqual([]);
      expect(notification.message).toContain('過去のセッションデータはありません');
    });

    it('should return notification with previous session data', async () => {
      const session: SessionData = {
        ...createNewSession('test-project'),
        inProgressTasks: [
          {
            id: 'task-1',
            title: 'Unfinished Task',
            status: 'in-progress',
            order: 0,
            createdAt: new Date(),
            updatedAt: new Date(),
          },
        ],
        notesForNextSession: ['Important note'],
        contextToLoad: ['important/file.ts'],
      };

      await store.saveSession(session);

      const notification = await store.getStartNotification();

      expect(notification.previousSession).not.toBeNull();
      expect(notification.unfinishedTasks).toHaveLength(1);
      expect(notification.unfinishedTasks[0].title).toBe('Unfinished Task');
      expect(notification.notesFromLastSession).toContain('Important note');
      expect(notification.recommendedFiles).toContain('important/file.ts');
      expect(notification.message).toContain('前回セッションからの引き継ぎ');
    });
  });

  describe('cleanup', () => {
    it('should delete old sessions', async () => {
      // Create old session file manually
      const oldDate = new Date();
      oldDate.setDate(oldDate.getDate() - 40); // 40 days ago

      const oldSessionId = `${oldDate.getFullYear()}-${String(oldDate.getMonth() + 1).padStart(2, '0')}-${String(oldDate.getDate()).padStart(2, '0')}-10-00`;
      const oldFilePath = path.join(testDir, `${oldSessionId}.md`);

      await fs.writeFile(oldFilePath, '# Old Session\n', 'utf-8');

      const store = createSessionStore({
        sessionsDir: testDir,
        retentionDays: 30,
      });

      const deletedCount = await store.cleanup();

      expect(deletedCount).toBeGreaterThanOrEqual(1);

      // Verify file is deleted
      const files = await fs.readdir(testDir);
      expect(files).not.toContain(`${oldSessionId}.md`);
    });

    it('should enforce max file count', async () => {
      const store = createSessionStore({
        sessionsDir: testDir,
        maxFileCount: 3,
      });

      // Create 5 sessions
      for (let i = 0; i < 5; i++) {
        const session = createNewSession();
        session.id = `2026-01-25-14-${String(i * 10).padStart(2, '0')}`;
        await store.saveSession(session as SessionData);
      }

      const deletedCount = await store.cleanup();

      expect(deletedCount).toBeGreaterThanOrEqual(2);

      const files = await fs.readdir(testDir);
      expect(files.length).toBeLessThanOrEqual(3);
    });
  });

  describe('addPreCompactSnapshot', () => {
    it('should add snapshot to session', () => {
      const session = createNewSession('test-project');

      const updated = addPreCompactSnapshot(session, {
        toolCallCount: 50,
        activeContext: ['Current task'],
        keyDecisions: [{ decision: 'Use TypeScript', reason: 'Type safety' }],
        pendingIssues: ['Fix bug #123'],
      });

      expect(updated.preCompactSnapshots).toHaveLength(1);
      expect(updated.preCompactSnapshots[0].toolCallCount).toBe(50);
      expect(updated.preCompactSnapshots[0].timestamp).toBeInstanceOf(Date);
    });

    it('should preserve existing snapshots', () => {
      let session = createNewSession('test-project');

      session = addPreCompactSnapshot(session, {
        toolCallCount: 25,
        activeContext: [],
        keyDecisions: [],
        pendingIssues: [],
      });

      session = addPreCompactSnapshot(session, {
        toolCallCount: 50,
        activeContext: [],
        keyDecisions: [],
        pendingIssues: [],
      });

      expect(session.preCompactSnapshots).toHaveLength(2);
      expect(session.preCompactSnapshots[0].toolCallCount).toBe(25);
      expect(session.preCompactSnapshots[1].toolCallCount).toBe(50);
    });
  });
});
