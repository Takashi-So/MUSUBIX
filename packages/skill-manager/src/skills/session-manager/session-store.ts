/**
 * Session Store Implementation
 *
 * File-based session storage with Markdown format
 *
 * @see REQ-SM-001 - SessionStart Hook
 * @see REQ-SM-002 - SessionEnd Hook
 * @see REQ-SM-003 - Pre-Compact State Saving
 * @see DES-v3.7.0 Section 4.2 - SessionStore
 */

import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import { homedir } from 'node:os';

import type {
  SessionData,
  SessionNotification,
  SessionSaveResult,
  SessionSearchOptions,
  SessionStore,
  SessionStoreConfig,
  TodoItem,
  PreCompactSnapshot,
} from './types.js';
import { DEFAULT_SESSION_STORE_CONFIG } from './types.js';

/**
 * Resolve home directory in path
 */
function resolvePath(p: string): string {
  if (p.startsWith('~')) {
    return path.join(homedir(), p.slice(1));
  }
  return p;
}

/**
 * Generate session ID from date
 */
function generateSessionId(date: Date): string {
  const pad = (n: number): string => n.toString().padStart(2, '0');
  return `${date.getFullYear()}-${pad(date.getMonth() + 1)}-${pad(date.getDate())}-${pad(date.getHours())}-${pad(date.getMinutes())}`;
}

/**
 * Parse session ID to date
 */
function parseSessionId(id: string): Date | null {
  const match = id.match(/^(\d{4})-(\d{2})-(\d{2})-(\d{2})-(\d{2})$/);
  if (!match) return null;
  const [, year, month, day, hour, minute] = match;
  return new Date(
    parseInt(year, 10),
    parseInt(month, 10) - 1,
    parseInt(day, 10),
    parseInt(hour, 10),
    parseInt(minute, 10)
  );
}

/**
 * Format todo item for markdown
 */
function formatTodoItem(item: TodoItem): string {
  const checkbox = item.status === 'completed' ? '[x]' : '[ ]';
  const blocked = item.blockedReason ? ` (blocked: ${item.blockedReason})` : '';
  return `- ${checkbox} ${item.title}${blocked}`;
}

/**
 * Format session data to markdown
 */
function formatSessionToMarkdown(session: SessionData): string {
  const lines: string[] = [];

  lines.push(`# Session: ${session.date}`);
  lines.push('');
  lines.push(`**Date:** ${session.date}`);
  lines.push(`**Started:** ${formatTime(session.startedAt)}`);
  lines.push(`**Last Updated:** ${formatTime(session.lastUpdatedAt)}`);
  if (session.projectName) {
    lines.push(`**Project:** ${session.projectName}`);
  }
  lines.push('');
  lines.push('---');
  lines.push('');
  lines.push('## Current State');
  lines.push('');

  lines.push('### Completed');
  if (session.completedTasks.length > 0) {
    for (const task of session.completedTasks) {
      lines.push(formatTodoItem(task));
    }
  } else {
    lines.push('_No completed tasks_');
  }
  lines.push('');

  lines.push('### In Progress');
  if (session.inProgressTasks.length > 0) {
    for (const task of session.inProgressTasks) {
      lines.push(formatTodoItem(task));
    }
  } else {
    lines.push('_No tasks in progress_');
  }
  lines.push('');

  if (session.blockedTasks.length > 0) {
    lines.push('### Blocked');
    for (const task of session.blockedTasks) {
      lines.push(formatTodoItem(task));
    }
    lines.push('');
  }

  lines.push('---');
  lines.push('');
  lines.push('## Notes for Next Session');
  lines.push('');
  if (session.notesForNextSession.length > 0) {
    for (const note of session.notesForNextSession) {
      lines.push(`- ${note}`);
    }
  } else {
    lines.push('_No notes_');
  }
  lines.push('');

  lines.push('---');
  lines.push('');
  lines.push('## Context to Load');
  lines.push('');
  lines.push('```');
  if (session.contextToLoad.length > 0) {
    for (const ctx of session.contextToLoad) {
      lines.push(ctx);
    }
  } else {
    lines.push('# No specific files to load');
  }
  lines.push('```');
  lines.push('');

  // Pre-compact snapshots
  if (session.preCompactSnapshots.length > 0) {
    lines.push('---');
    lines.push('');
    lines.push('## Pre-Compact Snapshots');
    lines.push('');
    for (const snapshot of session.preCompactSnapshots) {
      lines.push(`### Snapshot at ${formatTime(snapshot.timestamp)}`);
      lines.push('');
      lines.push(`**Tool Calls:** ${snapshot.toolCallCount}`);
      lines.push('');
      lines.push('**Active Context:**');
      for (const ctx of snapshot.activeContext) {
        lines.push(`- ${ctx}`);
      }
      lines.push('');
      lines.push('**Key Decisions:**');
      for (const decision of snapshot.keyDecisions) {
        lines.push(`- ${decision.decision}: ${decision.reason}`);
      }
      lines.push('');
      lines.push('**Pending Issues:**');
      for (const issue of snapshot.pendingIssues) {
        lines.push(`- ${issue}`);
      }
      lines.push('');
    }
  }

  lines.push('---');
  lines.push('');
  lines.push('## Session Summary');
  lines.push('');
  lines.push(`- **Tasks Completed:** ${session.summary.tasksCompleted}`);
  lines.push(`- **Patterns Learned:** ${session.summary.patternsLearned}`);
  lines.push(`- **Checkpoints Created:** ${session.summary.checkpointsCreated}`);
  lines.push(`- **Tool Calls Total:** ${session.summary.toolCallsTotal}`);
  lines.push('');

  return lines.join('\n');
}

/**
 * Format time for display
 */
function formatTime(date: Date): string {
  const pad = (n: number): string => n.toString().padStart(2, '0');
  return `${pad(date.getHours())}:${pad(date.getMinutes())}`;
}

/**
 * Parse markdown to session data
 */
function parseMarkdownToSession(content: string, filename: string): SessionData | null {
  try {
    const sessionId = filename.replace('.md', '');
    const dateFromId = parseSessionId(sessionId);
    if (!dateFromId) return null;

    // Extract date from content
    const dateMatch = content.match(/\*\*Date:\*\* (.+)/);
    const startedMatch = content.match(/\*\*Started:\*\* (\d{2}:\d{2})/);
    const lastUpdatedMatch = content.match(/\*\*Last Updated:\*\* (\d{2}:\d{2})/);
    const projectMatch = content.match(/\*\*Project:\*\* (.+)/);

    const date = dateMatch?.[1] || sessionId.slice(0, 10);
    const startedTime = startedMatch?.[1] || '00:00';
    const lastUpdatedTime = lastUpdatedMatch?.[1] || startedTime;
    const projectName = projectMatch?.[1];

    // Parse started/updated times
    const [startHour, startMin] = startedTime.split(':').map(Number);
    const [updateHour, updateMin] = lastUpdatedTime.split(':').map(Number);

    const startedAt = new Date(dateFromId);
    startedAt.setHours(startHour, startMin);

    const lastUpdatedAt = new Date(dateFromId);
    lastUpdatedAt.setHours(updateHour, updateMin);

    // Extract tasks
    const completedTasks = extractTasks(content, 'Completed', 'completed');
    const inProgressTasks = extractTasks(content, 'In Progress', 'in-progress');
    const blockedTasks = extractTasks(content, 'Blocked', 'blocked');

    // Extract notes
    const notesSection = extractSection(content, 'Notes for Next Session');
    const notesForNextSession = extractListItems(notesSection);

    // Extract context to load
    const contextSection = extractSection(content, 'Context to Load');
    const codeBlockMatch = contextSection.match(/```[\s\S]*?\n([\s\S]*?)```/);
    const contextToLoad = codeBlockMatch
      ? codeBlockMatch[1].split('\n').filter((line) => line.trim() && !line.startsWith('#'))
      : [];

    // Extract summary
    const summarySection = extractSection(content, 'Session Summary');
    const summary = {
      tasksCompleted: extractNumber(summarySection, 'Tasks Completed') || completedTasks.length,
      patternsLearned: extractNumber(summarySection, 'Patterns Learned') || 0,
      checkpointsCreated: extractNumber(summarySection, 'Checkpoints Created') || 0,
      toolCallsTotal: extractNumber(summarySection, 'Tool Calls Total') || 0,
    };

    return {
      id: sessionId,
      date,
      startedAt,
      lastUpdatedAt,
      projectName,
      completedTasks,
      inProgressTasks,
      blockedTasks,
      notesForNextSession,
      contextToLoad,
      preCompactSnapshots: [], // TODO: Parse pre-compact snapshots
      summary,
    };
  } catch {
    return null;
  }
}

/**
 * Extract tasks from a section
 */
function extractTasks(content: string, sectionName: string, status: TodoItem['status']): TodoItem[] {
  const section = extractSection(content, sectionName);
  const lines = section.split('\n').filter((line) => line.trim().startsWith('- ['));
  const tasks: TodoItem[] = [];

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const isCompleted = line.includes('[x]');
    const blockedMatch = line.match(/\(blocked: (.+)\)/);
    const title = line
      .replace(/^- \[.\] /, '')
      .replace(/\(blocked: .+\)/, '')
      .trim();

    tasks.push({
      id: `task-${i + 1}`,
      title,
      status: isCompleted ? 'completed' : status,
      order: i,
      createdAt: new Date(),
      updatedAt: new Date(),
      blockedReason: blockedMatch?.[1],
    });
  }

  return tasks;
}

/**
 * Extract a section from content
 */
function extractSection(content: string, sectionName: string): string {
  const regex = new RegExp(`## ${sectionName}[\\s\\S]*?(?=\\n## |\\n---\\n|$)`, 'i');
  const match = content.match(regex);
  return match?.[0] || '';
}

/**
 * Extract list items from section
 */
function extractListItems(section: string): string[] {
  const lines = section.split('\n').filter((line) => line.trim().startsWith('- '));
  return lines.map((line) => line.replace(/^- /, '').trim()).filter((item) => !item.startsWith('_'));
}

/**
 * Extract number from summary
 */
function extractNumber(section: string, key: string): number | null {
  const regex = new RegExp(`\\*\\*${key}:\\*\\* (\\d+)`);
  const match = section.match(regex);
  return match ? parseInt(match[1], 10) : null;
}

/**
 * Create a file-based session store
 *
 * @param config - Store configuration
 * @returns SessionStore instance
 */
export function createSessionStore(config: Partial<SessionStoreConfig> = {}): SessionStore {
  const fullConfig: SessionStoreConfig = {
    ...DEFAULT_SESSION_STORE_CONFIG,
    ...config,
  };

  const sessionsDir = resolvePath(fullConfig.sessionsDir);

  /**
   * Ensure sessions directory exists
   */
  async function ensureDir(): Promise<void> {
    await fs.mkdir(sessionsDir, { recursive: true });
  }

  /**
   * Get all session files
   */
  async function getSessionFiles(): Promise<string[]> {
    await ensureDir();
    const files = await fs.readdir(sessionsDir);
    return files.filter((f) => f.endsWith('.md')).sort().reverse();
  }

  return {
    async searchSessions(options: SessionSearchOptions = {}): Promise<SessionData[]> {
      const { daysBack = 7, projectName, limit = 10 } = options;
      const cutoffDate = new Date();
      cutoffDate.setDate(cutoffDate.getDate() - daysBack);

      const files = await getSessionFiles();
      const sessions: SessionData[] = [];

      for (const file of files) {
        if (sessions.length >= limit) break;

        const sessionId = file.replace('.md', '');
        const sessionDate = parseSessionId(sessionId);
        if (!sessionDate || sessionDate < cutoffDate) continue;

        const filePath = path.join(sessionsDir, file);
        const content = await fs.readFile(filePath, 'utf-8');
        const session = parseMarkdownToSession(content, file);

        if (session) {
          if (!projectName || session.projectName === projectName) {
            sessions.push(session);
          }
        }
      }

      return sessions;
    },

    async getSession(sessionId: string): Promise<SessionData | null> {
      const filePath = path.join(sessionsDir, `${sessionId}.md`);
      try {
        const content = await fs.readFile(filePath, 'utf-8');
        return parseMarkdownToSession(content, `${sessionId}.md`);
      } catch {
        return null;
      }
    },

    async saveSession(session: SessionData): Promise<SessionSaveResult> {
      try {
        await ensureDir();

        const markdown = formatSessionToMarkdown(session);
        const filePath = path.join(sessionsDir, `${session.id}.md`);

        // Check file size
        if (Buffer.byteLength(markdown, 'utf-8') > fullConfig.maxFileSizeBytes) {
          return {
            success: false,
            error: `Session file exceeds maximum size of ${fullConfig.maxFileSizeBytes} bytes`,
          };
        }

        await fs.writeFile(filePath, markdown, 'utf-8');

        return {
          success: true,
          filePath,
        };
      } catch (error) {
        return {
          success: false,
          error: error instanceof Error ? error.message : String(error),
        };
      }
    },

    async getStartNotification(options: SessionSearchOptions = {}): Promise<SessionNotification> {
      const sessions = await this.searchSessions({ ...options, limit: 1 });
      const previousSession = sessions[0] || null;

      if (!previousSession) {
        return {
          previousSession: null,
          unfinishedTasks: [],
          notesFromLastSession: [],
          recommendedFiles: [],
          message: '新しいセッションを開始します。過去のセッションデータはありません。',
        };
      }

      const unfinishedTasks = [...previousSession.inProgressTasks, ...previousSession.blockedTasks];

      const lines: string[] = [
        '📋 **前回セッションからの引き継ぎ**',
        '',
        `**日時**: ${previousSession.date} ${formatTime(previousSession.lastUpdatedAt)}`,
        '',
      ];

      if (unfinishedTasks.length > 0) {
        lines.push('**未完了タスク**:');
        for (const task of unfinishedTasks) {
          lines.push(`- [ ] ${task.title}`);
        }
        lines.push('');
      }

      if (previousSession.notesForNextSession.length > 0) {
        lines.push('**次回向けメモ**:');
        for (const note of previousSession.notesForNextSession) {
          lines.push(`- ${note}`);
        }
        lines.push('');
      }

      if (previousSession.contextToLoad.length > 0) {
        lines.push('**読み込み推奨ファイル**:');
        for (const file of previousSession.contextToLoad) {
          lines.push(`- \`${file}\``);
        }
        lines.push('');
      }

      lines.push('続きから作業を再開しますか？');

      return {
        previousSession,
        unfinishedTasks,
        notesFromLastSession: previousSession.notesForNextSession,
        recommendedFiles: previousSession.contextToLoad,
        message: lines.join('\n'),
      };
    },

    async cleanup(): Promise<number> {
      const cutoffDate = new Date();
      cutoffDate.setDate(cutoffDate.getDate() - fullConfig.retentionDays);

      const files = await getSessionFiles();
      let deletedCount = 0;

      // Delete old files
      for (const file of files) {
        const sessionId = file.replace('.md', '');
        const sessionDate = parseSessionId(sessionId);
        if (sessionDate && sessionDate < cutoffDate) {
          await fs.unlink(path.join(sessionsDir, file));
          deletedCount++;
        }
      }

      // Delete excess files (keep maxFileCount)
      const remainingFiles = await getSessionFiles();
      if (remainingFiles.length > fullConfig.maxFileCount) {
        const toDelete = remainingFiles.slice(fullConfig.maxFileCount);
        for (const file of toDelete) {
          await fs.unlink(path.join(sessionsDir, file));
          deletedCount++;
        }
      }

      return deletedCount;
    },
  };
}

/**
 * Create a new session
 *
 * @param projectName - Optional project name
 * @returns New session data
 */
export function createNewSession(projectName?: string): SessionData {
  const now = new Date();
  const id = generateSessionId(now);
  const date = `${now.getFullYear()}-${(now.getMonth() + 1).toString().padStart(2, '0')}-${now.getDate().toString().padStart(2, '0')}`;

  return {
    id,
    date,
    startedAt: now,
    lastUpdatedAt: now,
    projectName,
    completedTasks: [],
    inProgressTasks: [],
    blockedTasks: [],
    notesForNextSession: [],
    contextToLoad: [],
    preCompactSnapshots: [],
    summary: {
      tasksCompleted: 0,
      patternsLearned: 0,
      checkpointsCreated: 0,
      toolCallsTotal: 0,
    },
  };
}

/**
 * Add a pre-compact snapshot to session
 *
 * @param session - Current session
 * @param snapshot - Snapshot to add
 * @returns Updated session
 */
export function addPreCompactSnapshot(
  session: SessionData,
  snapshot: Omit<PreCompactSnapshot, 'timestamp'>
): SessionData {
  return {
    ...session,
    lastUpdatedAt: new Date(),
    preCompactSnapshots: [
      ...session.preCompactSnapshots,
      {
        ...snapshot,
        timestamp: new Date(),
      },
    ],
  };
}
