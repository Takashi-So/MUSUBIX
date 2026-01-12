/**
 * Watch MCP Tools
 *
 * Implements: TSK-WATCH-008, DES-WATCH-006, REQ-WATCH-007〜008
 * @see DES-DX-v3.1.0 Section Watch Module MCP Tools
 */

import type { Tool, CallToolResult, TextContent } from '@modelcontextprotocol/sdk/types.js';
import { resolve } from 'node:path';

/**
 * Tool: watch_start - Start file watching session
 */
export const watchStartTool: Tool = {
  name: 'watch_start',
  description: 'Start file watching and auto-validation. Monitors files for changes and runs lint/test/security automatically.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      paths: {
        type: 'array',
        items: { type: 'string' },
        description: 'Paths to watch (default: ["src/"])',
      },
      tasks: {
        type: 'array',
        items: { type: 'string', enum: ['lint', 'test', 'security', 'ears'] },
        description: 'Tasks to run on changes (default: ["lint", "test"])',
      },
      debounceMs: {
        type: 'number',
        description: 'Debounce time in milliseconds (default: 300)',
      },
      extensions: {
        type: 'array',
        items: { type: 'string' },
        description: 'File extensions to watch (default: auto-detect)',
      },
    },
    required: [],
  },
};

/**
 * Tool: watch_stop - Stop file watching session
 */
export const watchStopTool: Tool = {
  name: 'watch_stop',
  description: 'Stop the active file watching session.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      sessionId: {
        type: 'string',
        description: 'Watch session ID (optional, stops active session)',
      },
    },
    required: [],
  },
};

/**
 * Tool: watch_status - Get watch session status
 */
export const watchStatusTool: Tool = {
  name: 'watch_status',
  description: 'Get the status of active watch sessions.',
  inputSchema: {
    type: 'object' as const,
    properties: {},
    required: [],
  },
};

/**
 * Tool: watch_run_now - Run tasks immediately
 */
export const watchRunNowTool: Tool = {
  name: 'watch_run_now',
  description: 'Run specified tasks immediately on given files without waiting for changes.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      files: {
        type: 'array',
        items: { type: 'string' },
        description: 'Files to check',
      },
      tasks: {
        type: 'array',
        items: { type: 'string', enum: ['lint', 'test', 'security', 'ears'] },
        description: 'Tasks to run',
      },
    },
    required: ['files', 'tasks'],
  },
};

/**
 * Tool: watch_report - Get accumulated issues report
 */
export const watchReportTool: Tool = {
  name: 'watch_report',
  description: 'Get accumulated issues report from watch session.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      format: {
        type: 'string',
        enum: ['json', 'markdown', 'summary'],
        description: 'Output format (default: summary)',
      },
      severity: {
        type: 'string',
        enum: ['error', 'warning', 'info', 'all'],
        description: 'Filter by severity (default: all)',
      },
    },
    required: [],
  },
};

// Watch session state (in-memory for MCP context)
interface WatchSession {
  id: string;
  paths: string[];
  tasks: string[];
  startTime: Date;
  issues: Array<{
    severity: string;
    message: string;
    file: string;
    line?: number;
    ruleId?: string;
  }>;
  isRunning: boolean;
}

let activeSession: WatchSession | null = null;

/**
 * Handle watch_start tool call
 */
export async function handleWatchStart(args: {
  paths?: string[];
  tasks?: string[];
  debounceMs?: number;
  extensions?: string[];
}): Promise<CallToolResult> {
  // If session already active, return error
  if (activeSession?.isRunning) {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: false,
            error: 'Watch session already active. Call watch_stop first.',
            sessionId: activeSession.id,
          }),
        },
      ],
    };
  }

  const sessionId = `watch-${Date.now()}`;
  const paths = args.paths ?? ['src/'];
  const tasks = args.tasks ?? ['lint', 'test'];

  activeSession = {
    id: sessionId,
    paths: paths.map((p) => resolve(process.cwd(), p)),
    tasks,
    startTime: new Date(),
    issues: [],
    isRunning: true,
  };

  // Note: In MCP context, actual file watching would be managed by the MCP server
  // This returns configuration for the client to initiate watching

  const result = {
    success: true,
    sessionId,
    config: {
      paths: activeSession.paths,
      tasks,
      debounceMs: args.debounceMs ?? 300,
      extensions: args.extensions ?? getDefaultExtensions(tasks),
    },
    message: `Watch session started. Monitoring ${paths.join(', ')} for ${tasks.join(', ')}`,
  };

  return {
    content: [{ type: 'text', text: JSON.stringify(result, null, 2) } as TextContent],
  };
}

/**
 * Handle watch_stop tool call
 */
export async function handleWatchStop(_args: {
  sessionId?: string;
}): Promise<CallToolResult> {
  if (!activeSession) {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: false,
            error: 'No active watch session to stop.',
          }),
        },
      ],
    };
  }

  const session = activeSession;
  activeSession = null;

  const duration = Date.now() - session.startTime.getTime();
  const result = {
    success: true,
    sessionId: session.id,
    duration: `${Math.round(duration / 1000)}s`,
    totalIssues: session.issues.length,
    message: 'Watch session stopped.',
  };

  return {
    content: [{ type: 'text', text: JSON.stringify(result, null, 2) } as TextContent],
  };
}

/**
 * Handle watch_status tool call
 */
export async function handleWatchStatus(): Promise<CallToolResult> {
  if (!activeSession) {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            active: false,
            message: 'No active watch session.',
          }),
        },
      ],
    };
  }

  const duration = Date.now() - activeSession.startTime.getTime();
  const result = {
    active: true,
    sessionId: activeSession.id,
    paths: activeSession.paths,
    tasks: activeSession.tasks,
    duration: `${Math.round(duration / 1000)}s`,
    issueCount: activeSession.issues.length,
    recentIssues: activeSession.issues.slice(-5),
  };

  return {
    content: [{ type: 'text', text: JSON.stringify(result, null, 2) } as TextContent],
  };
}

/**
 * Handle watch_run_now tool call
 */
export async function handleWatchRunNow(args: {
  files: string[];
  tasks: string[];
}): Promise<CallToolResult> {
  const { LintRunner, TestRunner, SecurityRunner, EARSRunner } =
    await import('@nahisaho/musubix-core');

  const issues: Array<{
    task: string;
    severity: string;
    message: string;
    file: string;
    line?: number;
    ruleId?: string;
  }> = [];

  // Register runners for requested tasks
  const runnerMap: Record<string, { runner: { run: (files: string[]) => Promise<unknown[]> }; taskType: string }> = {
    lint: { runner: new LintRunner(), taskType: 'lint' },
    test: { runner: new TestRunner(), taskType: 'test' },
    security: { runner: new SecurityRunner(), taskType: 'security' },
    ears: { runner: new EARSRunner(), taskType: 'ears' },
  };

  // Run each task
  for (const task of args.tasks) {
    const config = runnerMap[task];
    if (!config) continue;

    try {
      const taskIssues = await config.runner.run(args.files);
      for (const issue of taskIssues as Array<{ severity: string; message: string; file: string; line?: number; ruleId?: string }>) {
        issues.push({
          task,
          ...issue,
        });
      }
    } catch (error) {
      issues.push({
        task,
        severity: 'error',
        message: `${task} failed: ${error instanceof Error ? error.message : String(error)}`,
        file: args.files[0],
      });
    }
  }

  // If active session, add to issues
  if (activeSession) {
    activeSession.issues.push(...issues);
  }

  const result = {
    success: true,
    files: args.files.length,
    tasks: args.tasks,
    issueCount: issues.length,
    issues,
    summary: {
      errors: issues.filter((i) => i.severity === 'error').length,
      warnings: issues.filter((i) => i.severity === 'warning').length,
      info: issues.filter((i) => i.severity === 'info').length,
    },
  };

  return {
    content: [{ type: 'text', text: JSON.stringify(result, null, 2) } as TextContent],
  };
}

/**
 * Handle watch_report tool call
 */
export async function handleWatchReport(args: {
  format?: 'json' | 'markdown' | 'summary';
  severity?: 'error' | 'warning' | 'info' | 'all';
}): Promise<CallToolResult> {
  if (!activeSession) {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: false,
            error: 'No active watch session.',
          }),
        },
      ],
    };
  }

  const format = args.format ?? 'summary';
  const severity = args.severity ?? 'all';

  let filteredIssues = activeSession.issues;
  if (severity !== 'all') {
    filteredIssues = activeSession.issues.filter((i) => i.severity === severity);
  }

  if (format === 'json') {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            sessionId: activeSession.id,
            issues: filteredIssues,
          }, null, 2),
        } as TextContent,
      ],
    };
  }

  if (format === 'markdown') {
    let md = `# Watch Report\n\n`;
    md += `**Session**: ${activeSession.id}\n`;
    md += `**Paths**: ${activeSession.paths.join(', ')}\n`;
    md += `**Tasks**: ${activeSession.tasks.join(', ')}\n\n`;
    md += `## Issues (${filteredIssues.length})\n\n`;

    if (filteredIssues.length === 0) {
      md += '_No issues found._\n';
    } else {
      for (const issue of filteredIssues) {
        const icon = issue.severity === 'error' ? '❌' : issue.severity === 'warning' ? '⚠️' : 'ℹ️';
        const location = issue.line ? `${issue.file}:${issue.line}` : issue.file;
        md += `- ${icon} **${issue.severity}**: ${issue.message}\n`;
        md += `  - File: \`${location}\`\n`;
        if (issue.ruleId) {
          md += `  - Rule: ${issue.ruleId}\n`;
        }
      }
    }

    return {
      content: [{ type: 'text', text: md } as TextContent],
    };
  }

  // Summary format
  const summary = {
    sessionId: activeSession.id,
    duration: `${Math.round((Date.now() - activeSession.startTime.getTime()) / 1000)}s`,
    totalIssues: filteredIssues.length,
    byType: {
      errors: filteredIssues.filter((i) => i.severity === 'error').length,
      warnings: filteredIssues.filter((i) => i.severity === 'warning').length,
      info: filteredIssues.filter((i) => i.severity === 'info').length,
    },
    topFiles: getTopFiles(filteredIssues),
  };

  return {
    content: [{ type: 'text', text: JSON.stringify(summary, null, 2) } as TextContent],
  };
}

/**
 * Get top files by issue count
 */
function getTopFiles(issues: Array<{ file: string }>): Array<{ file: string; count: number }> {
  const counts = new Map<string, number>();
  for (const issue of issues) {
    if (issue.file) {
      counts.set(issue.file, (counts.get(issue.file) ?? 0) + 1);
    }
  }
  return Array.from(counts.entries())
    .map(([file, count]) => ({ file, count }))
    .sort((a, b) => b.count - a.count)
    .slice(0, 5);
}

/**
 * Get default extensions for tasks
 */
function getDefaultExtensions(tasks: string[]): string[] {
  const extensions = new Set<string>();

  if (tasks.includes('lint') || tasks.includes('test')) {
    ['.ts', '.tsx', '.js', '.jsx', '.mjs', '.cjs'].forEach((e) => extensions.add(e));
  }
  if (tasks.includes('ears')) {
    extensions.add('.md');
  }
  if (tasks.includes('security')) {
    ['.ts', '.js', '.py', '.rb', '.rs', '.go', '.c'].forEach((e) => extensions.add(e));
  }

  return Array.from(extensions);
}

/**
 * All watch tools
 */
export const watchTools: Tool[] = [
  watchStartTool,
  watchStopTool,
  watchStatusTool,
  watchRunNowTool,
  watchReportTool,
];

/**
 * Get watch tools
 */
export function getWatchTools(): Tool[] {
  return watchTools;
}

/**
 * Handle watch tool calls
 */
export async function handleWatchTool(
  name: string,
  args: Record<string, unknown>
): Promise<CallToolResult> {
  switch (name) {
    case 'watch_start':
      return handleWatchStart(args as Parameters<typeof handleWatchStart>[0]);
    case 'watch_stop':
      return handleWatchStop(args as Parameters<typeof handleWatchStop>[0]);
    case 'watch_status':
      return handleWatchStatus();
    case 'watch_run_now':
      return handleWatchRunNow(args as Parameters<typeof handleWatchRunNow>[0]);
    case 'watch_report':
      return handleWatchReport(args as Parameters<typeof handleWatchReport>[0]);
    default:
      return {
        content: [{ type: 'text', text: `Unknown watch tool: ${name}` } as TextContent],
        isError: true,
      };
  }
}
