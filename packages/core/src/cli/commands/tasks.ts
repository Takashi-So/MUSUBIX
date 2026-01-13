/**
 * Tasks Command
 *
 * CLI commands for task management and validation
 *
 * @packageDocumentation
 * @module cli/commands/tasks
 *
 * @see REQ-CLI-003 - Tasks CLI
 * @see DES-MUSUBIX-001 Section 16-C.3 - tasksコマンド設計
 */

import type { Command } from 'commander';
import { readFile } from 'fs/promises';
import { resolve } from 'path';
import { ExitCode, getGlobalOptions, outputResult } from '../base.js';

/**
 * Task validation result
 */
export interface TaskValidationResult {
  success: boolean;
  valid: boolean;
  tasks: TaskInfo[];
  issues: Array<{
    taskId: string;
    severity: 'error' | 'warning' | 'info';
    message: string;
  }>;
  summary: {
    total: number;
    valid: number;
    errors: number;
    warnings: number;
  };
}

/**
 * Task information
 */
export interface TaskInfo {
  id: string;
  title: string;
  status: 'not-started' | 'in-progress' | 'completed' | 'blocked';
  priority: 'P0' | 'P1' | 'P2';
  estimate?: string;
  designRefs?: string[];
  dependencies?: string[];
}

/**
 * Register tasks command
 */
export function registerTasksCommand(program: Command): void {
  const tasks = program
    .command('tasks')
    .alias('task')
    .description('Task management commands');

  // tasks validate
  tasks
    .command('validate <file>')
    .description('Validate task document structure')
    .action(async (file: string) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const filePath = resolve(process.cwd(), file);
        const content = await readFile(filePath, 'utf-8');

        // Parse tasks from markdown
        const taskMatches = content.matchAll(/^##\s+TSK-(\d+):\s+(.+)$/gm);
        const tasks: TaskInfo[] = [];

        for (const match of taskMatches) {
          tasks.push({
            id: `TSK-${match[1]}`,
            title: match[2],
            status: 'not-started',
            priority: 'P1',
          });
        }

        const result: TaskValidationResult = {
          success: true,
          valid: true,
          tasks,
          issues: [],
          summary: {
            total: tasks.length,
            valid: tasks.length,
            errors: 0,
            warnings: 0,
          },
        };

        outputResult(result, globalOpts);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Failed to validate tasks: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // tasks list - file-based implementation
  tasks
    .command('list')
    .description('List tasks from task document')
    .option('-f, --file <path>', 'Task document file', 'storage/tasks/tasks.md')
    .action(async (options: { file: string }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const filePath = resolve(process.cwd(), options.file);
        const content = await readFile(filePath, 'utf-8');

        const taskMatches = content.matchAll(/^##\s+(TSK-\d+):\s+(.+)$/gm);
        const tasks: Array<{ id: string; title: string }> = [];

        for (const match of taskMatches) {
          tasks.push({
            id: match[1],
            title: match[2],
          });
        }

        const result = {
          success: true,
          tasks,
          total: tasks.length,
        };

        outputResult(result, globalOpts);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Failed to list tasks: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // tasks stats - simplified
  tasks
    .command('stats')
    .description('Show task statistics')
    .option('-f, --file <path>', 'Task document file', 'storage/tasks/tasks.md')
    .action(async (options: { file: string }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const filePath = resolve(process.cwd(), options.file);
        const content = await readFile(filePath, 'utf-8');

        const taskMatches = [...content.matchAll(/^##\s+TSK-\d+/gm)];
        const completedMatches = [...content.matchAll(/Status:\s*completed/gi)];

        const result = {
          success: true,
          stats: {
            total: taskMatches.length,
            completed: completedMatches.length,
            remaining: taskMatches.length - completedMatches.length,
          },
        };

        outputResult(result, globalOpts);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Failed to get task stats: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });
}
