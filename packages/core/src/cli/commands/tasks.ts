/**
 * Tasks Command
 *
 * CLI commands for task management and validation with YATA Local integration
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
import {
  AutoLearnMiddleware,
  isAutoLearnEnabled,
  type YataEntityInput,
  type YataRelationshipInput,
} from '../middleware/auto-learn.js';

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
  yataLocalRegistered?: number;
  message: string;
}

/**
 * Task information
 */
export interface TaskInfo {
  id: string;
  name: string;
  priority: string;
  estimate: string;
  requirements?: string[];
  design?: string;
  status: 'valid' | 'warning' | 'error';
}

/**
 * Register tasks command
 */
export function registerTasksCommand(program: Command): void {
  const tasks = program
    .command('tasks')
    .description('Task management and validation');

  // tasks validate
  tasks
    .command('validate <file>')
    .description('Validate task document and optionally register to YATA Local')
    .option('--auto-learn', 'Auto-register to YATA Local', false)
    .option('--db <path>', 'YATA Local database path', './.yata-local.db')
    .option('--strict', 'Enable strict validation', false)
    .action(async (file: string, options: { autoLearn?: boolean; db?: string; strict?: boolean }) => {
      const globalOpts = getGlobalOptions(program);
      const autoLearn = isAutoLearnEnabled(options);

      try {
        const filePath = resolve(process.cwd(), file);
        const content = await readFile(filePath, 'utf-8');

        // Parse and validate tasks
        const { tasks: parsedTasks, issues } = parseTaskDocument(content, options.strict ?? false);

        // Auto-register to YATA Local if enabled
        let yataLocalRegistered = 0;
        const errorCount = issues.filter(i => i.severity === 'error').length;

        if (autoLearn && errorCount === 0) {
          const middleware = new AutoLearnMiddleware(options);
          const initialized = await middleware.init();

          if (initialized) {
            // Extract document ID
            const docIdMatch = content.match(/\*\*Document ID\*\*:\s*([\w-]+)/);
            const docId = docIdMatch ? docIdMatch[1] : 'TSK-UNKNOWN';

            // Prepare entities and relationships
            const entities: YataEntityInput[] = [];
            const relationships: YataRelationshipInput[] = [];

            // Add document entity
            entities.push({
              name: docId,
              type: 'module',
              namespace: 'tasks',
              filePath,
              metadata: {
                entityKind: 'TaskDocument',
                validatedAt: new Date().toISOString(),
                taskCount: parsedTasks.length,
              },
            });

            // Add task entities
            for (const task of parsedTasks) {
              entities.push({
                name: task.id,
                type: 'function',
                namespace: 'tasks',
                metadata: {
                  entityKind: 'Task',
                  displayName: task.name,
                  priority: task.priority,
                  estimate: task.estimate,
                  requirements: task.requirements,
                  design: task.design,
                  parentDocument: docId,
                },
              });

              relationships.push({
                sourceId: task.id,
                targetId: docId,
                type: 'contains',
                metadata: { relationKind: 'DEFINED_IN' },
              });
            }

            // Register batch
            const result = await middleware.registerBatch(entities, relationships);
            yataLocalRegistered = result.entityCount;

            await middleware.close();
          }
        }

        const result: TaskValidationResult = {
          success: true,
          valid: errorCount === 0,
          tasks: parsedTasks,
          issues,
          summary: {
            total: parsedTasks.length,
            valid: parsedTasks.filter(t => t.status === 'valid').length,
            errors: issues.filter(i => i.severity === 'error').length,
            warnings: issues.filter(i => i.severity === 'warning').length,
          },
          yataLocalRegistered: yataLocalRegistered > 0 ? yataLocalRegistered : undefined,
          message: errorCount === 0
            ? `✅ All ${parsedTasks.length} tasks are valid` +
              (yataLocalRegistered > 0 ? ` (${yataLocalRegistered} registered to YATA Local)` : '')
            : `❌ Found ${errorCount} errors in task document`,
        };

        outputResult(result, globalOpts);
        process.exit(errorCount === 0 ? ExitCode.SUCCESS : ExitCode.VALIDATION_ERROR);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Task validation failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // tasks list
  tasks
    .command('list [dir]')
    .description('List tasks from YATA Local')
    .option('--db <path>', 'YATA Local database path', './.yata-local.db')
    .option('--status <status>', 'Filter by status')
    .option('--priority <priority>', 'Filter by priority')
    .action(async (_dir: string | undefined, options: { db?: string; status?: string; priority?: string }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const middleware = new AutoLearnMiddleware(options);
        const initialized = await middleware.init();

        if (!initialized) {
          if (!globalOpts.quiet) {
            console.error('❌ YATA Local not available. Run with --auto-learn first to populate.');
          }
          process.exit(ExitCode.GENERAL_ERROR);
          return;
        }

        // Query tasks from YATA Local
        const yataLocalModule = await import('@nahisaho/yata-local');
        const { createYataLocal } = yataLocalModule;
        const yata = createYataLocal({ path: options.db ?? './.yata-local.db' });
        await yata.open();

        const tasks = await yata.getEntitiesByKind('Task');

        // Filter if needed
        let filteredTasks = tasks;
        if (options.priority) {
          filteredTasks = filteredTasks.filter(t => 
            (t.metadata as Record<string, unknown>)?.priority === options.priority
          );
        }

        const result = {
          success: true,
          tasks: filteredTasks.map(t => ({
            id: t.name,
            name: (t.metadata as Record<string, unknown>)?.displayName ?? t.name,
            priority: (t.metadata as Record<string, unknown>)?.priority ?? 'unknown',
            estimate: (t.metadata as Record<string, unknown>)?.estimate ?? 'unknown',
          })),
          total: filteredTasks.length,
        };

        await yata.close();
        outputResult(result, globalOpts);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Failed to list tasks: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // tasks stats
  tasks
    .command('stats')
    .description('Show task statistics from YATA Local')
    .option('--db <path>', 'YATA Local database path', './.yata-local.db')
    .action(async (options: { db?: string }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const yataLocalModule = await import('@nahisaho/yata-local');
        const { createYataLocal } = yataLocalModule;
        const yata = createYataLocal({ path: options.db ?? './.yata-local.db' });
        await yata.open();

        const tasks = await yata.getEntitiesByKind('Task');
        const docs = await yata.getEntitiesByKind('TaskDocument');

        // Calculate statistics
        const byPriority: Record<string, number> = {};
        for (const task of tasks) {
          const priority = String((task.metadata as Record<string, unknown>)?.priority ?? 'unknown');
          byPriority[priority] = (byPriority[priority] ?? 0) + 1;
        }

        const result = {
          success: true,
          documents: docs.length,
          tasks: tasks.length,
          byPriority,
        };

        await yata.close();
        outputResult(result, globalOpts);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Failed to get stats: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });
}

/**
 * Parse task document content
 */
function parseTaskDocument(
  content: string,
  strict: boolean
): { tasks: TaskInfo[]; issues: Array<{ taskId: string; severity: 'error' | 'warning' | 'info'; message: string }> } {
  const tasks: TaskInfo[] = [];
  const issues: Array<{ taskId: string; severity: 'error' | 'warning' | 'info'; message: string }> = [];

  // Parse task headers: ### TSK-PM-001: Task Name
  const taskPattern = /### (TSK-[\w-]+):\s*([^\n]+)\n([\s\S]*?)(?=###|$)/g;
  let match;

  while ((match = taskPattern.exec(content)) !== null) {
    const taskId = match[1];
    const taskName = match[2].trim();
    const taskBody = match[3];

    // Extract priority
    const priorityMatch = taskBody.match(/\*\*Priority\*\*:\s*(\w+)/);
    const priority = priorityMatch ? priorityMatch[1] : 'unknown';

    // Extract estimate
    const estimateMatch = taskBody.match(/\*\*Estimate\*\*:\s*([^\n]+)/);
    const estimate = estimateMatch ? estimateMatch[1].trim() : 'unknown';

    // Extract requirements
    const reqMatch = taskBody.match(/\*\*Requirements\*\*:\s*([^\n]+)/);
    const requirements = reqMatch
      ? reqMatch[1].split(/[,;]/).map(r => r.trim()).filter(Boolean)
      : undefined;

    // Extract design reference
    const designMatch = taskBody.match(/\*\*Design\*\*:\s*([\w-]+)/);
    const design = designMatch ? designMatch[1] : undefined;

    let status: 'valid' | 'warning' | 'error' = 'valid';

    // Validation
    if (!taskId.match(/^TSK-[\w-]+-\d{3}$/)) {
      issues.push({
        taskId,
        severity: strict ? 'error' : 'warning',
        message: 'Task ID should follow pattern TSK-XXX-NNN',
      });
      status = strict ? 'error' : 'warning';
    }

    if (priority === 'unknown') {
      issues.push({
        taskId,
        severity: 'warning',
        message: 'Missing priority (P0/P1/P2)',
      });
      if (status === 'valid') status = 'warning';
    }

    if (estimate === 'unknown') {
      issues.push({
        taskId,
        severity: 'info',
        message: 'Missing time estimate',
      });
    }

    if (!requirements || requirements.length === 0) {
      issues.push({
        taskId,
        severity: strict ? 'warning' : 'info',
        message: 'No requirements linked',
      });
    }

    tasks.push({
      id: taskId,
      name: taskName,
      priority,
      estimate,
      requirements,
      design,
      status,
    });
  }

  // Check for document-level issues
  if (tasks.length === 0) {
    issues.push({
      taskId: 'DOCUMENT',
      severity: 'error',
      message: 'No tasks found in document',
    });
  }

  return { tasks, issues };
}
