/**
 * Agent MCP Tools
 * 
 * MCP tools for agent orchestration
 * 
 * @see TSK-MCP-001 - agent_* MCP Tools
 * @see REQ-MCP-001 - MCP Tool Naming Convention
 * @see DES-MCP-001 - Agent Tools
 */

import { z } from 'zod';
import type { ToolDefinition, ToolResult } from '../types.js';
import {
  handleAgentDispatch,
  handleAgentStatus,
  handleAgentCancel,
  handleAgentAnalyze,
} from './agent-handlers.js';

/**
 * agent_dispatch tool definition
 */
export const agentDispatchTool: ToolDefinition = {
  name: 'agent_dispatch',
  description: `サブエージェントをディスパッチして複雑なタスクを実行します。
  
タスクの複雑度を分析し、必要に応じてサブエージェントに分解して並列実行します。
YATAコンテキストストアとの統合により、実行中のコンテキスト共有を行います。

使用例:
- 大規模なリファクタリングタスクの分割実行
- 複数ファイルへの変更の並列処理
- 依存関係のあるタスクの順序付き実行`,
  inputSchema: {
    type: 'object',
    properties: {
      taskDescription: {
        type: 'string',
        description: 'タスクの説明（詳細であるほど良い分析が可能）',
      },
      context: {
        type: 'object',
        description: 'タスク実行のコンテキスト情報',
        properties: {
          workflowId: {
            type: 'string',
            description: 'ワークフローID（任意）',
          },
          phaseType: {
            type: 'string',
            description: '現在のフェーズ（requirements, design, task-breakdown, implementation, completion）',
          },
          files: {
            type: 'array',
            items: { type: 'string' },
            description: '関連ファイルパス',
          },
        },
      },
      options: {
        type: 'object',
        description: 'ディスパッチオプション',
        properties: {
          maxParallelism: {
            type: 'number',
            description: '最大並列実行数（デフォルト: 5）',
          },
          timeout: {
            type: 'number',
            description: 'タイムアウト（ミリ秒）',
          },
          decompose: {
            type: 'boolean',
            description: '自動タスク分解を有効にするか（デフォルト: true）',
          },
        },
      },
    },
    required: ['taskDescription'],
  },
  handler: async (args: Record<string, unknown>): Promise<ToolResult> => {
    const input = AgentDispatchInputSchema.parse(args);
    return handleAgentDispatch(input);
  },
};

/**
 * agent_status tool definition
 */
export const agentStatusTool: ToolDefinition = {
  name: 'agent_status',
  description: `ディスパッチされたエージェントの状態を取得します。
  
実行中のサブエージェントの進捗、完了状況、エラー情報を提供します。`,
  inputSchema: {
    type: 'object',
    properties: {
      executionId: {
        type: 'string',
        description: '実行ID（agent_dispatchの戻り値）',
      },
      includeDetails: {
        type: 'boolean',
        description: '詳細情報を含めるか（デフォルト: false）',
      },
    },
    required: ['executionId'],
  },
  handler: async (args: Record<string, unknown>): Promise<ToolResult> => {
    const input = AgentStatusInputSchema.parse(args);
    return handleAgentStatus(input);
  },
};

/**
 * agent_cancel tool definition
 */
export const agentCancelTool: ToolDefinition = {
  name: 'agent_cancel',
  description: `実行中のエージェントタスクをキャンセルします。
  
まだ開始されていないサブタスクはスキップされ、実行中のタスクは可能な限り中断されます。`,
  inputSchema: {
    type: 'object',
    properties: {
      executionId: {
        type: 'string',
        description: '実行ID',
      },
      reason: {
        type: 'string',
        description: 'キャンセル理由（任意）',
      },
    },
    required: ['executionId'],
  },
  handler: async (args: Record<string, unknown>): Promise<ToolResult> => {
    const input = AgentCancelInputSchema.parse(args);
    return handleAgentCancel(input);
  },
};

/**
 * agent_analyze tool definition
 */
export const agentAnalyzeTool: ToolDefinition = {
  name: 'agent_analyze',
  description: `タスクの複雑度を分析し、サブエージェント分解の推奨を提供します。
  
5つの因子（スコープ、依存関係、ファイル数、テストカバレッジ、不確実性）で分析し、
分解が必要かどうかを判定します。`,
  inputSchema: {
    type: 'object',
    properties: {
      taskDescription: {
        type: 'string',
        description: 'タスクの説明',
      },
      context: {
        type: 'object',
        description: 'コンテキスト情報',
        properties: {
          files: {
            type: 'array',
            items: { type: 'string' },
            description: '関連ファイルパス',
          },
          existingTests: {
            type: 'boolean',
            description: '既存テストがあるか',
          },
        },
      },
    },
    required: ['taskDescription'],
  },
  handler: async (args: Record<string, unknown>): Promise<ToolResult> => {
    const input = AgentAnalyzeInputSchema.parse(args);
    return handleAgentAnalyze(input);
  },
};

/**
 * All agent tools
 */
export const agentTools: ToolDefinition[] = [
  agentDispatchTool,
  agentStatusTool,
  agentCancelTool,
  agentAnalyzeTool,
];

/**
 * Input schemas for validation
 */
export const AgentDispatchInputSchema = z.object({
  taskDescription: z.string().min(1, 'Task description is required'),
  context: z.object({
    workflowId: z.string().optional(),
    phaseType: z.enum([
      'requirements',
      'design',
      'task-breakdown',
      'implementation',
      'completion',
    ]).optional(),
    files: z.array(z.string()).optional(),
  }).optional(),
  options: z.object({
    maxParallelism: z.number().min(1).max(10).optional(),
    timeout: z.number().min(1000).optional(),
    decompose: z.boolean().optional(),
  }).optional(),
});

export const AgentStatusInputSchema = z.object({
  executionId: z.string().min(1, 'Execution ID is required'),
  includeDetails: z.boolean().optional(),
});

export const AgentCancelInputSchema = z.object({
  executionId: z.string().min(1, 'Execution ID is required'),
  reason: z.string().optional(),
});

export const AgentAnalyzeInputSchema = z.object({
  taskDescription: z.string().min(1, 'Task description is required'),
  context: z.object({
    files: z.array(z.string()).optional(),
    existingTests: z.boolean().optional(),
  }).optional(),
});

/**
 * Input types
 */
export type AgentDispatchInput = z.infer<typeof AgentDispatchInputSchema>;
export type AgentStatusInput = z.infer<typeof AgentStatusInputSchema>;
export type AgentCancelInput = z.infer<typeof AgentCancelInputSchema>;
export type AgentAnalyzeInput = z.infer<typeof AgentAnalyzeInputSchema>;
