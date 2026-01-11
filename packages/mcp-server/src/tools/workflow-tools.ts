/**
 * Workflow MCP Tools
 * 
 * MCP tools for workflow orchestration
 * 
 * @see TSK-MCP-002 - workflow_* MCP Tools
 * @see REQ-MCP-001 - MCP Tool Naming Convention
 * @see DES-MCP-002 - Workflow Tools
 */

import { z } from 'zod';
import type { ToolDefinition, ToolResult } from '../types.js';
import {
  handleWorkflowCreate,
  handleWorkflowTransition,
  handleWorkflowStatus,
  handleWorkflowReview,
  handleWorkflowGate,
} from './workflow-handlers.js';

/**
 * Input schemas for validation (defined first for use in handlers)
 */
export const WorkflowCreateInputSchema = z.object({
  name: z.string().min(1, 'Workflow name is required'),
  description: z.string().optional(),
  autoStart: z.boolean().optional().default(true),
});

export const WorkflowTransitionInputSchema = z.object({
  workflowId: z.string().min(1, 'Workflow ID is required'),
  targetPhase: z.enum(['design', 'task-breakdown', 'implementation', 'completion']),
  approval: z.string().optional(),
});

export const WorkflowStatusInputSchema = z.object({
  workflowId: z.string().min(1, 'Workflow ID is required'),
});

export const WorkflowReviewInputSchema = z.object({
  workflowId: z.string().min(1, 'Workflow ID is required'),
  checkpoints: z.array(z.object({
    name: z.string(),
    status: z.enum(['✅', '⚠️', '❌']),
    details: z.string(),
  })),
});

export const WorkflowGateInputSchema = z.object({
  workflowId: z.string().min(1, 'Workflow ID is required'),
  phase: z.enum(['requirements', 'design', 'task-breakdown', 'implementation', 'completion']),
});

/**
 * Input types
 */
export type WorkflowCreateInput = z.infer<typeof WorkflowCreateInputSchema>;
export type WorkflowTransitionInput = z.infer<typeof WorkflowTransitionInputSchema>;
export type WorkflowStatusInput = z.infer<typeof WorkflowStatusInputSchema>;
export type WorkflowReviewInput = z.infer<typeof WorkflowReviewInputSchema>;
export type WorkflowGateInput = z.infer<typeof WorkflowGateInputSchema>;

/**
 * workflow_create tool definition
 */
export const workflowCreateTool: ToolDefinition = {
  name: 'workflow_create',
  description: `新しいワークフローを作成し、Phase 1（要件定義）を開始します。
  
SDDワークフローは以下の5フェーズで構成されます:
1. 要件定義 (EARS形式)
2. 設計 (C4モデル)
3. タスク分解 (必須 - スキップ禁止)
4. 実装 (Red-Green-Blue)
5. 完了 (ドキュメント更新)

⚠️ Phase 2からPhase 4への直接遷移は禁止されています。`,
  inputSchema: {
    type: 'object',
    properties: {
      name: {
        type: 'string',
        description: 'ワークフロー名',
      },
      description: {
        type: 'string',
        description: 'ワークフローの説明（任意）',
      },
      autoStart: {
        type: 'boolean',
        description: '作成後に自動的にPhase 1を開始するか（デフォルト: true）',
      },
    },
    required: ['name'],
  },
  handler: async (args: Record<string, unknown>): Promise<ToolResult> => {
    const input = WorkflowCreateInputSchema.parse(args);
    return handleWorkflowCreate(input);
  },
};

/**
 * workflow_transition tool definition
 */
export const workflowTransitionTool: ToolDefinition = {
  name: 'workflow_transition',
  description: `ワークフローを次のフェーズに遷移します。
  
現在のフェーズが承認された後にのみ遷移可能です。
ユーザーからの承認キーワード（承認, OK, LGTM, 進める）が必要です。

⚠️ Phase 2 (設計) から Phase 4 (実装) への直接遷移は禁止されています。
必ず Phase 3 (タスク分解) を経る必要があります。`,
  inputSchema: {
    type: 'object',
    properties: {
      workflowId: {
        type: 'string',
        description: 'ワークフローID',
      },
      targetPhase: {
        type: 'string',
        enum: ['design', 'task-breakdown', 'implementation', 'completion'],
        description: '遷移先のフェーズ',
      },
      approval: {
        type: 'string',
        description: 'ユーザーからの承認テキスト',
      },
    },
    required: ['workflowId', 'targetPhase'],
  },
  handler: async (args: Record<string, unknown>): Promise<ToolResult> => {
    const input = WorkflowTransitionInputSchema.parse(args);
    return handleWorkflowTransition(input);
  },
};

/**
 * workflow_status tool definition
 */
export const workflowStatusTool: ToolDefinition = {
  name: 'workflow_status',
  description: `ワークフローの現在の状態を取得します。
  
各フェーズの状態、進捗率、アーティファクト情報を含みます。`,
  inputSchema: {
    type: 'object',
    properties: {
      workflowId: {
        type: 'string',
        description: 'ワークフローID',
      },
    },
    required: ['workflowId'],
  },
  handler: async (args: Record<string, unknown>): Promise<ToolResult> => {
    const input = WorkflowStatusInputSchema.parse(args);
    return handleWorkflowStatus(input);
  },
};

/**
 * workflow_review tool definition
 */
export const workflowReviewTool: ToolDefinition = {
  name: 'workflow_review',
  description: `現在のフェーズのセルフレビューを実行し、結果を表示します。
  
レビュー完了後、ユーザーに承認/修正を求めます。`,
  inputSchema: {
    type: 'object',
    properties: {
      workflowId: {
        type: 'string',
        description: 'ワークフローID',
      },
      checkpoints: {
        type: 'array',
        items: {
          type: 'object',
          properties: {
            name: { type: 'string', description: 'チェック項目名' },
            status: { type: 'string', enum: ['✅', '⚠️', '❌'], description: 'ステータス' },
            details: { type: 'string', description: '詳細' },
          },
        },
        description: 'レビューチェックポイント',
      },
    },
    required: ['workflowId', 'checkpoints'],
  },
  handler: async (args: Record<string, unknown>): Promise<ToolResult> => {
    const input = WorkflowReviewInputSchema.parse(args);
    return handleWorkflowReview(input);
  },
};

/**
 * workflow_gate tool definition
 */
export const workflowGateTool: ToolDefinition = {
  name: 'workflow_gate',
  description: `フェーズのクオリティゲートを実行します。
  
フェーズごとに定義された品質チェックを実行し、結果を返します。`,
  inputSchema: {
    type: 'object',
    properties: {
      workflowId: {
        type: 'string',
        description: 'ワークフローID',
      },
      phase: {
        type: 'string',
        enum: ['requirements', 'design', 'task-breakdown', 'implementation', 'completion'],
        description: 'チェック対象のフェーズ',
      },
    },
    required: ['workflowId', 'phase'],
  },
  handler: async (args: Record<string, unknown>): Promise<ToolResult> => {
    const input = WorkflowGateInputSchema.parse(args);
    return handleWorkflowGate(input);
  },
};

/**
 * All workflow tools
 */
export const workflowTools: ToolDefinition[] = [
  workflowCreateTool,
  workflowTransitionTool,
  workflowStatusTool,
  workflowReviewTool,
  workflowGateTool,
];
