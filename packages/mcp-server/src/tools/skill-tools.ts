/**
 * Skill MCP Tools
 * 
 * MCP tools for skill management
 * 
 * @see TSK-MCP-003 - skill_* MCP Tools
 * @see REQ-MCP-001 - MCP Tool Naming Convention
 * @see DES-MCP-003 - Skill Tools
 */

import { z } from 'zod';
import type { ToolDefinition, ToolResult } from '../types.js';
import {
  handleSkillList,
  handleSkillExecute,
  handleSkillValidate,
  handleSkillInfo,
  handleSkillRegister,
} from './skill-handlers.js';

/**
 * Input schemas for validation (defined first for use in handlers)
 */
export const SkillListInputSchema = z.object({
  type: z.enum([
    'file-operation',
    'code-analysis',
    'code-generation',
    'requirements',
    'design',
    'testing',
    'knowledge-graph',
    'orchestration',
    'security',
    'documentation',
    'custom',
  ]).optional(),
  tags: z.array(z.string()).optional(),
  enabledOnly: z.boolean().optional().default(true),
  query: z.string().optional(),
});

export const SkillExecuteInputSchema = z.object({
  skillId: z.string().min(1, 'Skill ID is required'),
  parameters: z.record(z.unknown()).optional().default({}),
  context: z.object({
    workflowId: z.string().optional(),
    phaseType: z.string().optional(),
    taskId: z.string().optional(),
  }).optional(),
});

export const SkillValidateInputSchema = z.object({
  skillId: z.string().optional(),
  definition: z.object({
    id: z.string(),
    name: z.string(),
    description: z.string(),
    type: z.string(),
    parameters: z.array(z.object({
      name: z.string(),
      type: z.enum(['string', 'number', 'boolean', 'array', 'object']),
      required: z.boolean().optional(),
      description: z.string(),
    })).optional(),
  }).optional(),
}).refine(
  data => data.skillId || data.definition,
  { message: 'Either skillId or definition is required' }
);

export const SkillInfoInputSchema = z.object({
  skillId: z.string().min(1, 'Skill ID is required'),
});

export const SkillRegisterInputSchema = z.object({
  id: z.string().min(1, 'Skill ID is required'),
  name: z.string().min(1, 'Skill name is required'),
  description: z.string().min(1, 'Skill description is required'),
  type: z.enum([
    'file-operation',
    'code-analysis',
    'code-generation',
    'requirements',
    'design',
    'testing',
    'knowledge-graph',
    'orchestration',
    'security',
    'documentation',
    'custom',
  ]),
  parameters: z.array(z.object({
    name: z.string(),
    type: z.enum(['string', 'number', 'boolean', 'array', 'object']),
    required: z.boolean().optional(),
    description: z.string(),
    default: z.unknown().optional(),
  })).optional(),
  tags: z.array(z.string()).optional(),
});

/**
 * Input types
 */
export type SkillListInput = z.infer<typeof SkillListInputSchema>;
export type SkillExecuteInput = z.infer<typeof SkillExecuteInputSchema>;
export type SkillValidateInput = z.infer<typeof SkillValidateInputSchema>;
export type SkillInfoInput = z.infer<typeof SkillInfoInputSchema>;
export type SkillRegisterInput = z.infer<typeof SkillRegisterInputSchema>;

/**
 * skill_list tool definition
 */
export const skillListTool: ToolDefinition = {
  name: 'skill_list',
  description: `利用可能なスキルの一覧を取得します。
  
スキルタイプやタグでフィルタリングできます。

利用可能なスキルタイプ:
- file-operation: ファイル操作
- code-analysis: コード分析
- code-generation: コード生成
- requirements: 要件分析 (EARS)
- design: 設計 (C4)
- testing: テスト
- knowledge-graph: 知識グラフ
- orchestration: エージェントオーケストレーション
- security: セキュリティ
- documentation: ドキュメント
- custom: カスタムスキル`,
  inputSchema: {
    type: 'object',
    properties: {
      type: {
        type: 'string',
        enum: [
          'file-operation',
          'code-analysis',
          'code-generation',
          'requirements',
          'design',
          'testing',
          'knowledge-graph',
          'orchestration',
          'security',
          'documentation',
          'custom',
        ],
        description: 'スキルタイプでフィルタ',
      },
      tags: {
        type: 'array',
        items: { type: 'string' },
        description: 'タグでフィルタ（AND条件）',
      },
      enabledOnly: {
        type: 'boolean',
        description: '有効なスキルのみ表示（デフォルト: true）',
      },
      query: {
        type: 'string',
        description: '名前・説明でのテキスト検索',
      },
    },
    required: [],
  },
  handler: async (args: Record<string, unknown>): Promise<ToolResult> => {
    const input = SkillListInputSchema.parse(args);
    return handleSkillList(input);
  },
};

/**
 * skill_execute tool definition
 */
export const skillExecuteTool: ToolDefinition = {
  name: 'skill_execute',
  description: `指定したスキルを実行します。
  
スキルのパラメータを指定して実行し、結果を返します。`,
  inputSchema: {
    type: 'object',
    properties: {
      skillId: {
        type: 'string',
        description: 'スキルID',
      },
      parameters: {
        type: 'object',
        description: 'スキルパラメータ',
        additionalProperties: true,
      },
      context: {
        type: 'object',
        description: '実行コンテキスト',
        properties: {
          workflowId: { type: 'string' },
          phaseType: { type: 'string' },
          taskId: { type: 'string' },
        },
      },
    },
    required: ['skillId'],
  },
  handler: async (args: Record<string, unknown>): Promise<ToolResult> => {
    const input = SkillExecuteInputSchema.parse(args);
    return handleSkillExecute(input);
  },
};

/**
 * skill_validate tool definition
 */
export const skillValidateTool: ToolDefinition = {
  name: 'skill_validate',
  description: `スキル定義を検証します。
  
メタデータの完全性、パラメータ定義の妥当性をチェックします。`,
  inputSchema: {
    type: 'object',
    properties: {
      skillId: {
        type: 'string',
        description: 'スキルID（既存スキルの検証）',
      },
      definition: {
        type: 'object',
        description: 'スキル定義（新規スキルの検証）',
        properties: {
          id: { type: 'string' },
          name: { type: 'string' },
          description: { type: 'string' },
          type: { type: 'string' },
          parameters: { type: 'array' },
        },
      },
    },
    required: [],
  },
  handler: async (args: Record<string, unknown>): Promise<ToolResult> => {
    const input = SkillValidateInputSchema.parse(args);
    return handleSkillValidate(input);
  },
};

/**
 * skill_info tool definition
 */
export const skillInfoTool: ToolDefinition = {
  name: 'skill_info',
  description: `スキルの詳細情報を取得します。
  
パラメータ定義、タグ、使用例などの詳細を表示します。`,
  inputSchema: {
    type: 'object',
    properties: {
      skillId: {
        type: 'string',
        description: 'スキルID',
      },
    },
    required: ['skillId'],
  },
  handler: async (args: Record<string, unknown>): Promise<ToolResult> => {
    const input = SkillInfoInputSchema.parse(args);
    return handleSkillInfo(input);
  },
};

/**
 * skill_register tool definition
 */
export const skillRegisterTool: ToolDefinition = {
  name: 'skill_register',
  description: `新しいスキルを登録します。
  
カスタムスキルを登録して利用可能にします。`,
  inputSchema: {
    type: 'object',
    properties: {
      id: {
        type: 'string',
        description: 'スキルID（一意）',
      },
      name: {
        type: 'string',
        description: 'スキル名',
      },
      description: {
        type: 'string',
        description: 'スキルの説明',
      },
      type: {
        type: 'string',
        enum: [
          'file-operation',
          'code-analysis',
          'code-generation',
          'requirements',
          'design',
          'testing',
          'knowledge-graph',
          'orchestration',
          'security',
          'documentation',
          'custom',
        ],
        description: 'スキルタイプ',
      },
      parameters: {
        type: 'array',
        items: {
          type: 'object',
          properties: {
            name: { type: 'string' },
            type: { type: 'string', enum: ['string', 'number', 'boolean', 'array', 'object'] },
            required: { type: 'boolean' },
            description: { type: 'string' },
          },
        },
        description: 'パラメータ定義',
      },
      tags: {
        type: 'array',
        items: { type: 'string' },
        description: 'タグ',
      },
    },
    required: ['id', 'name', 'description', 'type'],
  },
  handler: async (args: Record<string, unknown>): Promise<ToolResult> => {
    const input = SkillRegisterInputSchema.parse(args);
    return handleSkillRegister(input);
  },
};

/**
 * All skill tools
 */
export const skillTools: ToolDefinition[] = [
  skillListTool,
  skillExecuteTool,
  skillValidateTool,
  skillInfoTool,
  skillRegisterTool,
];
