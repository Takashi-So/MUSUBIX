/**
 * Spaces MCP Tools - Copilot Spaces integration
 *
 * Implements: TSK-SPACES-005, REQ-SPACES-001〜006, DES-SPACES-004
 * MCP Tools: spaces_create, spaces_activate, spaces_list, spaces_status, spaces_suggest
 */

import { z } from 'zod';
import type { ToolDefinition, ToolResult } from '../types.js';

// Lazy import to avoid circular dependencies
let ContextManagerInstance: typeof import('@nahisaho/musubix-core').ContextManager | null = null;
let createContextManagerFn: typeof import('@nahisaho/musubix-core').createContextManager | null = null;

async function ensureImports() {
  if (!ContextManagerInstance || !createContextManagerFn) {
    const core = await import('@nahisaho/musubix-core');
    ContextManagerInstance = core.ContextManager;
    createContextManagerFn = core.createContextManager;
  }
}

// Schema definitions
const createSpaceSchema = z.object({
  name: z.string().describe('Space name'),
  description: z.string().optional().describe('Space description'),
  type: z.enum(['feature', 'bugfix', 'refactor', 'documentation', 'exploration', 'custom'])
    .describe('Space type'),
  requirements: z.array(z.string()).optional().describe('Related requirement IDs'),
  designs: z.array(z.string()).optional().describe('Related design IDs'),
  tasks: z.array(z.string()).optional().describe('Related task IDs'),
  files: z.array(z.string()).optional().describe('Initial files to include'),
  instructions: z.string().optional().describe('Custom instructions for this space'),
  workspacePath: z.string().optional().describe('Workspace path (default: cwd)'),
});

const activateSpaceSchema = z.object({
  spaceId: z.string().describe('Space ID to activate'),
  workspacePath: z.string().optional().describe('Workspace path'),
});

const listSpacesSchema = z.object({
  type: z.enum(['feature', 'bugfix', 'refactor', 'documentation', 'exploration', 'custom'])
    .optional().describe('Filter by type'),
  query: z.string().optional().describe('Search query'),
  workspacePath: z.string().optional().describe('Workspace path'),
});

const statusSchema = z.object({
  workspacePath: z.string().optional().describe('Workspace path'),
});

const suggestSchema = z.object({
  query: z.string().describe('Search query for file suggestions'),
  maxResults: z.number().optional().describe('Max results'),
  includeTests: z.boolean().optional().describe('Include test files'),
  workspacePath: z.string().optional().describe('Workspace path'),
});

// Cached context managers
const managers = new Map<string, any>();

async function getManager(workspacePath: string): Promise<any> {
  await ensureImports();
  const key = workspacePath;
  let manager = managers.get(key);

  if (!manager) {
    const storagePath = `${workspacePath}/.musubix`;
    manager = createContextManagerFn!({
      workspacePath,
      storagePath,
      autoActivate: true,
    });
    managers.set(key, manager);
  }

  return manager;
}

// Tool implementations
async function spacesCreate(
  args: z.infer<typeof createSpaceSchema>
): Promise<string> {
  const workspacePath = args.workspacePath ?? process.cwd();
  const manager = await getManager(workspacePath);
  await manager.init();

  const space = await manager.createSpace({
    name: args.name,
    description: args.description,
    type: args.type,
    context: {
      requirements: args.requirements ?? [],
      designs: args.designs ?? [],
      tasks: args.tasks ?? [],
      includedFiles: args.files ?? [],
      instructions: args.instructions,
    },
  });

  // Activate the new space
  await manager.activate(space.id);

  let output = `✅ Space「${space.name}」を作成しました！\n\n`;
  output += `**ID:** ${space.id}\n`;
  output += `**タイプ:** ${getTypeEmoji(space.type)} ${space.type}\n\n`;

  if (args.requirements?.length) {
    output += `**要件:** ${args.requirements.join(', ')}\n`;
  }
  if (args.designs?.length) {
    output += `**設計:** ${args.designs.join(', ')}\n`;
  }
  if (args.tasks?.length) {
    output += `**タスク:** ${args.tasks.join(', ')}\n`;
  }
  if (args.files?.length) {
    output += `**ファイル:** ${args.files.length}件\n`;
  }

  output += '\n💡 このスペースがアクティブになりました。';
  output += '\n   関連ファイルやコンテキストが自動的に読み込まれます。';

  return output;
}

async function spacesActivate(
  args: z.infer<typeof activateSpaceSchema>
): Promise<string> {
  const workspacePath = args.workspacePath ?? process.cwd();
  const manager = await getManager(workspacePath);
  await manager.init();

  const result = await manager.activate(args.spaceId);

  if (!result.success) {
    return `❌ スペースのアクティベートに失敗しました: ${result.error}`;
  }

  const space = result.space!;
  let output = `✅ Space「${space.name}」をアクティベートしました！\n\n`;
  output += `**タイプ:** ${getTypeEmoji(space.type)} ${space.type}\n`;

  if (result.loadedFiles && result.loadedFiles.length > 0) {
    output += `\n**読み込まれたファイル:** ${result.loadedFiles.length}件\n`;
    for (const file of result.loadedFiles.slice(0, 5)) {
      output += `- ${file}\n`;
    }
    if (result.loadedFiles.length > 5) {
      output += `- ...他${result.loadedFiles.length - 5}件\n`;
    }
  }

  if (space.context.requirements.length > 0) {
    output += `\n**関連要件:** ${space.context.requirements.join(', ')}\n`;
  }

  if (space.context.instructions) {
    output += `\n**カスタム指示:**\n${space.context.instructions}\n`;
  }

  return output;
}

async function spacesList(
  args: z.infer<typeof listSpacesSchema>
): Promise<string> {
  const workspacePath = args.workspacePath ?? process.cwd();
  const manager = await getManager(workspacePath);
  await manager.init();

  let spaces;

  if (args.query) {
    spaces = await manager.searchSpaces(args.query);
  } else {
    spaces = await manager.listSpaces();
    if (args.type) {
      spaces = spaces.filter((s: any) => s.type === args.type);
    }
  }

  if (spaces.length === 0) {
    return '📭 スペースがありません。\n\n' +
           '`spaces_create` を使用して新しいスペースを作成してください。';
  }

  const activeSpace = manager.getActiveSpace();

  let output = `# 📂 Spaces一覧 (${spaces.length}件)\n\n`;

  for (const space of spaces) {
    const isActive = activeSpace?.id === space.id;
    const activeMarker = isActive ? ' 🟢 アクティブ' : '';

    output += `## ${getTypeEmoji(space.type)} ${space.name}${activeMarker}\n\n`;
    output += `**ID:** ${space.id}\n`;
    output += `**タイプ:** ${space.type}\n`;
    output += `**更新日:** ${new Date(space.updatedAt).toLocaleDateString('ja-JP')}\n`;

    if (space.description) {
      output += `\n${space.description}\n`;
    }

    const reqCount = space.context.requirements.length;
    const taskCount = space.context.tasks.length;
    const fileCount = space.context.includedFiles.length;

    if (reqCount || taskCount || fileCount) {
      output += '\n📊 ';
      if (reqCount) output += `要件: ${reqCount} `;
      if (taskCount) output += `タスク: ${taskCount} `;
      if (fileCount) output += `ファイル: ${fileCount}`;
      output += '\n';
    }

    output += '\n---\n\n';
  }

  return output;
}

async function spacesStatus(
  args: z.infer<typeof statusSchema>
): Promise<string> {
  const workspacePath = args.workspacePath ?? process.cwd();
  const manager = await getManager(workspacePath);
  await manager.init();

  const stats = await manager.getStats();
  const activeSpace = manager.getActiveSpace();

  let output = '# 📊 Spaces ステータス\n\n';

  // Active space
  if (activeSpace) {
    output += `## 🟢 アクティブスペース\n\n`;
    output += `**${activeSpace.name}** (${getTypeEmoji(activeSpace.type)} ${activeSpace.type})\n\n`;

    if (activeSpace.context.instructions) {
      output += '**カスタム指示:**\n';
      output += `> ${activeSpace.context.instructions.slice(0, 200)}${activeSpace.context.instructions.length > 200 ? '...' : ''}\n\n`;
    }

    const contextFiles = await manager.getContextFiles();
    output += `**コンテキストファイル:** ${contextFiles.length}件\n`;

    if (activeSpace.context.requirements.length > 0) {
      output += `**要件:** ${activeSpace.context.requirements.join(', ')}\n`;
    }
  } else {
    output += `## ⚪ アクティブスペースなし\n\n`;
    output += '`spaces_activate` でスペースをアクティベートしてください。\n\n';
  }

  // Statistics
  output += `## 📈 統計\n\n`;
  output += `- **合計スペース:** ${stats.totalSpaces}件\n`;
  output += `- **合計ファイル:** ${stats.totalFiles}件\n`;
  output += `- **追跡中の要件:** ${stats.totalRequirements}件\n\n`;

  output += '### タイプ別\n';
  for (const [type, count] of Object.entries(stats.byType)) {
    const countNum = count as number;
    if (countNum > 0) {
      output += `- ${getTypeEmoji(type as any)} ${type}: ${countNum}件\n`;
    }
  }

  // Recent spaces
  if (stats.recentSpaces.length > 0) {
    output += '\n### 最近のスペース\n';
    for (const recent of stats.recentSpaces) {
      const isActive = activeSpace?.id === recent.id;
      output += `- ${recent.name}${isActive ? ' 🟢' : ''} (${new Date(recent.lastUsed).toLocaleDateString('ja-JP')})\n`;
    }
  }

  return output;
}

async function spacesSuggest(
  args: z.infer<typeof suggestSchema>
): Promise<string> {
  const workspacePath = args.workspacePath ?? process.cwd();
  const manager = await getManager(workspacePath);
  await manager.init();

  const suggestions = await manager.suggestFiles({
    query: args.query,
    maxResults: args.maxResults ?? 20,
    includeTests: args.includeTests ?? false,
  });

  if (suggestions.length === 0) {
    return '📭 該当するファイルが見つかりませんでした。';
  }

  let output = `# 🔍 ファイル候補 (「${args.query}」)\n\n`;
  output += `${suggestions.length}件の候補が見つかりました。\n\n`;

  for (const suggestion of suggestions) {
    const relevanceBar = '█'.repeat(Math.round(suggestion.relevance * 10)) +
                        '░'.repeat(10 - Math.round(suggestion.relevance * 10));
    output += `## ${suggestion.value}\n`;
    output += `**関連度:** ${relevanceBar} ${Math.round(suggestion.relevance * 100)}%\n`;
    output += `**理由:** ${suggestion.reason}\n\n`;
  }

  output += '\n💡 ファイルをスペースに追加するには、`spaces_add_file` を使用してください。';

  return output;
}

// Helper functions
function getTypeEmoji(type: string): string {
  switch (type) {
    case 'feature': return '✨';
    case 'bugfix': return '🐛';
    case 'refactor': return '♻️';
    case 'documentation': return '📚';
    case 'exploration': return '🔬';
    case 'custom': return '🎯';
    default: return '📂';
  }
}

// Tool definitions
export const spacesCreateTool: ToolDefinition = {
  name: 'spaces_create',
  description: '新しいCopilot Spaceを作成します。要件、設計、タスク、ファイルを関連付けて、コンテキストを管理できます。',
  inputSchema: createSpaceSchema.shape as unknown as Record<string, unknown>,
  handler: async (args): Promise<ToolResult> => {
    const result = await spacesCreate(args as z.infer<typeof createSpaceSchema>);
    return { content: [{ type: 'text', text: result }] };
  },
};

export const spacesActivateTool: ToolDefinition = {
  name: 'spaces_activate',
  description: 'スペースをアクティベートし、関連ファイルとコンテキストを読み込みます。',
  inputSchema: activateSpaceSchema.shape as unknown as Record<string, unknown>,
  handler: async (args): Promise<ToolResult> => {
    const result = await spacesActivate(args as z.infer<typeof activateSpaceSchema>);
    return { content: [{ type: 'text', text: result }] };
  },
};

export const spacesListTool: ToolDefinition = {
  name: 'spaces_list',
  description: '全てのスペースを一覧表示します。タイプやキーワードでフィルタリングできます。',
  inputSchema: listSpacesSchema.shape as unknown as Record<string, unknown>,
  handler: async (args): Promise<ToolResult> => {
    const result = await spacesList(args as z.infer<typeof listSpacesSchema>);
    return { content: [{ type: 'text', text: result }] };
  },
};

export const spacesStatusTool: ToolDefinition = {
  name: 'spaces_status',
  description: '現在のスペースのステータス（アクティブスペース、統計情報）を表示します。',
  inputSchema: statusSchema.shape as unknown as Record<string, unknown>,
  handler: async (args): Promise<ToolResult> => {
    const result = await spacesStatus(args as z.infer<typeof statusSchema>);
    return { content: [{ type: 'text', text: result }] };
  },
};

export const spacesSuggestTool: ToolDefinition = {
  name: 'spaces_suggest',
  description: 'クエリに基づいてコンテキストに追加すべきファイルを提案します。',
  inputSchema: suggestSchema.shape as unknown as Record<string, unknown>,
  handler: async (args): Promise<ToolResult> => {
    const result = await spacesSuggest(args as z.infer<typeof suggestSchema>);
    return { content: [{ type: 'text', text: result }] };
  },
};

// Export all tools
export const spacesTools: ToolDefinition[] = [
  spacesCreateTool,
  spacesActivateTool,
  spacesListTool,
  spacesStatusTool,
  spacesSuggestTool,
];
