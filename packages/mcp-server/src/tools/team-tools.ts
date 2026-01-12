/**
 * Team MCP Tools - Team sharing functionality
 *
 * Implements: TSK-TEAM-008, REQ-TEAM-001〜010, DES-TEAM-004
 * MCP Tools: team_share_pattern, team_list_patterns, team_sync,
 *            team_status, team_add_knowledge, team_query_knowledge
 */

import { z } from 'zod';
import type { ToolDefinition, ToolResult } from '../types.js';

// Lazy imports to avoid circular dependencies
let GitClientClass: any = null;
let createPatternSharerFn: any = null;
let createTeamKnowledgeFn: any = null;

async function ensureImports() {
  if (!GitClientClass || !createPatternSharerFn || !createTeamKnowledgeFn) {
    const core = await import('@nahisaho/musubix-core');
    GitClientClass = core.GitClient;
    createPatternSharerFn = core.createPatternSharer;
    createTeamKnowledgeFn = core.createTeamKnowledge;
  }
}

// Schema definitions
const sharePatternSchema = z.object({
  name: z.string().describe('Pattern name'),
  description: z.string().describe('Pattern description'),
  type: z.enum(['code', 'test', 'architecture', 'security']).describe('Pattern type'),
  content: z.string().describe('Pattern content (code or markdown)'),
  tags: z.array(z.string()).optional().describe('Tags for categorization'),
  applicableTo: z.array(z.string()).optional().describe('Languages or contexts where applicable'),
  memberName: z.string().describe('Name of the person sharing'),
  memberEmail: z.string().email().describe('Email of the person sharing'),
  repoPath: z.string().optional().describe('Repository path (default: cwd)'),
});

const listPatternsSchema = z.object({
  type: z.enum(['code', 'test', 'architecture', 'security']).optional().describe('Filter by type'),
  tags: z.array(z.string()).optional().describe('Filter by tags'),
  query: z.string().optional().describe('Search query'),
  repoPath: z.string().optional().describe('Repository path'),
});

const syncSchema = z.object({
  repoPath: z.string().optional().describe('Repository path'),
  autoPush: z.boolean().optional().describe('Push after sync'),
});

const statusSchema = z.object({
  repoPath: z.string().optional().describe('Repository path'),
});

const addKnowledgeSchema = z.object({
  title: z.string().describe('Knowledge entry title'),
  content: z.string().describe('Knowledge content'),
  type: z.enum(['decision', 'lesson-learned', 'best-practice', 'warning']).describe('Entry type'),
  category: z.string().describe('Category (e.g., architecture, security)'),
  tags: z.array(z.string()).optional().describe('Tags'),
  relatedEntities: z.array(z.string()).optional().describe('Related entity IDs'),
  memberName: z.string().describe('Contributor name'),
  memberEmail: z.string().email().describe('Contributor email'),
  repoPath: z.string().optional().describe('Repository path'),
});

const queryKnowledgeSchema = z.object({
  query: z.string().optional().describe('Search query'),
  type: z.string().optional().describe('Filter by type'),
  category: z.string().optional().describe('Filter by category'),
  tags: z.array(z.string()).optional().describe('Filter by tags'),
  limit: z.number().optional().describe('Max results'),
  repoPath: z.string().optional().describe('Repository path'),
});

// Helper functions
function getRepoPath(inputPath?: string): string {
  return inputPath ?? process.cwd();
}

async function createGitClient(repoPath: string): Promise<any> {
  await ensureImports();
  return new GitClientClass({
    repoPath,
    teamBranch: 'musubix-team',
  });
}

// Tool implementations
async function teamSharePattern(
  args: z.infer<typeof sharePatternSchema>
): Promise<string> {
  await ensureImports();
  const repoPath = getRepoPath(args.repoPath);
  const gitClient = await createGitClient(repoPath);

  // Ensure team branch
  await gitClient.ensureTeamBranch();

  const sharer = createPatternSharerFn({
    gitClient,
    autoCommit: true,
    autoPush: false,
  });

  const result = await sharer.sharePattern({
    name: args.name,
    description: args.description,
    type: args.type,
    content: args.content,
    tags: args.tags,
    applicableTo: args.applicableTo,
    sharedBy: {
      id: args.memberEmail,
      name: args.memberName,
      email: args.memberEmail,
      date: new Date(),
    },
  });

  if (result.success) {
    return `✅ パターン「${args.name}」を共有しました。\n\n` +
           `📁 ファイル: ${result.affectedFiles?.join(', ') ?? ''}\n` +
           `🔀 ブランチ: musubix-team\n\n` +
           `💡 チームと共有するには:\n` +
           `   git push origin musubix-team`;
  } else {
    return `❌ パターン共有に失敗しました: ${result.message}\n${result.error ?? ''}`;
  }
}

async function teamListPatterns(
  args: z.infer<typeof listPatternsSchema>
): Promise<string> {
  await ensureImports();
  const repoPath = getRepoPath(args.repoPath);
  const gitClient = await createGitClient(repoPath);
  const sharer = createPatternSharerFn({ gitClient });

  let patterns;

  if (args.query) {
    patterns = await sharer.searchPatterns(args.query, {
      type: args.type,
      tags: args.tags,
    });
  } else if (args.type || args.tags) {
    patterns = await sharer.searchPatterns('', {
      type: args.type,
      tags: args.tags,
    });
  } else {
    patterns = await sharer.listPatterns();
  }

  if (patterns.length === 0) {
    return '📭 共有パターンがありません。\n\n' +
           '`team_share_pattern` を使用してパターンを共有してください。';
  }

  let output = `# 📚 共有パターン一覧 (${patterns.length}件)\n\n`;

  for (const pattern of patterns) {
    output += `## ${pattern.name}\n\n`;
    output += `- **タイプ**: ${pattern.type}\n`;
    output += `- **共有者**: ${pattern.sharedBy.name}\n`;
    output += `- **日付**: ${new Date(pattern.sharedBy.date).toLocaleDateString('ja-JP')}\n`;
    if (pattern.tags && pattern.tags.length > 0) {
      output += `- **タグ**: ${pattern.tags.join(', ')}\n`;
    }
    output += `- **採用数**: ${pattern.adoptionCount ?? 0}\n`;
    if (pattern.rating) {
      output += `- **評価**: ${'⭐'.repeat(Math.round(pattern.rating))}\n`;
    }
    output += `\n${pattern.description}\n\n`;
    output += '---\n\n';
  }

  return output;
}

async function teamSync(
  args: z.infer<typeof syncSchema>
): Promise<string> {
  await ensureImports();
  const repoPath = getRepoPath(args.repoPath);
  const gitClient = await createGitClient(repoPath);

  // Ensure we're on team branch
  await gitClient.ensureTeamBranch();

  const patternSharer = createPatternSharerFn({
    gitClient,
    autoPush: args.autoPush ?? false,
  });
  const teamKnowledge = createTeamKnowledgeFn({
    gitClient,
    autoPush: args.autoPush ?? false,
  });

  // Sync both
  const patternStatus = await patternSharer.sync();
  const knowledgeStatus = await teamKnowledge.sync();

  let output = '# 🔄 同期結果\n\n';

  output += '## パターン\n';
  output += `- ステータス: ${getStatusEmoji(patternStatus.status)} ${patternStatus.status}\n`;
  output += `- 保留中の変更: ${patternStatus.pendingChanges}件\n`;
  if (patternStatus.lastSync) {
    output += `- 最終同期: ${patternStatus.lastSync.toLocaleString('ja-JP')}\n`;
  }
  if (patternStatus.error) {
    output += `- エラー: ${patternStatus.error}\n`;
  }

  output += '\n## ナレッジ\n';
  output += `- ステータス: ${getStatusEmoji(knowledgeStatus.status)} ${knowledgeStatus.status}\n`;
  output += `- 保留中の変更: ${knowledgeStatus.pendingChanges}件\n`;
  if (knowledgeStatus.lastSync) {
    output += `- 最終同期: ${knowledgeStatus.lastSync.toLocaleString('ja-JP')}\n`;
  }
  if (knowledgeStatus.error) {
    output += `- エラー: ${knowledgeStatus.error}\n`;
  }

  if (patternStatus.conflicts || knowledgeStatus.conflicts) {
    output += '\n## ⚠️ コンフリクト\n';
    const conflicts = [
      ...(patternStatus.conflicts ?? []),
      ...(knowledgeStatus.conflicts ?? []),
    ];
    for (const c of conflicts) {
      output += `- ${c.path}\n`;
    }
  }

  return output;
}

async function teamStatus(
  args: z.infer<typeof statusSchema>
): Promise<string> {
  await ensureImports();
  const repoPath = getRepoPath(args.repoPath);
  const gitClient = await createGitClient(repoPath);

  const isRepo = await gitClient.isRepo();
  if (!isRepo) {
    return '❌ このディレクトリはGitリポジトリではありません。';
  }

  const patternSharer = createPatternSharerFn({ gitClient });
  const teamKnowledge = createTeamKnowledgeFn({ gitClient });

  const patterns = await patternSharer.listPatterns();
  const knowledgeStats = await teamKnowledge.getStats();
  const gitStatus = await gitClient.status();
  const branch = await gitClient.getCurrentBranch();
  const remotes = await gitClient.listRemotes();

  let output = '# 📊 チームステータス\n\n';

  output += '## Git情報\n';
  output += `- リポジトリ: ${repoPath}\n`;
  output += `- 現在のブランチ: ${branch}\n`;
  output += `- リモート: ${remotes.length > 0 ? remotes.map((r: { name: string }) => r.name).join(', ') : 'なし'}\n`;
  output += `- 未コミットの変更: ${gitStatus.length}件\n`;

  output += '\n## 共有パターン\n';
  output += `- 合計: ${patterns.length}件\n`;

  const patternsByType = new Map<string, number>();
  patterns.forEach((p: { type: string }) => {
    patternsByType.set(p.type, (patternsByType.get(p.type) ?? 0) + 1);
  });
  for (const [type, count] of patternsByType) {
    output += `- ${type}: ${count}件\n`;
  }

  output += '\n## ナレッジベース\n';
  output += `- 合計エントリ: ${knowledgeStats.totalEntries}件\n`;
  output += `- カテゴリ別:\n`;
  for (const [category, count] of Object.entries(knowledgeStats.byCategory)) {
    output += `  - ${category}: ${count}件\n`;
  }

  if (knowledgeStats.topContributors.length > 0) {
    output += '\n### トップコントリビューター\n';
    for (const { member, count } of knowledgeStats.topContributors.slice(0, 5)) {
      output += `- ${member.name}: ${count}件\n`;
    }
  }

  return output;
}

async function teamAddKnowledge(
  args: z.infer<typeof addKnowledgeSchema>
): Promise<string> {
  await ensureImports();
  const repoPath = getRepoPath(args.repoPath);
  const gitClient = await createGitClient(repoPath);

  await gitClient.ensureTeamBranch();

  const knowledge = createTeamKnowledgeFn({
    gitClient,
    autoCommit: true,
  });

  const result = await knowledge.addEntry({
    title: args.title,
    content: args.content,
    type: args.type,
    category: args.category,
    tags: args.tags,
    relatedEntities: args.relatedEntities,
    contributor: {
      id: args.memberEmail,
      name: args.memberName,
      email: args.memberEmail,
    },
  });

  if (result.success) {
    return `✅ ナレッジ「${args.title}」を追加しました。\n\n` +
           `📁 ファイル: ${result.affectedFiles?.join(', ') ?? ''}\n` +
           `🔀 ブランチ: musubix-team\n\n` +
           `💡 チームと共有するには:\n` +
           `   git push origin musubix-team`;
  } else {
    return `❌ ナレッジ追加に失敗しました: ${result.message}`;
  }
}

async function teamQueryKnowledge(
  args: z.infer<typeof queryKnowledgeSchema>
): Promise<string> {
  await ensureImports();
  const repoPath = getRepoPath(args.repoPath);
  const gitClient = await createGitClient(repoPath);
  const knowledge = createTeamKnowledgeFn({ gitClient });

  let entries;

  if (args.query) {
    entries = await knowledge.search(args.query);
  } else {
    entries = await knowledge.query({
      type: args.type,
      category: args.category,
      tags: args.tags,
      limit: args.limit,
    });
  }

  if (entries.length === 0) {
    return '📭 該当するナレッジが見つかりませんでした。';
  }

  let output = `# 📖 ナレッジ検索結果 (${entries.length}件)\n\n`;

  for (const entry of entries) {
    const typeEmoji = getTypeEmoji(entry.type);
    output += `## ${typeEmoji} ${entry.title}\n\n`;
    output += `- **タイプ**: ${entry.type}\n`;
    output += `- **カテゴリ**: ${entry.category}\n`;
    output += `- **投稿者**: ${entry.contributor.name}\n`;
    output += `- **日付**: ${new Date(entry.timestamp).toLocaleDateString('ja-JP')}\n`;
    if (entry.tags && entry.tags.length > 0) {
      output += `- **タグ**: ${entry.tags.join(', ')}\n`;
    }
    output += `\n${entry.content}\n\n`;

    if (entry.relatedEntities && entry.relatedEntities.length > 0) {
      output += `**関連**: ${entry.relatedEntities.join(', ')}\n\n`;
    }

    output += '---\n\n';
  }

  return output;
}

// Helper functions
function getStatusEmoji(status: string): string {
  switch (status) {
    case 'synced': return '✅';
    case 'pending': return '⏳';
    case 'conflict': return '⚠️';
    case 'error': return '❌';
    default: return '❓';
  }
}

function getTypeEmoji(type: string): string {
  switch (type) {
    case 'decision': return '📋';
    case 'lesson-learned': return '💡';
    case 'best-practice': return '✨';
    case 'warning': return '⚠️';
    default: return '📝';
  }
}

// Tool definitions
export const teamSharePatternTool: ToolDefinition = {
  name: 'team_share_pattern',
  description: 'チームとコードパターンを共有します。Gitブランチ経由で共有され、チームメンバーが採用できます。',
  inputSchema: sharePatternSchema.shape as unknown as Record<string, unknown>,
  handler: async (args): Promise<ToolResult> => {
    const result = await teamSharePattern(args as z.infer<typeof sharePatternSchema>);
    return { content: [{ type: 'text', text: result }] };
  },
};

export const teamListPatternsTool: ToolDefinition = {
  name: 'team_list_patterns',
  description: 'チームで共有されているパターンの一覧を表示します。タイプやタグでフィルタリングできます。',
  inputSchema: listPatternsSchema.shape as unknown as Record<string, unknown>,
  handler: async (args): Promise<ToolResult> => {
    const result = await teamListPatterns(args as z.infer<typeof listPatternsSchema>);
    return { content: [{ type: 'text', text: result }] };
  },
};

export const teamSyncTool: ToolDefinition = {
  name: 'team_sync',
  description: 'チームのパターンとナレッジをリモートと同期します。',
  inputSchema: syncSchema.shape as unknown as Record<string, unknown>,
  handler: async (args): Promise<ToolResult> => {
    const result = await teamSync(args as z.infer<typeof syncSchema>);
    return { content: [{ type: 'text', text: result }] };
  },
};

export const teamStatusTool: ToolDefinition = {
  name: 'team_status',
  description: 'チーム共有の現在のステータス（パターン数、ナレッジ数、Git状態）を表示します。',
  inputSchema: statusSchema.shape as unknown as Record<string, unknown>,
  handler: async (args): Promise<ToolResult> => {
    const result = await teamStatus(args as z.infer<typeof statusSchema>);
    return { content: [{ type: 'text', text: result }] };
  },
};

export const teamAddKnowledgeTool: ToolDefinition = {
  name: 'team_add_knowledge',
  description: 'チームのナレッジベースに新しいエントリを追加します。決定、教訓、ベストプラクティス、警告などを共有できます。',
  inputSchema: addKnowledgeSchema.shape as unknown as Record<string, unknown>,
  handler: async (args): Promise<ToolResult> => {
    const result = await teamAddKnowledge(args as z.infer<typeof addKnowledgeSchema>);
    return { content: [{ type: 'text', text: result }] };
  },
};

export const teamQueryKnowledgeTool: ToolDefinition = {
  name: 'team_query_knowledge',
  description: 'チームのナレッジベースを検索します。タイプ、カテゴリ、タグでフィルタリングできます。',
  inputSchema: queryKnowledgeSchema.shape as unknown as Record<string, unknown>,
  handler: async (args): Promise<ToolResult> => {
    const result = await teamQueryKnowledge(args as z.infer<typeof queryKnowledgeSchema>);
    return { content: [{ type: 'text', text: result }] };
  },
};

// Export all tools
export const teamTools: ToolDefinition[] = [
  teamSharePatternTool,
  teamListPatternsTool,
  teamSyncTool,
  teamStatusTool,
  teamAddKnowledgeTool,
  teamQueryKnowledgeTool,
];
