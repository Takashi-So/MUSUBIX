/**
 * Agent Tool Handlers
 * 
 * Handlers for agent_* MCP tools
 * 
 * @see TSK-MCP-001 - agent_* MCP Tools
 * @see REQ-AGENT-001 - Subagent-Driven Development
 */

import type {
  AgentDispatchInput,
  AgentStatusInput,
  AgentCancelInput,
  AgentAnalyzeInput,
} from './agent-tools.js';

/**
 * Execution state storage
 */
interface ExecutionState {
  id: string;
  status: 'pending' | 'running' | 'completed' | 'failed' | 'cancelled';
  taskDescription: string;
  startedAt: Date;
  completedAt?: Date;
  result?: unknown;
  error?: string;
  subagents: Array<{
    id: string;
    status: string;
    result?: unknown;
  }>;
}

// In-memory execution state (would be persisted in production)
const executions = new Map<string, ExecutionState>();

/**
 * Generate execution ID
 */
function generateExecutionId(): string {
  return `EXEC-${Date.now().toString(36)}-${Math.random().toString(36).substring(2, 7)}`;
}

/**
 * Handle agent_dispatch tool call
 */
export async function handleAgentDispatch(input: AgentDispatchInput): Promise<{
  content: Array<{ type: 'text'; text: string }>;
}> {
  const executionId = generateExecutionId();
  
  // Create execution state
  const state: ExecutionState = {
    id: executionId,
    status: 'pending',
    taskDescription: input.taskDescription,
    startedAt: new Date(),
    subagents: [],
  };
  
  executions.set(executionId, state);
  
  // Analyze task complexity
  const complexity = analyzeTaskComplexity(input.taskDescription, input.context);
  
  // Determine if decomposition is needed
  const shouldDecompose = input.options?.decompose !== false && 
    complexity.score > 0.6;
  
  let responseText: string;
  
  if (shouldDecompose) {
    // Decompose into subtasks
    const subtasks = decomposeTask(input.taskDescription);
    state.subagents = subtasks.map((_t, i) => ({
      id: `${executionId}-SUB-${i}`,
      status: 'pending',
    }));
    
    responseText = `## 🚀 エージェントディスパッチ完了

**実行ID**: \`${executionId}\`
**ステータス**: ディスパッチ済み

### タスク分析

| 因子 | 値 |
|------|-----|
| 複雑度スコア | ${complexity.score.toFixed(2)} |
| 分解推奨 | ${shouldDecompose ? 'はい' : 'いいえ'} |
| サブタスク数 | ${subtasks.length} |

### サブタスク

${subtasks.map((t, i) => `${i + 1}. ${t}`).join('\n')}

\`agent_status\` で進捗を確認できます。`;
  } else {
    state.status = 'running';
    
    responseText = `## 🚀 エージェントディスパッチ完了

**実行ID**: \`${executionId}\`
**ステータス**: 実行中

### タスク分析

| 因子 | 値 |
|------|-----|
| 複雑度スコア | ${complexity.score.toFixed(2)} |
| 分解推奨 | いいえ（単一タスクとして実行） |

タスクは単一エージェントで実行されています。
\`agent_status\` で進捗を確認できます。`;
  }
  
  return {
    content: [{ type: 'text', text: responseText }],
  };
}

/**
 * Handle agent_status tool call
 */
export async function handleAgentStatus(input: AgentStatusInput): Promise<{
  content: Array<{ type: 'text'; text: string }>;
}> {
  const state = executions.get(input.executionId);
  
  if (!state) {
    return {
      content: [{
        type: 'text',
        text: `❌ 実行ID \`${input.executionId}\` が見つかりません。`,
      }],
    };
  }
  
  const duration = state.completedAt
    ? state.completedAt.getTime() - state.startedAt.getTime()
    : Date.now() - state.startedAt.getTime();
  
  let statusEmoji: string;
  switch (state.status) {
    case 'pending': statusEmoji = '⏳'; break;
    case 'running': statusEmoji = '🔄'; break;
    case 'completed': statusEmoji = '✅'; break;
    case 'failed': statusEmoji = '❌'; break;
    case 'cancelled': statusEmoji = '🚫'; break;
    default: statusEmoji = '❓';
  }
  
  let responseText = `## ${statusEmoji} エージェント状態

**実行ID**: \`${state.id}\`
**ステータス**: ${state.status}
**開始時刻**: ${state.startedAt.toISOString()}
**経過時間**: ${Math.round(duration / 1000)}秒
`;

  if (state.subagents.length > 0) {
    responseText += `
### サブエージェント状態

| # | ID | ステータス |
|---|-----|---------|
${state.subagents.map((s, i) => `| ${i + 1} | ${s.id} | ${s.status} |`).join('\n')}
`;
  }
  
  if (input.includeDetails && state.result) {
    responseText += `
### 結果詳細

\`\`\`json
${JSON.stringify(state.result, null, 2)}
\`\`\`
`;
  }
  
  if (state.error) {
    responseText += `
### エラー

\`\`\`
${state.error}
\`\`\`
`;
  }
  
  return {
    content: [{ type: 'text', text: responseText }],
  };
}

/**
 * Handle agent_cancel tool call
 */
export async function handleAgentCancel(input: AgentCancelInput): Promise<{
  content: Array<{ type: 'text'; text: string }>;
}> {
  const state = executions.get(input.executionId);
  
  if (!state) {
    return {
      content: [{
        type: 'text',
        text: `❌ 実行ID \`${input.executionId}\` が見つかりません。`,
      }],
    };
  }
  
  if (state.status === 'completed' || state.status === 'failed') {
    return {
      content: [{
        type: 'text',
        text: `⚠️ 実行 \`${input.executionId}\` は既に終了しています（ステータス: ${state.status}）。`,
      }],
    };
  }
  
  state.status = 'cancelled';
  state.completedAt = new Date();
  state.error = input.reason ?? 'User requested cancellation';
  
  // Cancel pending subagents
  for (const sub of state.subagents) {
    if (sub.status === 'pending') {
      sub.status = 'cancelled';
    }
  }
  
  return {
    content: [{
      type: 'text',
      text: `## 🚫 キャンセル完了

**実行ID**: \`${input.executionId}\`
**理由**: ${input.reason ?? '（指定なし）'}

実行がキャンセルされました。`,
    }],
  };
}

/**
 * Handle agent_analyze tool call
 */
export async function handleAgentAnalyze(input: AgentAnalyzeInput): Promise<{
  content: Array<{ type: 'text'; text: string }>;
}> {
  const complexity = analyzeTaskComplexity(input.taskDescription, input.context);
  
  const factors = [
    { name: 'スコープ', value: complexity.factors.scope },
    { name: '依存関係', value: complexity.factors.dependencies },
    { name: 'ファイル数', value: complexity.factors.fileCount },
    { name: 'テストカバレッジ', value: complexity.factors.testCoverage },
    { name: '不確実性', value: complexity.factors.uncertainty },
  ];
  
  const recommendation = complexity.score > 0.6
    ? '**推奨**: サブエージェント分解を行い、並列実行することを推奨します。'
    : '**推奨**: 単一エージェントで実行可能なタスクです。';
  
  const responseText = `## 📊 タスク複雑度分析

**総合スコア**: ${complexity.score.toFixed(2)} / 1.00
**分解閾値**: 0.60

### 因子別スコア

| 因子 | スコア | 重み付き |
|------|--------|----------|
${factors.map(f => `| ${f.name} | ${f.value.toFixed(2)} | ${(f.value * 0.2).toFixed(2)} |`).join('\n')}

### 分析結果

${recommendation}

${complexity.score > 0.6 ? `
### 推奨サブタスク

${decomposeTask(input.taskDescription).map((t, i) => `${i + 1}. ${t}`).join('\n')}
` : ''}`;
  
  return {
    content: [{ type: 'text', text: responseText }],
  };
}

/**
 * Analyze task complexity (simplified implementation)
 */
function analyzeTaskComplexity(
  taskDescription: string,
  context?: { files?: string[]; existingTests?: boolean }
): {
  score: number;
  factors: {
    scope: number;
    dependencies: number;
    fileCount: number;
    testCoverage: number;
    uncertainty: number;
  };
} {
  const wordCount = taskDescription.split(/\s+/).length;
  const hasMultipleActions = /and|また|そして|かつ/i.test(taskDescription);
  const mentionsFiles = context?.files?.length ?? 0;
  const hasTests = context?.existingTests ?? false;
  const hasUncertainWords = /probably|maybe|might|perhaps|おそらく|かもしれない/i.test(taskDescription);
  
  const factors = {
    scope: Math.min(wordCount / 100, 1) * 0.5 + (hasMultipleActions ? 0.5 : 0),
    dependencies: Math.min(mentionsFiles / 5, 1),
    fileCount: Math.min(mentionsFiles / 10, 1),
    testCoverage: hasTests ? 0.3 : 0.7,
    uncertainty: hasUncertainWords ? 0.8 : 0.2,
  };
  
  const score = (
    factors.scope * 0.25 +
    factors.dependencies * 0.2 +
    factors.fileCount * 0.2 +
    factors.testCoverage * 0.15 +
    factors.uncertainty * 0.2
  );
  
  return { score: Math.min(score, 1), factors };
}

/**
 * Decompose task into subtasks (simplified implementation)
 */
function decomposeTask(taskDescription: string): string[] {
  // Simple heuristic decomposition
  const subtasks: string[] = [];
  
  if (taskDescription.includes('分析') || taskDescription.includes('analyze')) {
    subtasks.push('要件・コンテキストの分析');
  }
  if (taskDescription.includes('設計') || taskDescription.includes('design')) {
    subtasks.push('設計ドキュメントの作成');
  }
  if (taskDescription.includes('実装') || taskDescription.includes('implement')) {
    subtasks.push('コード実装');
  }
  if (taskDescription.includes('テスト') || taskDescription.includes('test')) {
    subtasks.push('テストの作成・実行');
  }
  if (taskDescription.includes('ドキュメント') || taskDescription.includes('document')) {
    subtasks.push('ドキュメント更新');
  }
  
  // Default subtasks if none detected
  if (subtasks.length === 0) {
    subtasks.push(
      '前提条件の確認',
      'メイン処理の実装',
      '結果の検証',
    );
  }
  
  return subtasks;
}
