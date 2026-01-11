/**
 * Workflow Tool Handlers
 * 
 * Handlers for workflow_* MCP tools
 * 
 * @see TSK-MCP-002 - workflow_* MCP Tools
 * @see REQ-ORCH-001 - Phase Transition
 */

import type {
  WorkflowCreateInput,
  WorkflowTransitionInput,
  WorkflowStatusInput,
  WorkflowReviewInput,
  WorkflowGateInput,
} from './workflow-tools.js';

/**
 * Workflow state storage
 */
interface WorkflowState {
  id: string;
  name: string;
  description?: string;
  status: 'not-started' | 'in-progress' | 'completed';
  currentPhase: string | null;
  phases: Record<string, {
    status: string;
    approval?: { status: string; approver: string; timestamp: Date };
    artifacts: string[];
  }>;
  createdAt: Date;
  updatedAt: Date;
}

// In-memory workflow state
const workflows = new Map<string, WorkflowState>();

/**
 * Generate workflow ID
 */
function generateWorkflowId(name: string): string {
  const prefix = name.substring(0, 3).toUpperCase().replace(/[^A-Z]/g, 'W');
  return `WFL-${prefix}-${Date.now().toString(36)}`;
}

/**
 * Phase order and valid transitions
 */
const PHASE_ORDER = ['requirements', 'design', 'task-breakdown', 'implementation', 'completion'];
const PHASE_LABELS: Record<string, string> = {
  'requirements': 'Phase 1: 要件定義',
  'design': 'Phase 2: 設計',
  'task-breakdown': 'Phase 3: タスク分解',
  'implementation': 'Phase 4: 実装',
  'completion': 'Phase 5: 完了',
};

/**
 * Check if transition is valid
 */
function isValidTransition(from: string, to: string): { valid: boolean; error?: string } {
  const fromIndex = PHASE_ORDER.indexOf(from);
  const toIndex = PHASE_ORDER.indexOf(to);
  
  // Cannot skip phases
  if (toIndex !== fromIndex + 1) {
    return { valid: false, error: `${from}から${to}へは遷移できません。次のフェーズは${PHASE_ORDER[fromIndex + 1]}です。` };
  }
  
  // Special check: design → implementation is FORBIDDEN (must go through task-breakdown)
  if (from === 'design' && to === 'implementation') {
    return { 
      valid: false, 
      error: '⚠️ 設計から実装への直接遷移は禁止されています。必ずPhase 3（タスク分解）を経てください。' 
    };
  }
  
  return { valid: true };
}

/**
 * Handle workflow_create tool call
 */
export async function handleWorkflowCreate(input: WorkflowCreateInput): Promise<{
  content: Array<{ type: 'text'; text: string }>;
}> {
  const workflowId = generateWorkflowId(input.name);
  
  const state: WorkflowState = {
    id: workflowId,
    name: input.name,
    description: input.description,
    status: 'not-started',
    currentPhase: null,
    phases: {
      'requirements': { status: 'pending', artifacts: [] },
      'design': { status: 'pending', artifacts: [] },
      'task-breakdown': { status: 'pending', artifacts: [] },
      'implementation': { status: 'pending', artifacts: [] },
      'completion': { status: 'pending', artifacts: [] },
    },
    createdAt: new Date(),
    updatedAt: new Date(),
  };
  
  // Auto-start if requested
  if (input.autoStart !== false) {
    state.status = 'in-progress';
    state.currentPhase = 'requirements';
    state.phases['requirements'].status = 'in-progress';
  }
  
  workflows.set(workflowId, state);
  
  const responseText = `## 📋 ワークフロー作成完了

**ワークフローID**: \`${workflowId}\`
**名前**: ${input.name}
${input.description ? `**説明**: ${input.description}` : ''}

### ステータス

| フェーズ | 状態 |
|---------|------|
| Phase 1: 要件定義 | ${state.phases['requirements'].status === 'in-progress' ? '🔄 進行中' : '⬜ 未開始'} |
| Phase 2: 設計 | ⬜ 未開始 |
| Phase 3: タスク分解 | ⬜ 未開始 |
| Phase 4: 実装 | ⬜ 未開始 |
| Phase 5: 完了 | ⬜ 未開始 |

${state.currentPhase === 'requirements' ? `
### 🚀 Phase 1: 要件定義 を開始しました

EARS形式で要件を定義してください。完了後、\`workflow_review\` でセルフレビューを実行します。
` : ''}`;
  
  return {
    content: [{ type: 'text', text: responseText }],
  };
}

/**
 * Handle workflow_transition tool call
 */
export async function handleWorkflowTransition(input: WorkflowTransitionInput): Promise<{
  content: Array<{ type: 'text'; text: string }>;
}> {
  const state = workflows.get(input.workflowId);
  
  if (!state) {
    return {
      content: [{
        type: 'text',
        text: `❌ ワークフロー \`${input.workflowId}\` が見つかりません。`,
      }],
    };
  }
  
  if (!state.currentPhase) {
    return {
      content: [{
        type: 'text',
        text: `❌ ワークフローが開始されていません。`,
      }],
    };
  }
  
  // Check if current phase is approved
  const currentPhaseState = state.phases[state.currentPhase];
  if (currentPhaseState.status !== 'approved') {
    return {
      content: [{
        type: 'text',
        text: `⚠️ 現在のフェーズ (${PHASE_LABELS[state.currentPhase]}) が承認されていません。
        
レビューを実行し、承認を得てから次のフェーズに進んでください。`,
      }],
    };
  }
  
  // Validate transition
  const transitionCheck = isValidTransition(state.currentPhase, input.targetPhase);
  if (!transitionCheck.valid) {
    return {
      content: [{
        type: 'text',
        text: `❌ ${transitionCheck.error}`,
      }],
    };
  }
  
  // Perform transition
  state.currentPhase = input.targetPhase;
  state.phases[input.targetPhase].status = 'in-progress';
  state.updatedAt = new Date();
  
  // Check if completing
  if (input.targetPhase === 'completion') {
    state.status = 'completed';
  }
  
  return {
    content: [{
      type: 'text',
      text: `## ✅ フェーズ遷移完了

**ワークフロー**: \`${state.id}\`
**現在のフェーズ**: ${PHASE_LABELS[input.targetPhase]}

${input.targetPhase === 'completion' ? '🎉 ワークフローが完了しました！' : `${PHASE_LABELS[input.targetPhase]} を開始してください。`}`,
    }],
  };
}

/**
 * Handle workflow_status tool call
 */
export async function handleWorkflowStatus(input: WorkflowStatusInput): Promise<{
  content: Array<{ type: 'text'; text: string }>;
}> {
  const state = workflows.get(input.workflowId);
  
  if (!state) {
    return {
      content: [{
        type: 'text',
        text: `❌ ワークフロー \`${input.workflowId}\` が見つかりません。`,
      }],
    };
  }
  
  const getStatusEmoji = (status: string): string => {
    switch (status) {
      case 'pending': return '⬜';
      case 'in-progress': return '🔄';
      case 'completed': return '✅';
      case 'approved': return '✅✅';
      default: return '❓';
    }
  };
  
  const completedPhases = Object.values(state.phases).filter(p => 
    p.status === 'approved' || p.status === 'completed'
  ).length;
  const progress = Math.round((completedPhases / 5) * 100);
  
  const responseText = `## 📊 ワークフロー状態

**ワークフローID**: \`${state.id}\`
**名前**: ${state.name}
**ステータス**: ${state.status}
**現在のフェーズ**: ${state.currentPhase ? PHASE_LABELS[state.currentPhase] : 'N/A'}
**進捗**: ${progress}%

### フェーズ状態

| フェーズ | 状態 | 承認 |
|---------|------|------|
${PHASE_ORDER.map(phase => {
  const p = state.phases[phase];
  const approvalInfo = p.approval ? `${p.approval.approver} @ ${new Date(p.approval.timestamp).toLocaleString()}` : '-';
  return `| ${PHASE_LABELS[phase]} | ${getStatusEmoji(p.status)} ${p.status} | ${approvalInfo} |`;
}).join('\n')}

**作成日時**: ${state.createdAt.toISOString()}
**更新日時**: ${state.updatedAt.toISOString()}`;
  
  return {
    content: [{ type: 'text', text: responseText }],
  };
}

/**
 * Handle workflow_review tool call
 */
export async function handleWorkflowReview(input: WorkflowReviewInput): Promise<{
  content: Array<{ type: 'text'; text: string }>;
}> {
  const state = workflows.get(input.workflowId);
  
  if (!state) {
    return {
      content: [{
        type: 'text',
        text: `❌ ワークフロー \`${input.workflowId}\` が見つかりません。`,
      }],
    };
  }
  
  if (!state.currentPhase) {
    return {
      content: [{
        type: 'text',
        text: `❌ ワークフローが開始されていません。`,
      }],
    };
  }
  
  // Determine overall status
  const hasFailure = input.checkpoints.some(c => c.status === '❌');
  const hasWarning = input.checkpoints.some(c => c.status === '⚠️');
  const overall = hasFailure ? 'fail' : (hasWarning ? 'warning' : 'pass');
  
  // Update phase status
  if (overall === 'pass') {
    state.phases[state.currentPhase].status = 'completed';
  }
  state.updatedAt = new Date();
  
  const responseText = `## 📋 レビュー結果

**ワークフロー**: \`${state.id}\`
**フェーズ**: ${PHASE_LABELS[state.currentPhase]}
**結果**: ${overall === 'pass' ? '✅ 合格' : overall === 'warning' ? '⚠️ 警告あり' : '❌ 不合格'}

### チェック項目

| 観点 | 状態 | 詳細 |
|------|------|------|
${input.checkpoints.map(c => `| ${c.name} | ${c.status} | ${c.details} |`).join('\n')}

👉 **次のアクションを選択してください:**
- 「修正」/ 具体的な修正指示 → 修正して再提示
- 「承認」/「OK」/「進める」 → 次フェーズへ`;
  
  return {
    content: [{ type: 'text', text: responseText }],
  };
}

/**
 * Handle workflow_gate tool call
 */
export async function handleWorkflowGate(input: WorkflowGateInput): Promise<{
  content: Array<{ type: 'text'; text: string }>;
}> {
  const state = workflows.get(input.workflowId);
  
  if (!state) {
    return {
      content: [{
        type: 'text',
        text: `❌ ワークフロー \`${input.workflowId}\` が見つかりません。`,
      }],
    };
  }
  
  // Define quality gates for each phase
  const gateChecks: Record<string, string[]> = {
    'requirements': ['EARS形式の検証', '優先度設定の確認', '既存要件との整合性'],
    'design': ['トレーサビリティ (REQ → DES)', '型整合性', '設計パターン適用'],
    'task-breakdown': ['トレーサビリティ (DES → TSK)', 'タスクサイズの適切性', '依存関係の妥当性'],
    'implementation': ['ユニットテスト合格', '型チェック合格', 'リントエラーなし'],
    'completion': ['CHANGELOG更新', 'ドキュメント更新', 'コミット準備完了'],
  };
  
  const checks = gateChecks[input.phase] || [];
  
  // Simulate gate execution (all pass for now)
  const results = checks.map(check => ({
    name: check,
    passed: true,
    message: `${check}: OK`,
  }));
  
  const allPassed = results.every(r => r.passed);
  
  const responseText = `## 🔍 クオリティゲート結果

**ワークフロー**: \`${state.id}\`
**フェーズ**: ${PHASE_LABELS[input.phase]}
**結果**: ${allPassed ? '✅ 全て合格' : '❌ 不合格あり'}

### ゲートチェック

| チェック項目 | 結果 | メッセージ |
|--------------|------|-----------|
${results.map(r => `| ${r.name} | ${r.passed ? '✅' : '❌'} | ${r.message} |`).join('\n')}

${allPassed ? '全てのクオリティゲートを通過しました。フェーズを完了できます。' : '不合格のチェック項目を修正してください。'}`;
  
  return {
    content: [{ type: 'text', text: responseText }],
  };
}

/**
 * Process approval text and update workflow
 */
export function processApproval(workflowId: string, approvalText: string, approver: string): boolean {
  const state = workflows.get(workflowId);
  if (!state || !state.currentPhase) return false;
  
  const approvalKeywords = ['承認', 'approve', 'LGTM', '進める', 'OK', 'ok', '実装'];
  const isApproved = approvalKeywords.some(k => 
    approvalText.toLowerCase().includes(k.toLowerCase())
  );
  
  if (isApproved) {
    state.phases[state.currentPhase].status = 'approved';
    state.phases[state.currentPhase].approval = {
      status: 'approved',
      approver,
      timestamp: new Date(),
    };
    state.updatedAt = new Date();
    return true;
  }
  
  return false;
}
