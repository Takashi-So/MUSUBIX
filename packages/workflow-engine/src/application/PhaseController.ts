/**
 * PhaseController - Application Service
 * 
 * Controls phase transitions and manages workflow state
 * 
 * @see TSK-WORKFLOW-001 - PhaseController
 * @see REQ-ORCH-001 - Phase Transition
 * @see DES-ORCH-001 - PhaseController Component
 */

import {
  type PhaseType,
  type Phase,
  type Workflow,
  type ReviewResult,
  type ReviewCheckpoint,
  createWorkflow,
  startWorkflow,
  updatePhase,
  transitionToPhase,
  getCurrentPhase,
  setReview,
  approvePhase,
  createReviewResult,
  parseApprovalFromInput,
  getPhaseMetadata,
  generateWorkflowId,
} from '../domain/index.js';

/**
 * Phase controller configuration
 */
export interface PhaseControllerConfig {
  /** Auto-start workflow on creation */
  autoStart?: boolean;
  /** Require explicit approval for transitions */
  requireApproval?: boolean;
}

/**
 * Phase controller result
 */
export interface PhaseControllerResult<T = void> {
  readonly success: boolean;
  readonly data?: T;
  readonly error?: string;
  readonly message: string;
}

/**
 * Phase Controller
 * 
 * Manages workflow phase transitions
 */
export class PhaseController {
  private workflows: Map<string, Workflow> = new Map();
  private readonly config: PhaseControllerConfig;

  constructor(config: PhaseControllerConfig = {}) {
    this.config = {
      autoStart: true,
      requireApproval: true,
      ...config,
    };
  }

  /**
   * Create a new workflow
   * 
   * @param name - Workflow name
   * @param description - Optional description
   * @returns Created workflow
   */
  createWorkflow(name: string, description?: string): PhaseControllerResult<Workflow> {
    try {
      const id = generateWorkflowId(name);
      let workflow = createWorkflow(id, name, description);
      
      if (this.config.autoStart) {
        workflow = startWorkflow(workflow);
      }
      
      this.workflows.set(id, workflow);
      
      return {
        success: true,
        data: workflow,
        message: `Workflow "${name}" created with ID: ${id}`,
      };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : String(error),
        message: 'Failed to create workflow',
      };
    }
  }

  /**
   * Get workflow by ID
   * 
   * @param workflowId - Workflow ID
   * @returns Workflow or undefined
   */
  getWorkflow(workflowId: string): Workflow | undefined {
    return this.workflows.get(workflowId);
  }

  /**
   * Submit phase for review
   * 
   * @param workflowId - Workflow ID
   * @param checkpoints - Review checkpoints
   * @returns Review result
   */
  submitForReview(
    workflowId: string,
    checkpoints: ReviewCheckpoint[]
  ): PhaseControllerResult<ReviewResult> {
    try {
      const workflow = this.workflows.get(workflowId);
      if (!workflow) {
        return {
          success: false,
          error: 'Workflow not found',
          message: `Workflow ${workflowId} not found`,
        };
      }
      
      const currentPhase = getCurrentPhase(workflow);
      if (!currentPhase) {
        return {
          success: false,
          error: 'No active phase',
          message: 'Workflow has no active phase',
        };
      }
      
      const review = createReviewResult(currentPhase.type, checkpoints);
      const updatedPhase = setReview(currentPhase, review);
      const updatedWorkflow = updatePhase(workflow, updatedPhase);
      
      this.workflows.set(workflowId, updatedWorkflow);
      
      return {
        success: true,
        data: review,
        message: this.formatReviewMessage(review),
      };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : String(error),
        message: 'Failed to submit for review',
      };
    }
  }

  /**
   * Process user approval/rejection response
   * 
   * @param workflowId - Workflow ID
   * @param userInput - User input text
   * @param approver - Approver identifier
   * @returns Result
   */
  processApproval(
    workflowId: string,
    userInput: string,
    approver: string
  ): PhaseControllerResult<Phase> {
    try {
      const workflow = this.workflows.get(workflowId);
      if (!workflow) {
        return {
          success: false,
          error: 'Workflow not found',
          message: `Workflow ${workflowId} not found`,
        };
      }
      
      const currentPhase = getCurrentPhase(workflow);
      if (!currentPhase) {
        return {
          success: false,
          error: 'No active phase',
          message: 'Workflow has no active phase',
        };
      }
      
      const approvalStatus = parseApprovalFromInput(userInput);
      
      if (approvalStatus === 'rejected') {
        return {
          success: true,
          data: currentPhase,
          message: '修正が要求されました。フィードバックに基づいて修正を行います。',
        };
      }
      
      if (approvalStatus === 'approved') {
        const approvedPhase = approvePhase(currentPhase, approver, userInput);
        const updatedWorkflow = updatePhase(workflow, approvedPhase);
        this.workflows.set(workflowId, updatedWorkflow);
        
        return {
          success: true,
          data: approvedPhase,
          message: `${getPhaseMetadata(currentPhase.type).label}が承認されました。`,
        };
      }
      
      return {
        success: false,
        error: 'Approval status unclear',
        message: '承認キーワードが検出できませんでした。「承認」または「修正」でお答えください。',
      };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : String(error),
        message: 'Failed to process approval',
      };
    }
  }

  /**
   * Transition to next phase
   * 
   * @param workflowId - Workflow ID
   * @param targetPhase - Target phase
   * @returns Result
   */
  transitionTo(
    workflowId: string,
    targetPhase: PhaseType
  ): PhaseControllerResult<Workflow> {
    try {
      const workflow = this.workflows.get(workflowId);
      if (!workflow) {
        return {
          success: false,
          error: 'Workflow not found',
          message: `Workflow ${workflowId} not found`,
        };
      }
      
      // Enforce requirement: design → implementation is FORBIDDEN
      if (workflow.currentPhase === 'design' && targetPhase === 'implementation') {
        return {
          success: false,
          error: 'Direct transition forbidden',
          message: '⚠️ 設計から実装への直接遷移は禁止されています。必ずPhase 3（タスク分解）を経てください。',
        };
      }
      
      const updatedWorkflow = transitionToPhase(workflow, targetPhase);
      this.workflows.set(workflowId, updatedWorkflow);
      
      return {
        success: true,
        data: updatedWorkflow,
        message: `${getPhaseMetadata(targetPhase).label}に移行しました。`,
      };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : String(error),
        message: 'Failed to transition phase',
      };
    }
  }

  /**
   * Get next valid phase
   * 
   * @param workflowId - Workflow ID
   * @returns Next phase type or null
   */
  getNextPhase(workflowId: string): PhaseType | null {
    const workflow = this.workflows.get(workflowId);
    if (!workflow?.currentPhase) {
      return null;
    }
    
    const currentPhase = workflow.currentPhase;
    const phaseOrder: PhaseType[] = [
      'requirements',
      'design',
      'task-breakdown',
      'implementation',
      'completion',
    ];
    
    const currentIndex = phaseOrder.indexOf(currentPhase);
    if (currentIndex < 0 || currentIndex >= phaseOrder.length - 1) {
      return null;
    }
    
    return phaseOrder[currentIndex + 1];
  }

  /**
   * Format review message for display
   * 
   * @param review - Review result
   * @returns Formatted message
   */
  private formatReviewMessage(review: ReviewResult): string {
    const lines = ['📋 **レビュー結果**', '', '| 観点 | 状態 | 詳細 |', '|------|------|------|'];
    
    for (const checkpoint of review.checkpoints) {
      lines.push(`| ${checkpoint.name} | ${checkpoint.status} | ${checkpoint.details} |`);
    }
    
    lines.push('');
    lines.push('👉 **次のアクションを選択してください:**');
    lines.push('- 「修正」/ 具体的な修正指示 → 修正して再提示');
    lines.push('- 「承認」/「OK」/「進める」 → 次フェーズへ');
    
    return lines.join('\n');
  }

  /**
   * Get all workflows
   * 
   * @returns All workflows
   */
  getAllWorkflows(): Workflow[] {
    return Array.from(this.workflows.values());
  }

  /**
   * Clear all workflows (for testing)
   */
  clearAll(): void {
    this.workflows.clear();
  }
}

/**
 * Create a phase controller instance
 * 
 * @param config - Configuration
 * @returns PhaseController instance
 */
export function createPhaseController(config?: PhaseControllerConfig): PhaseController {
  return new PhaseController(config);
}
