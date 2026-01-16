// Workflow Engine Integration
// TSK-DR-026
// REQ: REQ-DR-INT-008
// DES: DES-DR-v3.4.0 Section 5.6

import type {
  PhaseType,
  Workflow,
} from '@nahisaho/musubix-workflow-engine';

/**
 * Result type for phase controller operations
 */
export interface PhaseControllerResult<T> {
  success: boolean;
  message?: string;
  error?: string;
  data?: T;
}

/**
 * Configuration for Workflow Engine integration
 */
export interface WorkflowIntegrationConfig {
  /** Auto-start workflow on creation */
  autoStart?: boolean;
  /** Require explicit approval for transitions */
  requireApproval?: boolean;
  /** Enable quality gate validation */
  enableQualityGates?: boolean;
}

/**
 * Default configuration
 */
const DEFAULT_CONFIG: Required<WorkflowIntegrationConfig> = {
  autoStart: true,
  requireApproval: true,
  enableQualityGates: true,
};

/**
 * Research phase mapping to workflow phases
 */
export type ResearchPhase = 
  | 'planning'
  | 'gathering'
  | 'analysis'
  | 'synthesis'
  | 'completion';

/**
 * Phase transition request
 */
export interface PhaseTransitionRequest {
  workflowId: string;
  targetPhase: ResearchPhase;
  reason?: string;
}

/**
 * Phase status info
 */
export interface PhaseStatusInfo {
  currentPhase: ResearchPhase;
  canTransition: boolean;
  nextPhases: ResearchPhase[];
  requiresApproval: boolean;
}

/**
 * Workflow Engine Integration
 * 
 * Integrates Deep Research with @nahisaho/musubix-workflow-engine
 * for 5-phase workflow control.
 * 
 * Workflow Phases:
 * 1. Planning: Initial query planning
 * 2. Gathering: Search and data collection
 * 3. Analysis: Content analysis
 * 4. Synthesis: Report generation
 * 5. Completion: Final review
 * 
 * Features:
 * - Phase transition control
 * - Quality gate validation
 * - Approval management
 * - State persistence
 */
export class WorkflowIntegration {
  private controller: any = null; // PhaseController type
  private config: Required<WorkflowIntegrationConfig>;
  private workflowCache: Map<string, string> = new Map(); // query -> workflowId

  constructor(config?: WorkflowIntegrationConfig) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  /**
   * Initialize the workflow engine
   */
  async initialize(): Promise<void> {
    const workflowModule = await this.loadWorkflowEngine();
    if (!workflowModule) {
      console.warn('⚠️  @nahisaho/musubix-workflow-engine package not available');
      return;
    }

    const { PhaseController } = workflowModule;
    this.controller = new PhaseController({
      autoStart: this.config.autoStart,
      requireApproval: this.config.requireApproval,
    });

    console.log('🔄 Workflow engine initialized');
  }

  /**
   * Check if workflow engine is available
   */
  async isAvailable(): Promise<boolean> {
    if (this.controller) return true;
    
    try {
      const workflowModule = await this.loadWorkflowEngine();
      return workflowModule !== null;
    } catch {
      return false;
    }
  }

  /**
   * Create a new research workflow
   */
  async createWorkflow(
    query: string,
    description?: string
  ): Promise<PhaseControllerResult<Workflow>> {
    if (!this.controller) {
      return {
        success: false,
        message: 'Workflow engine not initialized',
        error: 'Not initialized',
      };
    }

    const result = this.controller.createWorkflow(
      `Research: ${query}`,
      description ?? `Deep research workflow for: ${query}`
    );

    if (result.success && result.data) {
      this.workflowCache.set(query, result.data.id);
      console.log(`✅ Workflow created: ${result.data.id}`);
    }

    return result;
  }

  /**
   * Get workflow for a query
   */
  async getWorkflow(query: string): Promise<Workflow | null> {
    if (!this.controller) {
      return null;
    }

    const workflowId = this.workflowCache.get(query);
    if (!workflowId) {
      return null;
    }

    const workflow = this.controller.getWorkflow(workflowId);
    return workflow ?? null;
  }

  /**
   * Get current phase status
   */
  async getPhaseStatus(query: string): Promise<PhaseStatusInfo | null> {
    const workflow = await this.getWorkflow(query);
    if (!workflow) {
      return null;
    }

    const currentPhase = workflow.currentPhase 
      ? this.mapWorkflowPhaseToResearch(workflow.currentPhase)
      : null;

    return {
      currentPhase: currentPhase || 'planning', // Provide default value instead of null
      canTransition: workflow.currentPhase !== ('testing' as PhaseType),
      nextPhases: currentPhase ? this.getNextPhases(currentPhase) : [],
      requiresApproval: this.config.requireApproval,
    };
  }

  /**
   * Transition to next phase
   */
  async transitionPhase(
    request: PhaseTransitionRequest
  ): Promise<PhaseControllerResult<Workflow>> {
    if (!this.controller) {
      return {
        success: false,
        message: 'Workflow engine not initialized',
        error: 'Not initialized',
      };
    }

    const workflowPhase = this.mapResearchPhaseToWorkflow(request.targetPhase);
    
    const result = this.controller.transitionTo(
      request.workflowId,
      workflowPhase
    );

    if (result.success) {
      console.log(`🔄 Transitioned to phase: ${request.targetPhase}`);
    }

    return result;
  }

  /**
   * Approve current phase
   */
  async approvePhase(
    workflowId: string,
    reviewer: string = 'system'
  ): Promise<PhaseControllerResult<void>> {
    if (!this.controller) {
      return {
        success: false,
        message: 'Workflow engine not initialized',
        error: 'Not initialized',
      };
    }

    const result = this.controller.processApproval(workflowId, '承認', reviewer);

    if (result.success) {
      console.log(`✅ Phase approved by ${reviewer}`);
    }

    return result;
  }

  /**
   * Run quality gates for current phase
   */
  async runQualityGates(workflowId: string): Promise<boolean> {
    if (!this.controller || !this.config.enableQualityGates) {
      return true; // Pass if disabled
    }

    try {
      const result = this.controller.runQualityGates(workflowId);
      return result.success && result.data?.passed;
    } catch {
      return false;
    }
  }

  /**
   * Get all workflows
   */
  getAllWorkflows(): Map<string, string> {
    return new Map(this.workflowCache);
  }

  /**
   * Clear workflow cache
   */
  clearCache(): void {
    this.workflowCache.clear();
  }

  // ============================================================
  // Private Helper Methods
  // ============================================================

  /**
   * Map workflow phase to research phase
   */
  private mapWorkflowPhaseToResearch(phase: PhaseType): ResearchPhase {
    const mapping: Partial<Record<PhaseType, ResearchPhase>> = {
      'requirements': 'planning',
      'design': 'gathering',
      'implementation': 'synthesis',
    };
    return mapping[phase] ?? 'planning';
  }

  /**
   * Map research phase to workflow phase
   */
  private mapResearchPhaseToWorkflow(phase: ResearchPhase): PhaseType {
    const mapping: Partial<Record<ResearchPhase, PhaseType>> = {
      'planning': 'requirements',
      'gathering': 'design',
      'synthesis': 'implementation',
    };
    return mapping[phase] ?? ('requirements' as PhaseType);
  }

  /**
   * Get next possible phases
   */
  private getNextPhases(currentPhase: ResearchPhase): ResearchPhase[] {
    const transitions: Record<ResearchPhase, ResearchPhase[]> = {
      'planning': ['gathering'],
      'gathering': ['analysis'],
      'analysis': ['synthesis'],
      'synthesis': ['completion'],
      'completion': [],
    };
    return transitions[currentPhase] ?? [];
  }

  /**
   * Load @nahisaho/musubix-workflow-engine package dynamically
   */
  private async loadWorkflowEngine(): Promise<typeof import('@nahisaho/musubix-workflow-engine') | null> {
    try {
      const workflowModule = await import('@nahisaho/musubix-workflow-engine');
      return workflowModule;
    } catch (error) {
      console.error('⚠️  Failed to load @nahisaho/musubix-workflow-engine:', error);
      return null;
    }
  }
}

/**
 * Factory function to create Workflow integration
 */
export function createWorkflowIntegration(
  config?: WorkflowIntegrationConfig
): WorkflowIntegration {
  return new WorkflowIntegration(config);
}
