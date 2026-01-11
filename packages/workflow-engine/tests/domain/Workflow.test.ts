/**
 * Workflow Entity Tests
 * 
 * Tests for workflow entity operations
 * 
 * @see REQ-ORCH-001 - Phase Transition
 * @see REQ-ORCH-002 - State Tracking
 */

import { describe, it, expect } from 'vitest';
import {
  type Workflow,
  createWorkflow,
  startWorkflow,
  transitionToPhase,
  getCurrentPhase,
  getWorkflowProgress,
  generateWorkflowId,
  canProceedToImplementation,
  updatePhase,
  checkImplementationPrerequisites,
} from '../../src/domain/entities/Workflow.js';
import {
  type Phase,
  approvePhase,
  setReview,
  addArtifact,
  createArtifact,
} from '../../src/domain/entities/Phase.js';

describe('Workflow Entity', () => {
  describe('createWorkflow', () => {
    it('should create workflow with initial state', () => {
      const workflow = createWorkflow('WFL-001', 'Test Workflow');
      
      expect(workflow.id).toBe('WFL-001');
      expect(workflow.name).toBe('Test Workflow');
      expect(workflow.status).toBe('not-started');
      expect(workflow.currentPhase).toBeNull();
    });

    it('should create workflow with description', () => {
      const workflow = createWorkflow('WFL-002', 'Test', 'A test workflow');
      expect(workflow.description).toBe('A test workflow');
    });

    it('should initialize all 5 phases', () => {
      const workflow = createWorkflow('WFL-003', 'Test');
      expect(workflow.phases.size).toBe(5);
      expect(workflow.phases.has('requirements')).toBe(true);
      expect(workflow.phases.has('design')).toBe(true);
      expect(workflow.phases.has('task-breakdown')).toBe(true);
      expect(workflow.phases.has('implementation')).toBe(true);
      expect(workflow.phases.has('completion')).toBe(true);
    });
  });

  describe('startWorkflow', () => {
    it('should start workflow at requirements phase', () => {
      const workflow = createWorkflow('WFL-001', 'Test');
      const started = startWorkflow(workflow);
      
      expect(started.status).toBe('in-progress');
      expect(started.currentPhase).toBe('requirements');
    });

    it('should not start already started workflow', () => {
      const workflow = createWorkflow('WFL-001', 'Test');
      const started = startWorkflow(workflow);
      
      expect(() => startWorkflow(started)).toThrow();
    });

    it('should set requirements phase to in-progress', () => {
      const workflow = createWorkflow('WFL-001', 'Test');
      const started = startWorkflow(workflow);
      const reqPhase = started.phases.get('requirements');
      
      expect(reqPhase?.status).toBe('in-progress');
    });
  });

  describe('getCurrentPhase', () => {
    it('should return current phase', () => {
      const workflow = createWorkflow('WFL-001', 'Test');
      const started = startWorkflow(workflow);
      const currentPhase = getCurrentPhase(started);
      
      expect(currentPhase).not.toBeNull();
      expect(currentPhase?.type).toBe('requirements');
    });

    it('should return null for not-started workflow', () => {
      const workflow = createWorkflow('WFL-001', 'Test');
      const currentPhase = getCurrentPhase(workflow);
      
      expect(currentPhase).toBeNull();
    });
  });

  describe('transitionToPhase', () => {
    it('should THROW when attempting design -> implementation direct transition', () => {
      // Setup: Create workflow and transition to design
      let workflow = createWorkflow('WFL-001', 'Test');
      workflow = startWorkflow(workflow);
      
      // Complete and approve requirements phase
      const reqPhase = workflow.phases.get('requirements')!;
      const reviewedReq = setReview(reqPhase, {
        id: 'REV-001',
        phase: 'requirements',
        checkpoints: [{ name: 'Complete', status: '✅', details: 'OK' }],
        overall: 'pass',
        timestamp: new Date(),
      });
      const approvedReq = approvePhase(reviewedReq, 'user');
      workflow = updatePhase(workflow, approvedReq);
      
      // Transition to design
      workflow = transitionToPhase(workflow, 'design');
      
      // Complete and approve design phase
      const designPhase = workflow.phases.get('design')!;
      const reviewedDesign = setReview(designPhase, {
        id: 'REV-002',
        phase: 'design',
        checkpoints: [{ name: 'Complete', status: '✅', details: 'OK' }],
        overall: 'pass',
        timestamp: new Date(),
      });
      const approvedDesign = approvePhase(reviewedDesign, 'user');
      workflow = updatePhase(workflow, approvedDesign);
      
      // THIS IS THE CRITICAL TEST: design → implementation is PROHIBITED!
      expect(() => transitionToPhase(workflow, 'implementation')).toThrow(
        /設計から実装への直接遷移は禁止/
      );
    });

    it('should allow design -> task-breakdown transition', () => {
      let workflow = createWorkflow('WFL-001', 'Test');
      workflow = startWorkflow(workflow);
      
      // Complete and approve requirements
      const reqPhase = workflow.phases.get('requirements')!;
      const reviewedReq = setReview(reqPhase, {
        id: 'REV-001',
        phase: 'requirements',
        checkpoints: [{ name: 'Complete', status: '✅', details: 'OK' }],
        overall: 'pass',
        timestamp: new Date(),
      });
      const approvedReq = approvePhase(reviewedReq, 'user');
      workflow = updatePhase(workflow, approvedReq);
      
      // Transition to design
      workflow = transitionToPhase(workflow, 'design');
      
      // Complete and approve design
      const designPhase = workflow.phases.get('design')!;
      const reviewedDesign = setReview(designPhase, {
        id: 'REV-002',
        phase: 'design',
        checkpoints: [{ name: 'Complete', status: '✅', details: 'OK' }],
        overall: 'pass',
        timestamp: new Date(),
      });
      const approvedDesign = approvePhase(reviewedDesign, 'user');
      workflow = updatePhase(workflow, approvedDesign);
      
      // This should work: design → task-breakdown
      workflow = transitionToPhase(workflow, 'task-breakdown');
      expect(workflow.currentPhase).toBe('task-breakdown');
    });
  });

  describe('getWorkflowProgress', () => {
    it('should return 0 for not-started workflow', () => {
      const workflow = createWorkflow('WFL-001', 'Test');
      expect(getWorkflowProgress(workflow)).toBe(0);
    });

    it('should return 0 for in-progress phase (not yet approved)', () => {
      const workflow = startWorkflow(createWorkflow('WFL-001', 'Test'));
      // Phase is in-progress but not approved
      expect(getWorkflowProgress(workflow)).toBe(0);
    });

    it('should return 20% after completing first phase', () => {
      let workflow = createWorkflow('WFL-001', 'Test');
      workflow = startWorkflow(workflow);
      
      // Complete and approve requirements
      const reqPhase = workflow.phases.get('requirements')!;
      const reviewedReq = setReview(reqPhase, {
        id: 'REV-001',
        phase: 'requirements',
        checkpoints: [{ name: 'Complete', status: '✅', details: 'OK' }],
        overall: 'pass',
        timestamp: new Date(),
      });
      const approvedReq = approvePhase(reviewedReq, 'user');
      workflow = updatePhase(workflow, approvedReq);
      
      // 1 of 5 phases approved = 20%
      expect(getWorkflowProgress(workflow)).toBe(20);
    });
  });

  describe('generateWorkflowId', () => {
    it('should generate ID with WFL prefix by default', () => {
      const id = generateWorkflowId();
      expect(id).toMatch(/^WFL-[a-z0-9]+$/);
    });

    it('should generate ID with name-based prefix', () => {
      const id = generateWorkflowId('TestProject');
      expect(id).toMatch(/^TES-[a-z0-9]+$/);
    });
  });

  describe('canProceedToImplementation', () => {
    it('should return false when task-breakdown is not approved', () => {
      const workflow = createWorkflow('WFL-001', 'Test');
      expect(canProceedToImplementation(workflow)).toBe(false);
    });
  });

  describe('checkImplementationPrerequisites', () => {
    it('should fail when requirements phase is not approved', () => {
      const workflow = startWorkflow(createWorkflow('WFL-001', 'Test'));
      const result = checkImplementationPrerequisites(workflow);
      
      expect(result.canProceed).toBe(false);
      expect(result.missingArtifacts.length).toBeGreaterThan(0);
      expect(result.message).toContain('実装を開始できません');
    });

    it('should fail when design phase is not approved', () => {
      let workflow = createWorkflow('WFL-001', 'Test');
      workflow = startWorkflow(workflow);
      
      // Complete and approve requirements with artifact
      let reqPhase = workflow.phases.get('requirements')!;
      reqPhase = addArtifact(reqPhase, createArtifact('requirements', 'storage/specs/REQ-001.md'));
      reqPhase = setReview(reqPhase, {
        id: 'REV-001',
        phase: 'requirements',
        checkpoints: [{ name: 'Complete', status: '✅', details: 'OK' }],
        overall: 'pass',
        timestamp: new Date(),
      });
      reqPhase = approvePhase(reqPhase, 'user');
      workflow = updatePhase(workflow, reqPhase);
      
      const result = checkImplementationPrerequisites(workflow);
      expect(result.canProceed).toBe(false);
      expect(result.missingArtifacts.some(m => m.includes('設計書'))).toBe(true);
    });

    it('should fail when task-breakdown phase is not approved', () => {
      let workflow = createWorkflow('WFL-001', 'Test');
      workflow = startWorkflow(workflow);
      
      // Complete requirements
      let reqPhase = workflow.phases.get('requirements')!;
      reqPhase = addArtifact(reqPhase, createArtifact('requirements', 'storage/specs/REQ-001.md'));
      reqPhase = setReview(reqPhase, {
        id: 'REV-001',
        phase: 'requirements',
        checkpoints: [{ name: 'Complete', status: '✅', details: 'OK' }],
        overall: 'pass',
        timestamp: new Date(),
      });
      reqPhase = approvePhase(reqPhase, 'user');
      workflow = updatePhase(workflow, reqPhase);
      
      // Transition to design and complete
      workflow = transitionToPhase(workflow, 'design');
      let designPhase = workflow.phases.get('design')!;
      designPhase = addArtifact(designPhase, createArtifact('design', 'storage/design/DES-001.md'));
      designPhase = setReview(designPhase, {
        id: 'REV-002',
        phase: 'design',
        checkpoints: [{ name: 'Complete', status: '✅', details: 'OK' }],
        overall: 'pass',
        timestamp: new Date(),
      });
      designPhase = approvePhase(designPhase, 'user');
      workflow = updatePhase(workflow, designPhase);
      
      const result = checkImplementationPrerequisites(workflow);
      expect(result.canProceed).toBe(false);
      expect(result.missingArtifacts.some(m => m.includes('タスク分解'))).toBe(true);
    });

    it('should fail when artifacts are missing', () => {
      let workflow = createWorkflow('WFL-001', 'Test');
      workflow = startWorkflow(workflow);
      
      // Complete requirements WITHOUT artifact
      let reqPhase = workflow.phases.get('requirements')!;
      reqPhase = setReview(reqPhase, {
        id: 'REV-001',
        phase: 'requirements',
        checkpoints: [{ name: 'Complete', status: '✅', details: 'OK' }],
        overall: 'pass',
        timestamp: new Date(),
      });
      reqPhase = approvePhase(reqPhase, 'user');
      workflow = updatePhase(workflow, reqPhase);
      
      const result = checkImplementationPrerequisites(workflow);
      expect(result.canProceed).toBe(false);
      expect(result.missingArtifacts.some(m => m.includes('成果物なし'))).toBe(true);
    });

    it('should pass when all prerequisites are met', () => {
      let workflow = createWorkflow('WFL-001', 'Test');
      workflow = startWorkflow(workflow);
      
      // Complete requirements with artifact
      let reqPhase = workflow.phases.get('requirements')!;
      reqPhase = addArtifact(reqPhase, createArtifact('requirements', 'storage/specs/REQ-001.md'));
      reqPhase = setReview(reqPhase, {
        id: 'REV-001',
        phase: 'requirements',
        checkpoints: [{ name: 'Complete', status: '✅', details: 'OK' }],
        overall: 'pass',
        timestamp: new Date(),
      });
      reqPhase = approvePhase(reqPhase, 'user');
      workflow = updatePhase(workflow, reqPhase);
      
      // Transition to design and complete with artifact
      workflow = transitionToPhase(workflow, 'design');
      let designPhase = workflow.phases.get('design')!;
      designPhase = addArtifact(designPhase, createArtifact('design', 'storage/design/DES-001.md'));
      designPhase = setReview(designPhase, {
        id: 'REV-002',
        phase: 'design',
        checkpoints: [{ name: 'Complete', status: '✅', details: 'OK' }],
        overall: 'pass',
        timestamp: new Date(),
      });
      designPhase = approvePhase(designPhase, 'user');
      workflow = updatePhase(workflow, designPhase);
      
      // Transition to task-breakdown and complete with artifact
      workflow = transitionToPhase(workflow, 'task-breakdown');
      let taskPhase = workflow.phases.get('task-breakdown')!;
      taskPhase = addArtifact(taskPhase, createArtifact('task-breakdown', 'storage/tasks/TSK-001.md'));
      taskPhase = setReview(taskPhase, {
        id: 'REV-003',
        phase: 'task-breakdown',
        checkpoints: [{ name: 'Complete', status: '✅', details: 'OK' }],
        overall: 'pass',
        timestamp: new Date(),
      });
      taskPhase = approvePhase(taskPhase, 'user');
      workflow = updatePhase(workflow, taskPhase);
      
      const result = checkImplementationPrerequisites(workflow);
      expect(result.canProceed).toBe(true);
      expect(result.missingArtifacts.length).toBe(0);
      expect(result.message).toContain('全ての前提条件を満たしています');
    });
  });
});
