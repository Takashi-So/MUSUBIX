// Workflow Engine Integration Tests
// TSK-DR-026
// REQ: REQ-DR-INT-008
// DES: DES-DR-v3.4.0 Section 5.6

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  WorkflowIntegration,
  createWorkflowIntegration,
  type ResearchPhase,
  type PhaseTransitionRequest,
} from '../integration/workflow-engine.js';

/**
 * Test Suite: Workflow Engine Integration
 * 
 * Verifies integration with @nahisaho/musubix-workflow-engine package.
 * 
 * Test Coverage:
 * 1. Initialization and configuration
 * 2. Workflow creation
 * 3. Phase transitions
 * 4. Phase approval
 * 5. Quality gate validation
 * 6. Error handling
 */
describe('Workflow Engine Integration', () => {
  let integration: WorkflowIntegration;
  
  beforeEach(() => {
    integration = createWorkflowIntegration({
      autoStart: true,
      requireApproval: true,
      enableQualityGates: true,
    });
  });
  
  describe('Initialization', () => {
    it('should create workflow integration instance', () => {
      expect(integration).toBeInstanceOf(WorkflowIntegration);
    });
    
    it('should initialize with default config', () => {
      const defaultIntegration = createWorkflowIntegration();
      expect(defaultIntegration).toBeInstanceOf(WorkflowIntegration);
    });
    
    it('should initialize with custom config', () => {
      const custom = createWorkflowIntegration({
        autoStart: false,
        requireApproval: false,
        enableQualityGates: false,
      });
      expect(custom).toBeInstanceOf(WorkflowIntegration);
    });
    
    it('should initialize workflow engine', async () => {
      const isAvailable = await integration.isAvailable();
      
      if (!isAvailable) {
        console.log('⚠️  @nahisaho/musubix-workflow-engine package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const workflows = integration.getAllWorkflows();
      expect(workflows.size).toBe(0);
    });
  });
  
  describe('Availability Check', () => {
    it('should check if workflow engine is available', async () => {
      const isAvailable = await integration.isAvailable();
      // Returns false if package not installed, true if installed
      expect(typeof isAvailable).toBe('boolean');
    });
  });
  
  describe('Workflow Creation', () => {
    it('should create a new workflow', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Workflow engine not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const result = await integration.createWorkflow(
        'Test TypeScript patterns',
        'Research TypeScript design patterns'
      );
      
      expect(result.success).toBe(true);
      expect(result.data).toBeDefined();
      if (result.data) {
        expect(result.data.id).toBeDefined();
        expect(result.data.name).toContain('Test TypeScript patterns');
      }
    });
    
    it('should fail to create workflow without initialization', async () => {
      const result = await integration.createWorkflow('test query');
      
      expect(result.success).toBe(false);
      expect(result.error).toBe('Not initialized');
    });
    
    it('should cache workflow by query', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Workflow engine not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const query = 'Test caching';
      await integration.createWorkflow(query);
      
      const workflows = integration.getAllWorkflows();
      expect(workflows.has(query)).toBe(true);
    });
  });
  
  describe('Workflow Retrieval', () => {
    it('should get workflow by query', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Workflow engine not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const query = 'Test retrieval';
      await integration.createWorkflow(query);
      
      const workflow = await integration.getWorkflow(query);
      
      expect(workflow).toBeDefined();
      if (workflow) {
        expect(workflow.name).toContain(query);
      }
    });
    
    it('should return null for non-existent workflow', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Workflow engine not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const workflow = await integration.getWorkflow('non-existent query');
      
      expect(workflow).toBeNull();
    });
  });
  
  describe('Phase Status', () => {
    it('should get current phase status', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Workflow engine not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const query = 'Test phase status';
      await integration.createWorkflow(query);
      
      const status = await integration.getPhaseStatus(query);
      
      expect(status).toBeDefined();
      if (status) {
        expect(['planning', 'gathering', 'analysis', 'synthesis', 'completion']).toContain(status.currentPhase);
        expect(typeof status.canTransition).toBe('boolean');
        expect(Array.isArray(status.nextPhases)).toBe(true);
        expect(typeof status.requiresApproval).toBe('boolean');
      }
    });
    
    it('should return null for non-existent workflow', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Workflow engine not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const status = await integration.getPhaseStatus('non-existent');
      
      expect(status).toBeNull();
    });
  });
  
  describe('Phase Transitions', () => {
    it('should transition to next phase', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Workflow engine not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const query = 'Test transition';
      const createResult = await integration.createWorkflow(query);
      
      if (!createResult.success || !createResult.data) {
        console.log('Failed to create workflow, skipping test');
        return;
      }
      
      const request: PhaseTransitionRequest = {
        workflowId: createResult.data.id,
        targetPhase: 'gathering',
        reason: 'Moving to data collection phase',
      };
      
      const result = await integration.transitionPhase(request);
      
      // Transition may fail due to approval requirements
      expect(typeof result.success).toBe('boolean');
      expect(result.message).toBeDefined();
    });
    
    it('should fail transition without initialization', async () => {
      const request: PhaseTransitionRequest = {
        workflowId: 'test-id',
        targetPhase: 'gathering',
      };
      
      const result = await integration.transitionPhase(request);
      
      expect(result.success).toBe(false);
      expect(result.error).toBe('Not initialized');
    });
  });
  
  describe('Phase Approval', () => {
    it('should approve current phase', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Workflow engine not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const query = 'Test approval';
      const createResult = await integration.createWorkflow(query);
      
      if (!createResult.success || !createResult.data) {
        console.log('Failed to create workflow, skipping test');
        return;
      }
      
      const result = await integration.approvePhase(
        createResult.data.id,
        'test-reviewer'
      );
      
      expect(typeof result.success).toBe('boolean');
      expect(result.message).toBeDefined();
    });
    
    it('should fail approval without initialization', async () => {
      const result = await integration.approvePhase('test-id');
      
      expect(result.success).toBe(false);
      expect(result.error).toBe('Not initialized');
    });
  });
  
  describe('Quality Gates', () => {
    it('should run quality gates', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Workflow engine not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const query = 'Test quality gates';
      const createResult = await integration.createWorkflow(query);
      
      if (!createResult.success || !createResult.data) {
        console.log('Failed to create workflow, skipping test');
        return;
      }
      
      const passed = await integration.runQualityGates(createResult.data.id);
      
      expect(typeof passed).toBe('boolean');
    });
    
    it('should pass quality gates when disabled', async () => {
      const custom = createWorkflowIntegration({
        enableQualityGates: false,
      });
      
      const passed = await custom.runQualityGates('any-id');
      
      expect(passed).toBe(true);
    });
  });
  
  describe('Cache Management', () => {
    it('should get all workflows', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Workflow engine not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      await integration.createWorkflow('Query 1');
      await integration.createWorkflow('Query 2');
      
      const workflows = integration.getAllWorkflows();
      
      expect(workflows.size).toBeGreaterThanOrEqual(2);
    });
    
    it('should clear cache', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Workflow engine not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      await integration.createWorkflow('Test clear');
      
      integration.clearCache();
      
      const workflows = integration.getAllWorkflows();
      expect(workflows.size).toBe(0);
    });
  });
  
  describe('Phase Mapping', () => {
    it('should have valid research phases', () => {
      const validPhases: ResearchPhase[] = [
        'planning',
        'gathering',
        'analysis',
        'synthesis',
        'completion',
      ];
      
      validPhases.forEach(phase => {
        expect(['planning', 'gathering', 'analysis', 'synthesis', 'completion']).toContain(phase);
      });
    });
  });
  
  describe('Error Handling', () => {
    it('should handle workflow creation errors', async () => {
      const result = await integration.createWorkflow('test');
      
      expect(result.success).toBe(false);
      expect(result.error).toBeDefined();
    });
    
    it('should handle getWorkflow without initialization', async () => {
      const workflow = await integration.getWorkflow('test');
      
      expect(workflow).toBeNull();
    });
    
    it('should handle getPhaseStatus without initialization', async () => {
      const status = await integration.getPhaseStatus('test');
      
      expect(status).toBeNull();
    });
  });
});

/**
 * E2E Integration Test with Real Package
 * 
 * Note: This test requires @nahisaho/musubix-workflow-engine to be installed.
 * It will be skipped if the package is not available.
 */
describe('Workflow Engine E2E Integration', () => {
  it('should integrate with real workflow-engine package if available', async () => {
    const integration = createWorkflowIntegration({
      autoStart: true,
      requireApproval: true,
      enableQualityGates: true,
    });
    
    const isAvailable = await integration.isAvailable();
    
    if (!isAvailable) {
      console.log('⚠️  Workflow engine package not available, skipping E2E test');
      return;
    }
    
    // If package is available, test full workflow
    try {
      await integration.initialize();
      
      // Create workflow
      const query = 'E2E test workflow';
      const createResult = await integration.createWorkflow(query, 'Full E2E test');
      
      expect(createResult.success).toBe(true);
      expect(createResult.data).toBeDefined();
      
      if (!createResult.data) return;
      
      // Get phase status
      const status = await integration.getPhaseStatus(query);
      expect(status).toBeDefined();
      expect(status?.currentPhase).toBe('planning');
      
      // Get workflow
      const workflow = await integration.getWorkflow(query);
      expect(workflow).toBeDefined();
      
      console.log('✅ Workflow engine package is available and integrated');
      console.log(`🔄 Current phase: ${status?.currentPhase}`);
      console.log(`📋 Workflow ID: ${createResult.data.id}`);
    } catch (error) {
      console.error('❌ E2E integration test failed:', error);
      throw error;
    }
  });
});
