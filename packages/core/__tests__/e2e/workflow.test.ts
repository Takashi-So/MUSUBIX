/**
 * E2E Integration Tests - MUSUBIX Workflow
 * 
 * End-to-end tests validating the complete SDD workflow
 * 
 * @see Article IX - Quality Assurance
 * @see TSK-054 - E2E Integration Tests
 */

import { describe, it, expect, beforeAll, afterAll, beforeEach } from 'vitest';

/**
 * Mock implementations for E2E testing
 * In production, these would be actual service imports
 */

// Requirement types
interface Requirement {
  id: string;
  title: string;
  description: string;
  type: 'functional' | 'non-functional' | 'constraint';
  priority: 'must' | 'should' | 'could' | 'wont';
  status: 'draft' | 'approved' | 'implemented' | 'verified';
  acceptanceCriteria: string[];
  traceability: {
    designRefs: string[];
    taskRefs: string[];
    testRefs: string[];
  };
}

// Design types
interface DesignDocument {
  id: string;
  type: 'c4-context' | 'c4-container' | 'c4-component' | 'adr';
  title: string;
  content: string;
  requirementRefs: string[];
  version: string;
}

// Task types
interface Task {
  id: string;
  title: string;
  description: string;
  status: 'pending' | 'in-progress' | 'completed' | 'blocked';
  requirementRef: string;
  designRef?: string;
  estimatedHours: number;
  actualHours?: number;
}

// Validation types
interface ValidationResult {
  valid: boolean;
  errors: Array<{ code: string; message: string; severity: 'error' | 'warning' }>;
  coverage: {
    requirements: number;
    design: number;
    tasks: number;
    tests: number;
  };
}

/**
 * Mock Services
 */
class MockRequirementsService {
  private requirements: Map<string, Requirement> = new Map();
  private counter = 0;

  create(req: Omit<Requirement, 'id' | 'status' | 'traceability'>): Requirement {
    const requirement: Requirement = {
      ...req,
      id: `REQ-${Date.now()}-${this.counter++}`,
      status: 'draft',
      traceability: {
        designRefs: [],
        taskRefs: [],
        testRefs: [],
      },
    };
    this.requirements.set(requirement.id, requirement);
    return requirement;
  }

  get(id: string): Requirement | undefined {
    return this.requirements.get(id);
  }

  getAll(): Requirement[] {
    return Array.from(this.requirements.values());
  }

  update(id: string, updates: Partial<Requirement>): Requirement | undefined {
    const req = this.requirements.get(id);
    if (!req) return undefined;
    const updated = { ...req, ...updates };
    this.requirements.set(id, updated);
    return updated;
  }

  approve(id: string): boolean {
    const req = this.requirements.get(id);
    if (!req) return false;
    req.status = 'approved';
    return true;
  }

  linkDesign(reqId: string, designId: string): boolean {
    const req = this.requirements.get(reqId);
    if (!req) return false;
    req.traceability.designRefs.push(designId);
    return true;
  }

  linkTask(reqId: string, taskId: string): boolean {
    const req = this.requirements.get(reqId);
    if (!req) return false;
    req.traceability.taskRefs.push(taskId);
    return true;
  }

  clear(): void {
    this.requirements.clear();
    this.counter = 0;
  }
}

class MockDesignService {
  private designs: Map<string, DesignDocument> = new Map();
  private counter = 0;

  create(design: Omit<DesignDocument, 'id' | 'version'>): DesignDocument {
    const doc: DesignDocument = {
      ...design,
      id: `DES-${Date.now()}-${this.counter++}`,
      version: '1.0.0',
    };
    this.designs.set(doc.id, doc);
    return doc;
  }

  get(id: string): DesignDocument | undefined {
    return this.designs.get(id);
  }

  getAll(): DesignDocument[] {
    return Array.from(this.designs.values());
  }

  getByRequirement(reqId: string): DesignDocument[] {
    return Array.from(this.designs.values()).filter((d) =>
      d.requirementRefs.includes(reqId)
    );
  }

  clear(): void {
    this.designs.clear();
    this.counter = 0;
  }
}

class MockTaskService {
  private tasks: Map<string, Task> = new Map();
  private counter = 0;

  create(task: Omit<Task, 'id' | 'status'>): Task {
    const newTask: Task = {
      ...task,
      id: `TSK-${Date.now()}-${this.counter++}`,
      status: 'pending',
    };
    this.tasks.set(newTask.id, newTask);
    return newTask;
  }

  get(id: string): Task | undefined {
    return this.tasks.get(id);
  }

  getAll(): Task[] {
    return Array.from(this.tasks.values());
  }

  getByRequirement(reqId: string): Task[] {
    return Array.from(this.tasks.values()).filter((t) => t.requirementRef === reqId);
  }

  updateStatus(id: string, status: Task['status']): boolean {
    const task = this.tasks.get(id);
    if (!task) return false;
    task.status = status;
    return true;
  }

  complete(id: string, actualHours: number): boolean {
    const task = this.tasks.get(id);
    if (!task) return false;
    task.status = 'completed';
    task.actualHours = actualHours;
    return true;
  }

  clear(): void {
    this.tasks.clear();
    this.counter = 0;
  }
}

class MockValidationService {
  constructor(
    private requirements: MockRequirementsService,
    private designs: MockDesignService,
    private tasks: MockTaskService
  ) {}

  validate(): ValidationResult {
    const reqs = this.requirements.getAll();
    const designs = this.designs.getAll();
    const tasks = this.tasks.getAll();

    const errors: ValidationResult['errors'] = [];

    // Check requirement coverage
    const reqsWithDesign = reqs.filter((r) => r.traceability.designRefs.length > 0);
    const reqsWithTasks = reqs.filter((r) => r.traceability.taskRefs.length > 0);

    // Check for orphan designs
    for (const design of designs) {
      if (design.requirementRefs.length === 0) {
        errors.push({
          code: 'ORPHAN_DESIGN',
          message: `Design ${design.id} has no requirement references`,
          severity: 'warning',
        });
      }
    }

    // Check for tasks without requirements
    for (const task of tasks) {
      const req = this.requirements.get(task.requirementRef);
      if (!req) {
        errors.push({
          code: 'ORPHAN_TASK',
          message: `Task ${task.id} references non-existent requirement ${task.requirementRef}`,
          severity: 'error',
        });
      }
    }

    // Check for incomplete traceability
    for (const req of reqs) {
      if (req.status === 'approved' && req.traceability.designRefs.length === 0) {
        errors.push({
          code: 'MISSING_DESIGN',
          message: `Approved requirement ${req.id} has no design references`,
          severity: 'warning',
        });
      }
      if (req.status === 'approved' && req.traceability.taskRefs.length === 0) {
        errors.push({
          code: 'MISSING_TASKS',
          message: `Approved requirement ${req.id} has no task references`,
          severity: 'warning',
        });
      }
    }

    const coverage = {
      requirements: reqs.length > 0 ? (reqsWithDesign.length / reqs.length) * 100 : 0,
      design: reqs.length > 0 ? (designs.length / reqs.length) * 100 : 0,
      tasks: reqs.length > 0 ? (reqsWithTasks.length / reqs.length) * 100 : 0,
      tests: 0, // Would be calculated from actual test coverage
    };

    return {
      valid: errors.filter((e) => e.severity === 'error').length === 0,
      errors,
      coverage,
    };
  }
}

/**
 * E2E Test Suite
 */
describe('MUSUBIX E2E Integration Tests', () => {
  let requirementsService: MockRequirementsService;
  let designService: MockDesignService;
  let taskService: MockTaskService;
  let validationService: MockValidationService;

  beforeAll(() => {
    // Initialize services
    requirementsService = new MockRequirementsService();
    designService = new MockDesignService();
    taskService = new MockTaskService();
    validationService = new MockValidationService(
      requirementsService,
      designService,
      taskService
    );
  });

  afterAll(() => {
    // Cleanup
    requirementsService.clear();
    designService.clear();
    taskService.clear();
  });

  beforeEach(() => {
    // Clear state between tests
    requirementsService.clear();
    designService.clear();
    taskService.clear();
  });

  describe('Complete SDD Workflow', () => {
    it('should complete full workflow from requirement to implementation', async () => {
      // Step 1: Create requirement (Article II)
      const requirement = requirementsService.create({
        title: 'User Authentication',
        description: 'System shall support user authentication with email and password',
        type: 'functional',
        priority: 'must',
        acceptanceCriteria: [
          'User can register with email',
          'User can login with credentials',
          'System validates password strength',
        ],
      });

      expect(requirement).toBeDefined();
      expect(requirement.id).toMatch(/^REQ-/);
      expect(requirement.status).toBe('draft');

      // Step 2: Approve requirement
      const approved = requirementsService.approve(requirement.id);
      expect(approved).toBe(true);
      expect(requirementsService.get(requirement.id)?.status).toBe('approved');

      // Step 3: Create design (Article III)
      const design = designService.create({
        type: 'c4-component',
        title: 'Authentication Component',
        content: 'Component diagram for authentication...',
        requirementRefs: [requirement.id],
      });

      expect(design).toBeDefined();
      expect(design.id).toMatch(/^DES-/);

      // Link design to requirement
      requirementsService.linkDesign(requirement.id, design.id);

      // Step 4: Create tasks (Article IV)
      const tasks = [
        taskService.create({
          title: 'Implement registration endpoint',
          description: 'Create POST /auth/register endpoint',
          requirementRef: requirement.id,
          designRef: design.id,
          estimatedHours: 4,
        }),
        taskService.create({
          title: 'Implement login endpoint',
          description: 'Create POST /auth/login endpoint',
          requirementRef: requirement.id,
          designRef: design.id,
          estimatedHours: 4,
        }),
        taskService.create({
          title: 'Add password validation',
          description: 'Implement password strength checker',
          requirementRef: requirement.id,
          estimatedHours: 2,
        }),
      ];

      expect(tasks).toHaveLength(3);

      // Link tasks to requirement
      for (const task of tasks) {
        requirementsService.linkTask(requirement.id, task.id);
      }

      // Step 5: Complete tasks
      for (const task of tasks) {
        taskService.updateStatus(task.id, 'in-progress');
        taskService.complete(task.id, task.estimatedHours);
      }

      // Step 6: Validate (Article IX)
      const validation = validationService.validate();

      expect(validation.valid).toBe(true);
      expect(validation.coverage.requirements).toBe(100);
      expect(validation.coverage.tasks).toBe(100);
    });

    it('should detect incomplete traceability', () => {
      // Create requirement without design or tasks
      const requirement = requirementsService.create({
        title: 'Orphan Requirement',
        description: 'This requirement has no design or tasks',
        type: 'functional',
        priority: 'should',
        acceptanceCriteria: ['Some criteria'],
      });

      requirementsService.approve(requirement.id);

      const validation = validationService.validate();

      expect(validation.valid).toBe(true); // No errors, only warnings
      expect(validation.errors).toContainEqual(
        expect.objectContaining({
          code: 'MISSING_DESIGN',
          severity: 'warning',
        })
      );
      expect(validation.errors).toContainEqual(
        expect.objectContaining({
          code: 'MISSING_TASKS',
          severity: 'warning',
        })
      );
    });

    it('should detect orphan designs', () => {
      // Create design without requirement reference
      designService.create({
        type: 'c4-context',
        title: 'Orphan Design',
        content: 'Design without requirement',
        requirementRefs: [],
      });

      const validation = validationService.validate();

      expect(validation.errors).toContainEqual(
        expect.objectContaining({
          code: 'ORPHAN_DESIGN',
          severity: 'warning',
        })
      );
    });

    it('should detect orphan tasks', () => {
      // Create task with non-existent requirement
      taskService.create({
        title: 'Orphan Task',
        description: 'Task with invalid requirement reference',
        requirementRef: 'REQ-NONEXISTENT',
        estimatedHours: 2,
      });

      const validation = validationService.validate();

      expect(validation.valid).toBe(false);
      expect(validation.errors).toContainEqual(
        expect.objectContaining({
          code: 'ORPHAN_TASK',
          severity: 'error',
        })
      );
    });
  });

  describe('Requirements Phase (Article II)', () => {
    it('should create EARS-compliant requirement', () => {
      const requirement = requirementsService.create({
        title: 'Data Export',
        description: 'When user requests export, the system shall generate CSV file within 30 seconds',
        type: 'functional',
        priority: 'must',
        acceptanceCriteria: [
          'Export button triggers generation',
          'CSV format is valid',
          'Generation completes within 30s',
        ],
      });

      expect(requirement.description).toMatch(/when.*shall/i);
      expect(requirement.acceptanceCriteria.length).toBeGreaterThan(0);
    });

    it('should handle requirement updates', () => {
      const requirement = requirementsService.create({
        title: 'Initial Title',
        description: 'Initial description',
        type: 'functional',
        priority: 'should',
        acceptanceCriteria: [],
      });

      const updated = requirementsService.update(requirement.id, {
        title: 'Updated Title',
        priority: 'must',
      });

      expect(updated?.title).toBe('Updated Title');
      expect(updated?.priority).toBe('must');
    });
  });

  describe('Design Phase (Article III)', () => {
    it('should create C4 design documents', () => {
      const requirement = requirementsService.create({
        title: 'API Gateway',
        description: 'System shall provide API gateway for external access',
        type: 'functional',
        priority: 'must',
        acceptanceCriteria: ['Gateway handles routing'],
      });

      const contextDiagram = designService.create({
        type: 'c4-context',
        title: 'System Context',
        content: 'Context level view...',
        requirementRefs: [requirement.id],
      });

      const containerDiagram = designService.create({
        type: 'c4-container',
        title: 'Container View',
        content: 'Container level view...',
        requirementRefs: [requirement.id],
      });

      expect(contextDiagram.type).toBe('c4-context');
      expect(containerDiagram.type).toBe('c4-container');

      const designs = designService.getByRequirement(requirement.id);
      expect(designs.length).toBeGreaterThanOrEqual(1);
    });

    it('should create ADR documents', () => {
      const adr = designService.create({
        type: 'adr',
        title: 'ADR-001: Use TypeScript',
        content: '# Decision: Use TypeScript\n\n## Context...',
        requirementRefs: [],
      });

      expect(adr.type).toBe('adr');
      expect(adr.title).toContain('ADR');
    });
  });

  describe('Task Phase (Article IV)', () => {
    it('should track task lifecycle', () => {
      const requirement = requirementsService.create({
        title: 'Feature X',
        description: 'Implement feature X',
        type: 'functional',
        priority: 'must',
        acceptanceCriteria: [],
      });

      const task = taskService.create({
        title: 'Implement Feature X',
        description: 'Implementation details',
        requirementRef: requirement.id,
        estimatedHours: 8,
      });

      expect(task.status).toBe('pending');

      taskService.updateStatus(task.id, 'in-progress');
      expect(taskService.get(task.id)?.status).toBe('in-progress');

      taskService.complete(task.id, 6);
      const completed = taskService.get(task.id);
      expect(completed?.status).toBe('completed');
      expect(completed?.actualHours).toBe(6);
    });

    it('should calculate task efficiency', () => {
      const requirement = requirementsService.create({
        title: 'Feature Y',
        description: 'Implement feature Y',
        type: 'functional',
        priority: 'should',
        acceptanceCriteria: [],
      });

      const task = taskService.create({
        title: 'Task Y',
        description: 'Task description',
        requirementRef: requirement.id,
        estimatedHours: 4,
      });

      taskService.complete(task.id, 3);

      const completed = taskService.get(task.id);
      const efficiency =
        ((completed?.estimatedHours ?? 0) / (completed?.actualHours ?? 1)) * 100;

      expect(efficiency).toBeGreaterThan(100); // Under estimate is > 100%
    });
  });

  describe('Validation Phase (Article IX)', () => {
    it('should calculate coverage metrics', () => {
      // Create multiple requirements with varying coverage
      const req1 = requirementsService.create({
        title: 'Requirement 1',
        description: 'Description 1',
        type: 'functional',
        priority: 'must',
        acceptanceCriteria: [],
      });

      const req2 = requirementsService.create({
        title: 'Requirement 2',
        description: 'Description 2',
        type: 'functional',
        priority: 'should',
        acceptanceCriteria: [],
      });

      // Only req1 has design
      const design = designService.create({
        type: 'c4-component',
        title: 'Design 1',
        content: 'Content',
        requirementRefs: [req1.id],
      });

      requirementsService.linkDesign(req1.id, design.id);

      // Only req1 has task
      const task = taskService.create({
        title: 'Task 1',
        description: 'Description',
        requirementRef: req1.id,
        estimatedHours: 2,
      });

      requirementsService.linkTask(req1.id, task.id);

      const validation = validationService.validate();

      expect(validation.coverage.requirements).toBe(50); // 1 of 2 has design
      expect(validation.coverage.tasks).toBe(50); // 1 of 2 has tasks
    });

    it('should report validation errors with severity', () => {
      // Create invalid state
      taskService.create({
        title: 'Invalid Task',
        description: 'Task with bad reference',
        requirementRef: 'REQ-INVALID',
        estimatedHours: 1,
      });

      const validation = validationService.validate();

      const errorCount = validation.errors.filter((e) => e.severity === 'error').length;
      const warningCount = validation.errors.filter((e) => e.severity === 'warning').length;

      expect(errorCount).toBeGreaterThan(0);
      expect(validation.valid).toBe(false);
    });
  });

  describe('Traceability (Article V)', () => {
    it('should maintain bidirectional traceability', () => {
      // Create requirement
      const requirement = requirementsService.create({
        title: 'Traceable Requirement',
        description: 'Requirement with full traceability',
        type: 'functional',
        priority: 'must',
        acceptanceCriteria: ['Criteria 1', 'Criteria 2'],
      });

      // Create design linked to requirement
      const design = designService.create({
        type: 'c4-component',
        title: 'Traceable Design',
        content: 'Design content',
        requirementRefs: [requirement.id],
      });

      // Link requirement to design
      requirementsService.linkDesign(requirement.id, design.id);

      // Create task linked to requirement and design
      const task = taskService.create({
        title: 'Traceable Task',
        description: 'Task description',
        requirementRef: requirement.id,
        designRef: design.id,
        estimatedHours: 4,
      });

      // Link requirement to task
      requirementsService.linkTask(requirement.id, task.id);

      // Verify traceability
      const req = requirementsService.get(requirement.id);
      expect(req?.traceability.designRefs).toContain(design.id);
      expect(req?.traceability.taskRefs).toContain(task.id);

      const des = designService.get(design.id);
      expect(des?.requirementRefs).toContain(requirement.id);

      const tsk = taskService.get(task.id);
      expect(tsk?.requirementRef).toBe(requirement.id);
      expect(tsk?.designRef).toBe(design.id);
    });
  });

  describe('Multi-requirement Workflow', () => {
    it('should handle multiple requirements with dependencies', () => {
      // Create parent requirement
      const authReq = requirementsService.create({
        title: 'User Authentication',
        description: 'System shall authenticate users',
        type: 'functional',
        priority: 'must',
        acceptanceCriteria: ['Login works'],
      });

      // Create dependent requirement
      const profileReq = requirementsService.create({
        title: 'User Profile',
        description: 'System shall display user profile after authentication',
        type: 'functional',
        priority: 'should',
        acceptanceCriteria: ['Profile displays after login'],
      });

      // Create shared design
      const userDesign = designService.create({
        type: 'c4-container',
        title: 'User Management Container',
        content: 'User management design',
        requirementRefs: [authReq.id, profileReq.id],
      });

      requirementsService.linkDesign(authReq.id, userDesign.id);
      requirementsService.linkDesign(profileReq.id, userDesign.id);

      // Create tasks for each requirement
      const authTask = taskService.create({
        title: 'Implement Auth',
        description: 'Auth implementation',
        requirementRef: authReq.id,
        estimatedHours: 8,
      });

      const profileTask = taskService.create({
        title: 'Implement Profile',
        description: 'Profile implementation',
        requirementRef: profileReq.id,
        estimatedHours: 4,
      });

      requirementsService.linkTask(authReq.id, authTask.id);
      requirementsService.linkTask(profileReq.id, profileTask.id);

      // Verify design serves multiple requirements
      const designs = designService.getAll();
      const sharedDesign = designs.find((d) => d.requirementRefs.length > 1);
      expect(sharedDesign).toBeDefined();
      expect(sharedDesign?.requirementRefs).toContain(authReq.id);
      expect(sharedDesign?.requirementRefs).toContain(profileReq.id);

      // Validate
      const validation = validationService.validate();
      expect(validation.valid).toBe(true);
      expect(validation.coverage.requirements).toBe(100);
    });
  });
});

/**
 * Performance E2E Tests
 */
describe('MUSUBIX Performance E2E Tests', () => {
  let requirementsService: MockRequirementsService;
  let designService: MockDesignService;
  let taskService: MockTaskService;

  beforeEach(() => {
    requirementsService = new MockRequirementsService();
    designService = new MockDesignService();
    taskService = new MockTaskService();
  });

  it('should handle large number of requirements efficiently', () => {
    const startTime = Date.now();
    const count = 100;

    // Create many requirements
    for (let i = 0; i < count; i++) {
      requirementsService.create({
        title: `Requirement ${i}`,
        description: `Description for requirement ${i}`,
        type: 'functional',
        priority: 'should',
        acceptanceCriteria: [`Criteria ${i}`],
      });
    }

    const createTime = Date.now() - startTime;
    expect(createTime).toBeLessThan(1000); // Should complete in < 1s

    // Query all requirements
    const queryStart = Date.now();
    const all = requirementsService.getAll();
    const queryTime = Date.now() - queryStart;

    expect(all).toHaveLength(count);
    expect(queryTime).toBeLessThan(100); // Query should be fast
  });

  it('should validate large project efficiently', () => {
    // Create 50 requirements with full traceability
    const requirements: Requirement[] = [];
    for (let i = 0; i < 50; i++) {
      const req = requirementsService.create({
        title: `Requirement ${i}`,
        description: `Description ${i}`,
        type: 'functional',
        priority: 'should',
        acceptanceCriteria: [],
      });
      requirements.push(req);

      // Create design for each
      const design = designService.create({
        type: 'c4-component',
        title: `Design ${i}`,
        content: 'Content',
        requirementRefs: [req.id],
      });
      requirementsService.linkDesign(req.id, design.id);

      // Create tasks for each
      const task = taskService.create({
        title: `Task ${i}`,
        description: 'Description',
        requirementRef: req.id,
        estimatedHours: 4,
      });
      requirementsService.linkTask(req.id, task.id);
    }

    // Validate
    const validationService = new MockValidationService(
      requirementsService,
      designService,
      taskService
    );

    const startTime = Date.now();
    const result = validationService.validate();
    const validationTime = Date.now() - startTime;

    expect(result.valid).toBe(true);
    expect(validationTime).toBeLessThan(500); // Validation should be fast
  });
});
