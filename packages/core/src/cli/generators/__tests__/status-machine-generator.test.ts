/**
 * Status Machine Generator Tests
 *
 * @traceability TST-SCF-003
 * @see REQ-SCF-003, REQ-SCF-004
 * @see ADR-v3.3.0-001 - -sオプション構文決定
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  StatusMachineGenerator,
  createStatusMachineGenerator,
  type StatusMachineSpec,
  type StatusMachineGeneratorConfig,
} from '../status-machine-generator.js';

describe('StatusMachineGenerator', () => {
  let generator: StatusMachineGenerator;
  let config: StatusMachineGeneratorConfig;

  beforeEach(() => {
    config = {
      domain: 'TEST',
      outputDir: '/tmp/test-project',
      generateTests: true,
      generateEnum: false,
    };
    generator = createStatusMachineGenerator(config);
  });

  describe('parseStatusOption (ADR-v3.3.0-001)', () => {
    it('should parse single entity with initial status', () => {
      const result = StatusMachineGenerator.parseStatusOption('Order=draft');

      expect(result.get('Order')).toBe('draft');
    });

    it('should parse multiple entities with initial statuses', () => {
      const result = StatusMachineGenerator.parseStatusOption('Order=draft,Task=pending');

      expect(result.get('Order')).toBe('draft');
      expect(result.get('Task')).toBe('pending');
    });

    it('should handle entity without initial status', () => {
      const result = StatusMachineGenerator.parseStatusOption('Order');

      expect(result.has('Order')).toBe(true);
      expect(result.get('Order')).toBe('');
    });

    it('should handle mixed format', () => {
      const result = StatusMachineGenerator.parseStatusOption('Order=draft,Task,Item=active');

      expect(result.get('Order')).toBe('draft');
      expect(result.get('Task')).toBe('');
      expect(result.get('Item')).toBe('active');
    });

    it('should handle empty string', () => {
      const result = StatusMachineGenerator.parseStatusOption('');

      expect(result.size).toBe(0);
    });

    it('should handle whitespace', () => {
      const result = StatusMachineGenerator.parseStatusOption('  Order = draft , Task = pending  ');

      expect(result.get('Order')).toBe('draft');
      expect(result.get('Task')).toBe('pending');
    });
  });

  describe('generate', () => {
    it('should generate Status Machine file for Order', async () => {
      const specs: StatusMachineSpec[] = [
        { entityName: 'Order' },
      ];

      const files = await generator.generate(specs);

      expect(files).toHaveLength(1);
      expect(files[0].path).toContain('order-status.ts');
      expect(files[0].type).toBe('status-machine');
      expect(files[0].content).toContain('type OrderStatus');
      expect(files[0].content).toContain('orderStatusList');
      expect(files[0].content).toContain('validOrderTransitions');
      expect(files[0].content).toContain('canTransitionOrder');
      expect(files[0].content).toContain('transitionOrder');
    });

    it('should generate with custom statuses', async () => {
      const specs: StatusMachineSpec[] = [
        {
          entityName: 'Task',
          statuses: ['todo', 'in_progress', 'review', 'done'],
        },
      ];

      const files = await generator.generate(specs);

      expect(files[0].content).toContain("'todo'");
      expect(files[0].content).toContain("'in_progress'");
      expect(files[0].content).toContain("'review'");
      expect(files[0].content).toContain("'done'");
    });

    it('should generate with custom initial status', async () => {
      const specs: StatusMachineSpec[] = [
        {
          entityName: 'Order',
          initialStatus: 'pending',
          statuses: ['pending', 'confirmed', 'shipped', 'delivered'],
        },
      ];

      const files = await generator.generate(specs);

      expect(files[0].content).toContain("orderDefaultStatus: OrderStatus = 'pending'");
    });

    it('should generate with custom transitions', async () => {
      const specs: StatusMachineSpec[] = [
        {
          entityName: 'Order',
          statuses: ['draft', 'active', 'completed'],
          transitions: [
            { from: 'draft', to: ['active'] },
            { from: 'active', to: ['completed'] },
            { from: 'completed', to: [] },
          ],
        },
      ];

      const files = await generator.generate(specs);

      expect(files[0].content).toContain("'draft': ['active']");
      expect(files[0].content).toContain("'active': ['completed']");
      expect(files[0].content).toContain("'completed': []");
    });

    it('should generate multiple Status Machines', async () => {
      const specs: StatusMachineSpec[] = [
        { entityName: 'Order' },
        { entityName: 'Task' },
      ];

      const files = await generator.generate(specs);

      expect(files).toHaveLength(2);
      expect(files.map(f => f.path)).toEqual(
        expect.arrayContaining([
          expect.stringContaining('order-status.ts'),
          expect.stringContaining('task-status.ts'),
        ])
      );
    });

    it('should handle empty specs array', async () => {
      const files = await generator.generate([]);
      expect(files).toHaveLength(0);
    });
  });

  describe('generateTests', () => {
    it('should generate test files when enabled', async () => {
      const specs: StatusMachineSpec[] = [
        { entityName: 'Order' },
      ];

      const files = await generator.generateTests(specs);

      expect(files).toHaveLength(1);
      expect(files[0].path).toContain('order-status.test.ts');
      expect(files[0].type).toBe('test');
      expect(files[0].content).toContain("describe('Order Status Machine'");
    });

    it('should not generate test files when disabled', async () => {
      const noTestConfig: StatusMachineGeneratorConfig = {
        ...config,
        generateTests: false,
      };
      const noTestGenerator = createStatusMachineGenerator(noTestConfig);

      const specs: StatusMachineSpec[] = [
        { entityName: 'Order' },
      ];

      const files = await noTestGenerator.generateTests(specs);
      expect(files).toHaveLength(0);
    });
  });

  describe('generateEnum option', () => {
    it('should generate enum when enabled', async () => {
      const enumConfig: StatusMachineGeneratorConfig = {
        ...config,
        generateEnum: true,
      };
      const enumGenerator = createStatusMachineGenerator(enumConfig);

      const specs: StatusMachineSpec[] = [
        { entityName: 'Order', statuses: ['draft', 'active'] },
      ];

      const files = await enumGenerator.generate(specs);

      expect(files[0].content).toContain('enum OrderStatusEnum');
      expect(files[0].content).toContain("Draft = 'draft'");
      expect(files[0].content).toContain("Active = 'active'");
    });

    it('should not generate enum when disabled', async () => {
      const specs: StatusMachineSpec[] = [
        { entityName: 'Order' },
      ];

      const files = await generator.generate(specs);

      expect(files[0].content).not.toContain('enum OrderStatusEnum');
    });
  });

  describe('getDefaultStatuses', () => {
    it('should return default statuses', () => {
      const statuses = generator.getDefaultStatuses('Order');

      expect(statuses).toContain('draft');
      expect(statuses).toContain('active');
      expect(statuses).toContain('completed');
      expect(statuses).toContain('cancelled');
    });
  });

  describe('getDefaultTransitions', () => {
    it('should generate default transitions', () => {
      const statuses = ['draft', 'active', 'completed', 'cancelled'];
      const transitions = generator.getDefaultTransitions(statuses);

      const draftTrans = transitions.find(t => t.from === 'draft');
      expect(draftTrans?.to).toContain('active');

      const activeTrans = transitions.find(t => t.from === 'active');
      expect(activeTrans?.to).toContain('completed');

      const completedTrans = transitions.find(t => t.from === 'completed');
      expect(completedTrans?.to).toHaveLength(0);
    });
  });

  describe('traceability', () => {
    it('should include traceability comment', async () => {
      const specs: StatusMachineSpec[] = [{ entityName: 'Order' }];
      const files = await generator.generate(specs);

      expect(files[0].content).toContain('@traceability REQ-SCF-003');
      expect(files[0].content).toContain('@domain TEST');
    });
  });
});
