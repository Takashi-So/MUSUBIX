/**
 * Status Transition Test Generator Tests
 *
 * @module codegen/status-transition-test-generator.test
 */

import { describe, it, expect } from 'vitest';
import {
  StatusTransitionTestGenerator,
  generateStatusTransitionTests,
} from './status-transition-test-generator.js';
import type { StatusMachineSpec } from './status-transition-generator.js';

describe('StatusTransitionTestGenerator', () => {
  describe('generate', () => {
    it('should generate basic test code', () => {
      const spec: StatusMachineSpec = {
        name: 'Order',
        statuses: [
          { name: 'draft', isInitial: true },
          { name: 'pending' },
          { name: 'confirmed', isTerminal: true },
        ],
        transitions: [
          { from: 'draft', to: 'pending' },
          { from: 'pending', to: 'confirmed' },
        ],
      };

      const generator = new StatusTransitionTestGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain("import { describe, it, expect } from 'vitest';");
      expect(result.code).toContain("describe('OrderStatus Transitions'");
      expect(result.code).toContain('canTransitionOrderStatus');
      expect(result.fileName).toBe('order-status.test.ts');
    });

    it('should generate valid transition tests', () => {
      const spec: StatusMachineSpec = {
        name: 'Task',
        statuses: [{ name: 'todo' }, { name: 'done' }],
        transitions: [{ from: 'todo', to: 'done' }],
      };

      const generator = new StatusTransitionTestGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain("describe('valid transitions'");
      expect(result.code).toContain("from: 'todo', to: 'done'");
      expect(result.validTransitionTests).toBe(1);
    });

    it('should generate invalid transition tests', () => {
      const spec: StatusMachineSpec = {
        name: 'Item',
        statuses: [{ name: 'active' }, { name: 'inactive' }, { name: 'deleted' }],
        transitions: [
          { from: 'active', to: 'inactive' },
          { from: 'inactive', to: 'deleted' },
        ],
      };

      const generator = new StatusTransitionTestGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain("describe('invalid transitions'");
      // active -> deleted is invalid
      expect(result.code).toContain("from: 'active', to: 'deleted'");
      expect(result.invalidTransitionTests).toBeGreaterThan(0);
    });

    it('should use table-driven tests by default', () => {
      const spec: StatusMachineSpec = {
        name: 'Ticket',
        statuses: [{ name: 'open' }, { name: 'closed' }],
        transitions: [{ from: 'open', to: 'closed' }],
      };

      const generator = new StatusTransitionTestGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('it.each(validCases)');
    });

    it('should generate individual tests when useTableDrivenTests is false', () => {
      const spec: StatusMachineSpec = {
        name: 'Request',
        statuses: [{ name: 'new' }, { name: 'approved' }],
        transitions: [{ from: 'new', to: 'approved' }],
      };

      const generator = new StatusTransitionTestGenerator({ useTableDrivenTests: false });
      const result = generator.generate(spec);

      expect(result.code).not.toContain('it.each');
      expect(result.code).toContain("it('should allow new -> approved'");
    });

    it('should include edge case tests by default', () => {
      const spec: StatusMachineSpec = {
        name: 'Project',
        statuses: [
          { name: 'planning', isInitial: true },
          { name: 'active' },
          { name: 'completed', isTerminal: true },
        ],
        transitions: [
          { from: 'planning', to: 'active' },
          { from: 'active', to: 'completed' },
        ],
      };

      const generator = new StatusTransitionTestGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain("describe('edge cases'");
      expect(result.code).toContain('should reject self-transition');
      expect(result.code).toContain('no transitions from terminal status');
    });

    it('should skip edge case tests when disabled', () => {
      const spec: StatusMachineSpec = {
        name: 'Simple',
        statuses: [{ name: 'a' }, { name: 'b' }],
        transitions: [{ from: 'a', to: 'b' }],
      };

      const generator = new StatusTransitionTestGenerator({ includeEdgeCases: false });
      const result = generator.generate(spec);

      expect(result.code).not.toContain("describe('edge cases'");
    });

    it('should support jest framework', () => {
      const spec: StatusMachineSpec = {
        name: 'Unit',
        statuses: [{ name: 'pending' }, { name: 'done' }],
        transitions: [{ from: 'pending', to: 'done' }],
      };

      const generator = new StatusTransitionTestGenerator({ testFramework: 'jest' });
      const result = generator.generate(spec);

      expect(result.code).toContain("import { describe, it, expect } from '@jest/globals';");
    });

    it('should include JSDoc comments by default', () => {
      const spec: StatusMachineSpec = {
        name: 'Workflow',
        requirementId: 'REQ-WF-001',
        statuses: [{ name: 'start' }, { name: 'end' }],
        transitions: [{ from: 'start', to: 'end' }],
      };

      const generator = new StatusTransitionTestGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('* Workflow Status Transition Tests');
      expect(result.code).toContain('@pattern BP-TEST-005');
      expect(result.code).toContain('@requirement REQ-WF-001');
    });

    it('should skip JSDoc when disabled', () => {
      const spec: StatusMachineSpec = {
        name: 'NoDoc',
        statuses: [{ name: 'x' }, { name: 'y' }],
        transitions: [{ from: 'x', to: 'y' }],
      };

      const generator = new StatusTransitionTestGenerator({ includeJSDoc: false });
      const result = generator.generate(spec);

      expect(result.code).not.toContain('/**');
    });

    it('should count test cases correctly', () => {
      const spec: StatusMachineSpec = {
        name: 'Counter',
        statuses: [
          { name: 'a', isInitial: true },
          { name: 'b' },
          { name: 'c', isTerminal: true },
        ],
        transitions: [
          { from: 'a', to: 'b' },
          { from: 'b', to: 'c' },
        ],
      };

      const generator = new StatusTransitionTestGenerator();
      const result = generator.generate(spec);

      // 2 valid + (3*3-3-2)=4 invalid + 4 edge cases
      expect(result.validTransitionTests).toBe(2);
      expect(result.invalidTransitionTests).toBe(4);
      expect(result.testCount).toBeGreaterThanOrEqual(2 + 4);
    });

    it('should generate imports for status module', () => {
      const spec: StatusMachineSpec = {
        name: 'UserAccount',
        statuses: [{ name: 'active' }, { name: 'suspended' }],
        transitions: [{ from: 'active', to: 'suspended' }],
      };

      const generator = new StatusTransitionTestGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain("from './user-account-status.js'");
      expect(result.code).toContain('UserAccountStatus');
      expect(result.code).toContain('canTransitionUserAccountStatus');
      expect(result.code).toContain('validUserAccountTransitions');
    });

    it('should test transition map completeness', () => {
      const spec: StatusMachineSpec = {
        name: 'Phase',
        statuses: [{ name: 'alpha' }, { name: 'beta' }, { name: 'release' }],
        transitions: [
          { from: 'alpha', to: 'beta' },
          { from: 'beta', to: 'release' },
        ],
      };

      const generator = new StatusTransitionTestGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('should have transitions defined for all statuses');
      expect(result.code).toContain('validPhaseTransitions[status]');
    });

    it('should handle status with no outgoing transitions', () => {
      const spec: StatusMachineSpec = {
        name: 'Leaf',
        statuses: [
          { name: 'root' },
          { name: 'terminal', isTerminal: true },
        ],
        transitions: [{ from: 'root', to: 'terminal' }],
      };

      const generator = new StatusTransitionTestGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain("getNextLeafStatuses('terminal')");
      expect(result.code).toContain('toHaveLength(0)');
    });
  });

  describe('generateStatusTransitionTests', () => {
    it('should work as convenience function', () => {
      const spec: StatusMachineSpec = {
        name: 'Quick',
        statuses: [{ name: 'on' }, { name: 'off' }],
        transitions: [
          { from: 'on', to: 'off' },
          { from: 'off', to: 'on' },
        ],
      };

      const result = generateStatusTransitionTests(spec);

      expect(result.code).toContain('QuickStatus');
      expect(result.validTransitionTests).toBe(2);
    });
  });
});
