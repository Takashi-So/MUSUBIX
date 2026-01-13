/**
 * Status Transition Generator Tests
 *
 * @module codegen/status-transition-generator.test
 */

import { describe, it, expect } from 'vitest';
import {
  StatusTransitionGenerator,
  generateStatusTransitions,
  parseStatusMachineSpec,
  StatusMachineSpec,
} from './status-transition-generator.js';

describe('StatusTransitionGenerator', () => {
  describe('generate', () => {
    it('should generate basic status transition code', () => {
      const spec: StatusMachineSpec = {
        name: 'Order',
        statuses: [
          { name: 'draft', isInitial: true },
          { name: 'pending' },
          { name: 'confirmed' },
          { name: 'cancelled', isTerminal: true },
        ],
        transitions: [
          { from: 'draft', to: 'pending' },
          { from: 'pending', to: 'confirmed' },
          { from: 'pending', to: 'cancelled' },
          { from: 'confirmed', to: 'cancelled' },
        ],
      };

      const generator = new StatusTransitionGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain("export type OrderStatus = 'draft' | 'pending' | 'confirmed' | 'cancelled';");
      expect(result.code).toContain('validOrderTransitions');
      expect(result.code).toContain("'draft': ['pending']");
      expect(result.code).toContain("'pending': ['confirmed', 'cancelled']");
      expect(result.statusCount).toBe(4);
      expect(result.transitionCount).toBe(4);
    });

    it('should generate enum type when useUnionType is false', () => {
      const spec: StatusMachineSpec = {
        name: 'Task',
        statuses: [
          { name: 'todo', description: 'Initial state' },
          { name: 'in_progress' },
          { name: 'done' },
        ],
        transitions: [
          { from: 'todo', to: 'in_progress' },
          { from: 'in_progress', to: 'done' },
        ],
      };

      const generator = new StatusTransitionGenerator({ useUnionType: false });
      const result = generator.generate(spec);

      expect(result.code).toContain('export enum TaskStatus {');
      expect(result.code).toContain("Todo = 'todo'");
      expect(result.code).toContain("InProgress = 'in_progress'");
      expect(result.code).toContain("Done = 'done'");
    });

    it('should generate validator function', () => {
      const spec: StatusMachineSpec = {
        name: 'Ticket',
        statuses: [{ name: 'open' }, { name: 'closed' }],
        transitions: [{ from: 'open', to: 'closed' }],
      };

      const generator = new StatusTransitionGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('export function canTransitionTicketStatus(from: TicketStatus, to: TicketStatus): boolean');
      expect(result.code).toContain('return validTicketTransitions[from].includes(to)');
    });

    it('should skip validator when generateValidator is false', () => {
      const spec: StatusMachineSpec = {
        name: 'Item',
        statuses: [{ name: 'active' }, { name: 'inactive' }],
        transitions: [{ from: 'active', to: 'inactive' }],
      };

      const generator = new StatusTransitionGenerator({ generateValidator: false });
      const result = generator.generate(spec);

      expect(result.code).not.toContain('canTransitionItemStatus');
    });

    it('should generate initial status helper', () => {
      const spec: StatusMachineSpec = {
        name: 'Member',
        statuses: [
          { name: 'pending', isInitial: true },
          { name: 'active' },
        ],
        transitions: [{ from: 'pending', to: 'active' }],
      };

      const generator = new StatusTransitionGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('export function getInitialMemberStatus(): MemberStatus');
      expect(result.code).toContain("return 'pending'");
      expect(result.initialStatus).toBe('pending');
    });

    it('should generate terminal status helper', () => {
      const spec: StatusMachineSpec = {
        name: 'Project',
        statuses: [
          { name: 'planning' },
          { name: 'completed', isTerminal: true },
          { name: 'cancelled', isTerminal: true },
        ],
        transitions: [
          { from: 'planning', to: 'completed' },
          { from: 'planning', to: 'cancelled' },
        ],
      };

      const generator = new StatusTransitionGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('export function isTerminalProjectStatus(status: ProjectStatus): boolean');
      expect(result.terminalStatuses).toEqual(['completed', 'cancelled']);
    });

    it('should generate getNextStatuses helper', () => {
      const spec: StatusMachineSpec = {
        name: 'Document',
        statuses: [{ name: 'draft' }, { name: 'published' }],
        transitions: [{ from: 'draft', to: 'published' }],
      };

      const generator = new StatusTransitionGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('export function getNextDocumentStatuses(current: DocumentStatus): DocumentStatus[]');
    });

    it('should generate assertValidTransition helper', () => {
      const spec: StatusMachineSpec = {
        name: 'Request',
        statuses: [{ name: 'new' }, { name: 'approved' }],
        transitions: [{ from: 'new', to: 'approved' }],
      };

      const generator = new StatusTransitionGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('export function assertValidRequestTransition(from: RequestStatus, to: RequestStatus): void');
      expect(result.code).toContain('throw new Error');
    });

    it('should skip helpers when generateHelpers is false', () => {
      const spec: StatusMachineSpec = {
        name: 'Job',
        statuses: [
          { name: 'queued', isInitial: true },
          { name: 'running' },
        ],
        transitions: [{ from: 'queued', to: 'running' }],
      };

      const generator = new StatusTransitionGenerator({ generateHelpers: false });
      const result = generator.generate(spec);

      expect(result.code).not.toContain('getInitialJobStatus');
      expect(result.code).not.toContain('getNextJobStatuses');
    });

    it('should include JSDoc comments by default', () => {
      const spec: StatusMachineSpec = {
        name: 'Workflow',
        description: 'A test workflow',
        requirementId: 'REQ-WF-001',
        statuses: [{ name: 'start' }, { name: 'end' }],
        transitions: [{ from: 'start', to: 'end' }],
      };

      const generator = new StatusTransitionGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('* Workflow Status Transitions');
      expect(result.code).toContain('* A test workflow');
      expect(result.code).toContain('@requirement REQ-WF-001');
      expect(result.code).toContain('@pattern BP-DESIGN-001');
    });

    it('should skip JSDoc when includeJSDoc is false', () => {
      const spec: StatusMachineSpec = {
        name: 'Simple',
        statuses: [{ name: 'a' }, { name: 'b' }],
        transitions: [{ from: 'a', to: 'b' }],
      };

      const generator = new StatusTransitionGenerator({ includeJSDoc: false });
      const result = generator.generate(spec);

      expect(result.code).not.toContain('/**');
      expect(result.code).not.toContain('* @pattern');
    });

    it('should generate status values array', () => {
      const spec: StatusMachineSpec = {
        name: 'Phase',
        statuses: [{ name: 'alpha' }, { name: 'beta' }, { name: 'release' }],
        transitions: [],
      };

      const generator = new StatusTransitionGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain('phaseStatusValues');
      expect(result.code).toContain("['alpha', 'beta', 'release']");
    });

    it('should convert name to kebab-case for file name', () => {
      const spec: StatusMachineSpec = {
        name: 'UserAccount',
        statuses: [{ name: 'active' }],
        transitions: [],
      };

      const generator = new StatusTransitionGenerator();
      const result = generator.generate(spec);

      expect(result.fileName).toBe('user-account-status.ts');
    });

    it('should handle empty transitions for terminal statuses', () => {
      const spec: StatusMachineSpec = {
        name: 'Process',
        statuses: [
          { name: 'running' },
          { name: 'finished', isTerminal: true },
        ],
        transitions: [{ from: 'running', to: 'finished' }],
      };

      const generator = new StatusTransitionGenerator();
      const result = generator.generate(spec);

      expect(result.code).toContain("'finished': []");
    });
  });

  describe('generateStatusTransitions', () => {
    it('should work as convenience function', () => {
      const spec: StatusMachineSpec = {
        name: 'Quick',
        statuses: [{ name: 'on' }, { name: 'off' }],
        transitions: [
          { from: 'on', to: 'off' },
          { from: 'off', to: 'on' },
        ],
      };

      const result = generateStatusTransitions(spec);

      expect(result.code).toContain('QuickStatus');
      expect(result.transitionCount).toBe(2);
    });
  });

  describe('parseStatusMachineSpec', () => {
    it('should parse simple spec text', () => {
      const text = `
        Name: Order
        Description: Order status machine
        Statuses: draft, pending, confirmed
        Initial: draft
        Terminal: confirmed
        Transitions:
          draft -> pending
          pending -> confirmed
      `;

      const spec = parseStatusMachineSpec(text);

      expect(spec.name).toBe('Order');
      expect(spec.description).toBe('Order status machine');
      expect(spec.statuses).toHaveLength(3);
      expect(spec.statuses[0]).toEqual({ name: 'draft', isInitial: true });
      expect(spec.statuses[2]).toEqual({ name: 'confirmed', isTerminal: true });
      expect(spec.transitions).toHaveLength(2);
    });

    it('should parse multiple targets in transition', () => {
      const text = `
        Name: Task
        Statuses: todo, in_progress, done, cancelled
        Initial: todo
        Terminal: done, cancelled
        Transitions:
          todo -> in_progress
          in_progress -> done, cancelled
      `;

      const spec = parseStatusMachineSpec(text);

      expect(spec.transitions).toHaveLength(3);
      expect(spec.transitions).toContainEqual({ from: 'in_progress', to: 'done' });
      expect(spec.transitions).toContainEqual({ from: 'in_progress', to: 'cancelled' });
    });

    it('should parse requirement ID', () => {
      const text = `
        Name: Booking
        Requirement: REQ-BOOK-001
        Statuses: pending, confirmed
        Transitions:
          pending -> confirmed
      `;

      const spec = parseStatusMachineSpec(text);

      expect(spec.requirementId).toBe('REQ-BOOK-001');
    });

    it('should handle multiple terminal statuses', () => {
      const text = `
        Name: Invoice
        Statuses: draft, sent, paid, voided
        Initial: draft
        Terminal: paid, voided
        Transitions:
          draft -> sent
          sent -> paid, voided
      `;

      const spec = parseStatusMachineSpec(text);

      const terminals = spec.statuses.filter((s) => s.isTerminal);
      expect(terminals).toHaveLength(2);
      expect(terminals.map((s) => s.name)).toEqual(['paid', 'voided']);
    });
  });
});
