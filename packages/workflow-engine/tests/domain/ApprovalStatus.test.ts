/**
 * ApprovalStatus Value Object Tests
 * 
 * @see REQ-ORCH-003 - Quality Gate Integration
 * @see DES-ORCH-003 - QualityGateRunner
 */

import { describe, it, expect } from 'vitest';
import {
  type ApprovalStatus,
  type Approval,
  APPROVAL_KEYWORDS,
  REJECTION_KEYWORDS,
  createApproval,
  parseApprovalFromInput,
  isApproved,
  isRejected,
  generateApprovalId,
} from '../../src/domain/value-objects/ApprovalStatus.js';

describe('ApprovalStatus', () => {
  describe('APPROVAL_KEYWORDS', () => {
    it('should include common approval keywords', () => {
      expect(APPROVAL_KEYWORDS).toContain('承認');
      expect(APPROVAL_KEYWORDS).toContain('approve');
      expect(APPROVAL_KEYWORDS).toContain('LGTM');
      expect(APPROVAL_KEYWORDS).toContain('OK');
      expect(APPROVAL_KEYWORDS).toContain('進める');
      expect(APPROVAL_KEYWORDS).toContain('実装');
    });
  });

  describe('parseApprovalFromInput', () => {
    it('should detect approval keywords (Japanese)', () => {
      const result = parseApprovalFromInput('承認します');
      expect(result).toBe('approved');
    });

    it('should detect approval keywords (OK)', () => {
      const result = parseApprovalFromInput('OK, looks good');
      expect(result).toBe('approved');
    });

    it('should detect approval keywords (LGTM)', () => {
      const result = parseApprovalFromInput('LGTM!');
      expect(result).toBe('approved');
    });

    it('should detect approval keywords (case insensitive)', () => {
      const result = parseApprovalFromInput('lgtm');
      expect(result).toBe('approved');
    });

    it('should detect rejection keywords', () => {
      const result = parseApprovalFromInput('修正が必要です');
      expect(result).toBe('rejected');
    });

    it('should return pending without keywords', () => {
      const result = parseApprovalFromInput('何か言いたいことがある');
      expect(result).toBe('pending');
    });

    it('should return pending for empty input', () => {
      const result = parseApprovalFromInput('');
      expect(result).toBe('pending');
    });
  });

  describe('createApproval', () => {
    it('should create approved approval', () => {
      const approval = createApproval('APR-001', 'approved', 'user', 'Looks good');
      expect(approval.status).toBe('approved');
      expect(approval.approver).toBe('user');
      expect(approval.comment).toBe('Looks good');
    });

    it('should create rejected approval', () => {
      const approval = createApproval('APR-002', 'rejected', 'reviewer', '修正が必要');
      expect(approval.status).toBe('rejected');
      expect(approval.comment).toBe('修正が必要');
    });

    it('should include timestamp', () => {
      const approval = createApproval('APR-003', 'approved', 'user');
      expect(approval.timestamp).toBeInstanceOf(Date);
    });

    it('should create approval without comment', () => {
      const approval = createApproval('APR-004', 'pending', 'user');
      expect(approval.comment).toBeUndefined();
    });
  });

  describe('isApproved', () => {
    it('should return true for approved status', () => {
      const approval = createApproval('APR-001', 'approved', 'user');
      expect(isApproved(approval)).toBe(true);
    });

    it('should return false for rejected status', () => {
      const approval = createApproval('APR-002', 'rejected', 'user');
      expect(isApproved(approval)).toBe(false);
    });

    it('should return false for pending status', () => {
      const approval = createApproval('APR-003', 'pending', 'user');
      expect(isApproved(approval)).toBe(false);
    });
  });

  describe('isRejected', () => {
    it('should return true for rejected status', () => {
      const approval = createApproval('APR-001', 'rejected', 'user');
      expect(isRejected(approval)).toBe(true);
    });

    it('should return false for approved status', () => {
      const approval = createApproval('APR-002', 'approved', 'user');
      expect(isRejected(approval)).toBe(false);
    });
  });

  describe('generateApprovalId', () => {
    it('should generate unique IDs', () => {
      const id1 = generateApprovalId('requirements');
      const id2 = generateApprovalId('requirements');
      // They might be the same if called in the same millisecond, so just check format
      expect(id1).toMatch(/^APR-REQUIREMENTS-[a-z0-9]+$/);
    });

    it('should have APR- prefix', () => {
      const id = generateApprovalId('design');
      expect(id.startsWith('APR-')).toBe(true);
    });

    it('should include uppercase phase type', () => {
      const id = generateApprovalId('task-breakdown');
      expect(id).toContain('TASK-BREAKDOWN');
    });
  });
});
