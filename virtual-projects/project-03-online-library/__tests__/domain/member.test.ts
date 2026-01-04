/**
 * Member Entity and Related Value Objects Tests
 * @requirements REQ-MEMBER-001, REQ-MEMBER-004, REQ-MEMBER-005
 * @design DES-LIBRARY-001 §3.3
 * @task TSK-LIB-003, TSK-LIB-004
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { Member, MemberId, MemberType, MemberStatus } from '../../src/domain/member/Member';
import { Penalty, PenaltyId, PenaltyStatus } from '../../src/domain/member/Penalty';

describe('Member Entity', () => {
  describe('creation', () => {
    it('should create member with valid data', () => {
      const member = Member.create({
        name: '山田太郎',
        email: 'yamada@example.com',
        phone: '090-1234-5678',
        address: '東京都渋谷区1-1-1',
        birthDate: new Date('1990-01-01'),
        memberType: MemberType.GENERAL,
      });

      expect(member.id).toBeDefined();
      expect(member.name).toBe('山田太郎');
      expect(member.email).toBe('yamada@example.com');
      expect(member.status).toBe(MemberStatus.ACTIVE);
    });

    it('should reject invalid email format', () => {
      expect(() =>
        Member.create({
          name: '山田太郎',
          email: 'invalid-email',
          phone: '090-1234-5678',
          address: '東京都渋谷区1-1-1',
          birthDate: new Date('1990-01-01'),
          memberType: MemberType.GENERAL,
        })
      ).toThrow('Invalid email format');
    });
  });

  describe('loan limit', () => {
    it('should return 5 for general member', () => {
      const member = Member.create({
        name: '山田太郎',
        email: 'yamada@example.com',
        phone: '090-1234-5678',
        address: '東京都',
        birthDate: new Date('1990-01-01'),
        memberType: MemberType.GENERAL,
      });
      expect(member.getLoanLimit()).toBe(5);
    });

    it('should return 10 for student member', () => {
      const member = Member.create({
        name: '学生太郎',
        email: 'student@example.com',
        phone: '090-1234-5678',
        address: '東京都',
        birthDate: new Date('2000-01-01'),
        memberType: MemberType.STUDENT,
      });
      expect(member.getLoanLimit()).toBe(10);
    });

    it('should return 7 for senior member', () => {
      const member = Member.create({
        name: 'シニア太郎',
        email: 'senior@example.com',
        phone: '090-1234-5678',
        address: '東京都',
        birthDate: new Date('1950-01-01'),
        memberType: MemberType.SENIOR,
      });
      expect(member.getLoanLimit()).toBe(7);
    });
  });

  describe('status management', () => {
    it('should deactivate member', () => {
      const member = Member.create({
        name: '山田太郎',
        email: 'yamada@example.com',
        phone: '090-1234-5678',
        address: '東京都',
        birthDate: new Date('1990-01-01'),
        memberType: MemberType.GENERAL,
      });

      member.deactivate();
      expect(member.status).toBe(MemberStatus.INACTIVE);
    });

    it('should reactivate member', () => {
      const member = Member.create({
        name: '山田太郎',
        email: 'yamada@example.com',
        phone: '090-1234-5678',
        address: '東京都',
        birthDate: new Date('1990-01-01'),
        memberType: MemberType.GENERAL,
      });

      member.deactivate();
      member.activate();
      expect(member.status).toBe(MemberStatus.ACTIVE);
    });

    it('should suspend member', () => {
      const member = Member.create({
        name: '山田太郎',
        email: 'yamada@example.com',
        phone: '090-1234-5678',
        address: '東京都',
        birthDate: new Date('1990-01-01'),
        memberType: MemberType.GENERAL,
      });

      member.suspend();
      expect(member.status).toBe(MemberStatus.SUSPENDED);
    });
  });

  describe('eligibility', () => {
    it('should be eligible when active', () => {
      const member = Member.create({
        name: '山田太郎',
        email: 'yamada@example.com',
        phone: '090-1234-5678',
        address: '東京都',
        birthDate: new Date('1990-01-01'),
        memberType: MemberType.GENERAL,
      });

      expect(member.isEligibleForLoan()).toBe(true);
    });

    it('should not be eligible when inactive', () => {
      const member = Member.create({
        name: '山田太郎',
        email: 'yamada@example.com',
        phone: '090-1234-5678',
        address: '東京都',
        birthDate: new Date('1990-01-01'),
        memberType: MemberType.GENERAL,
      });

      member.deactivate();
      expect(member.isEligibleForLoan()).toBe(false);
    });
  });
});

describe('Penalty Entity', () => {
  let memberId: MemberId;

  beforeEach(() => {
    memberId = MemberId.generate();
  });

  describe('creation', () => {
    it('should create penalty with calculated end date', () => {
      const penalty = Penalty.create({
        memberId,
        reason: 'overdue',
        overdueDays: 5,
      });

      expect(penalty.id).toBeDefined();
      expect(penalty.status).toBe(PenaltyStatus.ACTIVE);
      // 延滞日数 × 2日間のペナルティ期間
      const expectedDuration = 5 * 2; // 10日間
      const expectedEndDate = new Date(penalty.startDate);
      expectedEndDate.setDate(expectedEndDate.getDate() + expectedDuration);
      expect(penalty.endDate.toDateString()).toBe(expectedEndDate.toDateString());
    });
  });

  describe('status', () => {
    it('should check if penalty is active', () => {
      const penalty = Penalty.create({
        memberId,
        reason: 'overdue',
        overdueDays: 1,
      });

      expect(penalty.isActive()).toBe(true);
    });

    it('should complete penalty', () => {
      const penalty = Penalty.create({
        memberId,
        reason: 'overdue',
        overdueDays: 1,
      });

      penalty.complete();
      expect(penalty.status).toBe(PenaltyStatus.COMPLETED);
    });

    it('should waive penalty', () => {
      const penalty = Penalty.create({
        memberId,
        reason: 'overdue',
        overdueDays: 1,
      });

      penalty.waive();
      expect(penalty.status).toBe(PenaltyStatus.WAIVED);
    });
  });

  describe('remaining days', () => {
    it('should calculate remaining penalty days', () => {
      const penalty = Penalty.create({
        memberId,
        reason: 'overdue',
        overdueDays: 5, // 10日間のペナルティ
      });

      const remaining = penalty.getRemainingDays();
      expect(remaining).toBeGreaterThan(0);
      expect(remaining).toBeLessThanOrEqual(10);
    });
  });
});

describe('MemberId Value Object', () => {
  it('should generate unique ID', () => {
    const id1 = MemberId.generate();
    const id2 = MemberId.generate();
    expect(id1.equals(id2)).toBe(false);
  });

  it('should be equal for same ID value', () => {
    const id = MemberId.generate();
    const id2 = new MemberId(id.value);
    expect(id.equals(id2)).toBe(true);
  });
});
