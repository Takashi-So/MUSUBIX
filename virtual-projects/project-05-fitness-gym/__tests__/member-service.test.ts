/**
 * MemberService Unit Tests
 * @traces REQ-GYM-001, REQ-GYM-002, REQ-GYM-003
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  MemberService,
  IMemberRepository,
  Member,
  CreateMemberInput,
  MemberFilterOptions,
  UsageRecord,
} from '../src/member-service';

// Mock Repository
function createMockRepository(): IMemberRepository {
  const members: Map<string, Member> = new Map();
  const usageRecords: UsageRecord[] = [];

  return {
    async save(member: Member): Promise<Member> {
      members.set(member.id, member);
      return member;
    },
    async findById(id: string): Promise<Member | null> {
      return members.get(id) || null;
    },
    async findByEmail(email: string): Promise<Member | null> {
      for (const member of members.values()) {
        if (member.email === email) return member;
      }
      return null;
    },
    async findByCardNumber(_cardNumber: string): Promise<Member | null> {
      return null;
    },
    async findAll(_filter?: MemberFilterOptions): Promise<Member[]> {
      return Array.from(members.values());
    },
    async update(id: string, data: Partial<Member>): Promise<Member> {
      const member = members.get(id);
      if (!member) throw new Error('Not found');
      const updated = { ...member, ...data };
      members.set(id, updated);
      return updated;
    },
    async delete(id: string): Promise<boolean> {
      return members.delete(id);
    },
    async saveUsageRecord(record: UsageRecord): Promise<UsageRecord> {
      usageRecords.push(record);
      return record;
    },
    async getUsageRecords(memberId: string, _days: number): Promise<UsageRecord[]> {
      return usageRecords.filter((r) => r.memberId === memberId);
    },
  };
}

describe('MemberService', () => {
  let service: MemberService;
  let repository: IMemberRepository;

  beforeEach(() => {
    repository = createMockRepository();
    service = new MemberService(repository);
  });

  describe('REQ-GYM-001: 会員登録', () => {
    const validInput: CreateMemberInput = {
      name: '山田太郎',
      email: 'yamada@example.com',
      phone: '090-1234-5678',
      emergencyContact: {
        name: '山田花子',
        phone: '090-8765-4321',
        relationship: '配偶者',
      },
      membershipPlanId: 'standard',
    };

    it('THE MemberService SHALL create a new member with valid input', async () => {
      const member = await service.create(validInput);

      expect(member).toBeDefined();
      expect(member.id).toMatch(/^MEM-/);
      expect(member.name).toBe(validInput.name);
      expect(member.email).toBe(validInput.email);
      expect(member.status).toBe('active');
      expect(member.emergencyContact).toEqual(validInput.emergencyContact);
    });

    it('THE MemberService SHALL NOT create duplicate members with same email', async () => {
      await service.create(validInput);

      await expect(service.create(validInput)).rejects.toThrow(
        'Member with this email already exists',
      );
    });

    it('THE MemberService SHALL set initial status to active', async () => {
      const member = await service.create(validInput);
      expect(member.status).toBe('active');
    });

    it('THE MemberService SHALL record join date', async () => {
      const before = new Date();
      const member = await service.create(validInput);
      const after = new Date();

      expect(member.joinDate.getTime()).toBeGreaterThanOrEqual(before.getTime());
      expect(member.joinDate.getTime()).toBeLessThanOrEqual(after.getTime());
    });
  });

  describe('REQ-GYM-002: チェックイン/チェックアウト', () => {
    let testMember: Member;

    beforeEach(async () => {
      testMember = await service.create({
        name: 'Test User',
        email: 'test@example.com',
        phone: '000-0000-0000',
        emergencyContact: { name: 'Emergency', phone: '111-1111-1111', relationship: 'Friend' },
        membershipPlanId: 'basic',
      });
    });

    it('WHEN member checks in, THE MemberService SHALL return success result', async () => {
      const result = await service.checkIn(testMember.id);

      expect(result.success).toBe(true);
      expect(result.memberId).toBe(testMember.id);
      expect(result.membershipStatus).toBe('active');
      expect(result.message).toContain('Welcome back');
    });

    it('WHEN non-existent member checks in, THE MemberService SHALL return failure', async () => {
      const result = await service.checkIn('non-existent-id');

      expect(result.success).toBe(false);
      expect(result.message).toBe('Member not found');
    });

    it('WHILE member is suspended, THE MemberService SHALL reject check-in', async () => {
      await service.suspend(testMember.id, 'Payment overdue');
      const result = await service.checkIn(testMember.id);

      expect(result.success).toBe(false);
      expect(result.message).toContain('suspended');
    });

    it('WHEN member checks in, THE MemberService SHALL update last visit date', async () => {
      const before = new Date();
      await service.checkIn(testMember.id);
      const updated = await service.getById(testMember.id);

      expect(updated?.lastVisit).toBeDefined();
      expect(updated?.lastVisit?.getTime()).toBeGreaterThanOrEqual(before.getTime());
    });
  });

  describe('REQ-GYM-003: プロフィール管理', () => {
    let testMember: Member;

    beforeEach(async () => {
      testMember = await service.create({
        name: 'Test User',
        email: 'test@example.com',
        phone: '000-0000-0000',
        emergencyContact: { name: 'Emergency', phone: '111-1111-1111', relationship: 'Friend' },
        membershipPlanId: 'basic',
      });
    });

    it('THE MemberService SHALL allow updating member profile', async () => {
      const updated = await service.update(testMember.id, {
        name: 'Updated Name',
        phone: '999-9999-9999',
      });

      expect(updated.name).toBe('Updated Name');
      expect(updated.phone).toBe('999-9999-9999');
      expect(updated.email).toBe(testMember.email);
    });

    it('THE MemberService SHALL NOT update non-existent member', async () => {
      await expect(service.update('non-existent', { name: 'New Name' })).rejects.toThrow(
        'Member not found',
      );
    });

    it('THE MemberService SHALL return member by ID', async () => {
      const member = await service.getById(testMember.id);
      expect(member).toEqual(testMember);
    });

    it('THE MemberService SHALL return member by email', async () => {
      const member = await service.getByEmail(testMember.email);
      expect(member).toEqual(testMember);
    });

    it('THE MemberService SHALL return null for non-existent member', async () => {
      const member = await service.getById('non-existent');
      expect(member).toBeNull();
    });
  });

  describe('会員ステータス管理', () => {
    let testMember: Member;

    beforeEach(async () => {
      testMember = await service.create({
        name: 'Test User',
        email: 'test@example.com',
        phone: '000-0000-0000',
        emergencyContact: { name: 'Emergency', phone: '111-1111-1111', relationship: 'Friend' },
        membershipPlanId: 'basic',
      });
    });

    it('THE MemberService SHALL activate suspended member', async () => {
      await service.suspend(testMember.id, 'Test');
      const activated = await service.activate(testMember.id);
      expect(activated.status).toBe('active');
    });

    it('THE MemberService SHALL suspend active member', async () => {
      const suspended = await service.suspend(testMember.id, 'Payment overdue');
      expect(suspended.status).toBe('suspended');
    });

    it('THE MemberService SHALL delete member', async () => {
      const deleted = await service.delete(testMember.id);
      expect(deleted).toBe(true);
      
      const member = await service.getById(testMember.id);
      expect(member).toBeNull();
    });
  });

  describe('利用履歴', () => {
    let testMember: Member;

    beforeEach(async () => {
      testMember = await service.create({
        name: 'Test User',
        email: 'test@example.com',
        phone: '000-0000-0000',
        emergencyContact: { name: 'Emergency', phone: '111-1111-1111', relationship: 'Friend' },
        membershipPlanId: 'basic',
      });
    });

    it('THE MemberService SHALL track usage history', async () => {
      await service.checkIn(testMember.id);
      const history = await service.getUsageHistory(testMember.id, 30);
      
      expect(history.length).toBeGreaterThan(0);
      expect(history[0].memberId).toBe(testMember.id);
    });
  });
});
