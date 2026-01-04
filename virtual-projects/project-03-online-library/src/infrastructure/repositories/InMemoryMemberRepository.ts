/**
 * InMemory Member Repository Implementation
 * @design DES-LIBRARY-001 §5.2
 * @task TSK-LIB-011
 */

import { Member, MemberId, MemberStatus } from '../../domain/member/Member';
import { Penalty, PenaltyId } from '../../domain/member/Penalty';
import { MemberRepository } from './MemberRepository';

export class InMemoryMemberRepository implements MemberRepository {
  private members: Map<string, Member> = new Map();
  private penalties: Map<string, Penalty> = new Map();

  async save(member: Member): Promise<void> {
    this.members.set(member.id.value, member);
  }

  async findById(id: MemberId): Promise<Member | null> {
    return this.members.get(id.value) || null;
  }

  async findByEmail(email: string): Promise<Member | null> {
    for (const member of this.members.values()) {
      if (member.email === email) {
        return member;
      }
    }
    return null;
  }

  async findActiveMembers(): Promise<Member[]> {
    const results: Member[] = [];
    for (const member of this.members.values()) {
      if (member.status === MemberStatus.ACTIVE) {
        results.push(member);
      }
    }
    return results;
  }

  async findAll(): Promise<Member[]> {
    return Array.from(this.members.values());
  }

  async delete(id: MemberId): Promise<void> {
    this.members.delete(id.value);
  }

  // Penalty management
  async savePenalty(penalty: Penalty): Promise<void> {
    this.penalties.set(penalty.id.value, penalty);
  }

  async findPenaltyById(id: PenaltyId): Promise<Penalty | null> {
    return this.penalties.get(id.value) || null;
  }

  async findActivePenaltiesByMemberId(memberId: MemberId): Promise<Penalty[]> {
    const results: Penalty[] = [];
    for (const penalty of this.penalties.values()) {
      if (penalty.memberId.equals(memberId) && penalty.isActive()) {
        results.push(penalty);
      }
    }
    return results;
  }
}
