/**
 * Member Repository Interface
 * @design DES-LIBRARY-001 §5.2
 */

import { Member, MemberId } from '../../domain/member/Member';
import { Penalty, PenaltyId } from '../../domain/member/Penalty';

export interface MemberRepository {
  save(member: Member): Promise<void>;
  findById(id: MemberId): Promise<Member | null>;
  findByEmail(email: string): Promise<Member | null>;
  findActiveMembers(): Promise<Member[]>;
  findAll(): Promise<Member[]>;
  delete(id: MemberId): Promise<void>;

  // Penalty management
  savePenalty(penalty: Penalty): Promise<void>;
  findPenaltyById(id: PenaltyId): Promise<Penalty | null>;
  findActivePenaltiesByMemberId(memberId: MemberId): Promise<Penalty[]>;
}
