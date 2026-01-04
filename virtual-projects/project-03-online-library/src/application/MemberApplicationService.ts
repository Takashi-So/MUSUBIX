/**
 * Member Application Service
 * @design DES-LIBRARY-001 §6.2
 * @task TSK-LIB-014
 */

import { Member, MemberType, MemberId } from '../domain/member/Member';
import { MemberRepository } from '../infrastructure/repositories/MemberRepository';

export interface RegisterMemberCommand {
  email: string;
  name: string;
  phone: string;
  address: string;
  birthDate: Date;
  memberType: MemberType;
}

export interface RegisterMemberResult {
  success: boolean;
  member?: Member;
  error?: string;
}

export class MemberApplicationService {
  constructor(private readonly memberRepository: MemberRepository) {}

  async registerMember(command: RegisterMemberCommand): Promise<RegisterMemberResult> {
    try {
      // Check for duplicate email
      const existing = await this.memberRepository.findByEmail(command.email);
      if (existing) {
        return {
          success: false,
          error: 'Member with this email already exists',
        };
      }

      // Create member
      const member = Member.create({
        email: command.email,
        name: command.name,
        phone: command.phone,
        address: command.address,
        birthDate: command.birthDate,
        memberType: command.memberType,
      });

      await this.memberRepository.save(member);

      return { success: true, member };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Failed to register member',
      };
    }
  }

  async getMemberById(memberId: string): Promise<Member | null> {
    return this.memberRepository.findById(new MemberId(memberId));
  }

  async getMemberByEmail(email: string): Promise<Member | null> {
    return this.memberRepository.findByEmail(email);
  }

  async getActiveMembers(): Promise<Member[]> {
    return this.memberRepository.findActiveMembers();
  }

  async suspendMember(memberId: string, reason: string): Promise<{ success: boolean; error?: string }> {
    const member = await this.memberRepository.findById(new MemberId(memberId));
    if (!member) {
      return { success: false, error: 'Member not found' };
    }

    member.suspend(reason);
    await this.memberRepository.save(member);
    return { success: true };
  }
}
