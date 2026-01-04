/**
 * MemberService - 会員ドメインサービス
 * @requirements REQ-MEMBER-001, REQ-MEMBER-002, REQ-MEMBER-003, REQ-MEMBER-004, REQ-MEMBER-005
 * @design DES-LIBRARY-001 §4.3 MemberService
 * @task TSK-LIB-009
 */

import { Member, MemberStatus } from '../member/Member';
import { Penalty, PenaltyStatus } from '../member/Penalty';
import { Loan } from '../loan/Loan';

export interface EligibilityResult {
  eligible: boolean;
  reason?: string;
}

/**
 * MemberService - 会員ビジネスロジック
 * 
 * @requirements REQ-MEMBER-001 会員登録
 * @requirements REQ-MEMBER-002 会員種別管理
 * @requirements REQ-MEMBER-003 貸出可能冊数
 * @requirements REQ-MEMBER-004 延滞ペナルティ
 */
export class MemberService {
  /**
   * ペナルティ適用
   * @requirements REQ-MEMBER-004
   */
  applyPenalty(member: Member, penalty: Penalty): void {
    const reason = `Overdue penalty: ${penalty.suspensionDays} days suspension`;
    member.suspend(reason);
  }

  /**
   * 貸出資格チェック
   * @requirements REQ-MEMBER-003, REQ-MEMBER-004
   */
  checkEligibility(member: Member, penalties: Penalty[]): EligibilityResult {
    // 停止中の会員は不可
    if (member.status === MemberStatus.SUSPENDED) {
      return {
        eligible: false,
        reason: 'Member is suspended',
      };
    }

    // 退会済みの会員は不可
    if (member.status === MemberStatus.WITHDRAWN) {
      return {
        eligible: false,
        reason: 'Member has withdrawn',
      };
    }

    // アクティブなペナルティがある場合は不可
    const activePenalties = penalties.filter(
      (p) =>
        p.memberId.equals(member.id) && p.isActive()
    );
    if (activePenalties.length > 0) {
      return {
        eligible: false,
        reason: 'Member has unpaid penalties',
      };
    }

    return { eligible: true };
  }

  /**
   * 残り貸出可能枠を取得
   * @requirements REQ-MEMBER-003
   */
  getRemainingLoanSlots(member: Member, activeLoans: Loan[]): number {
    const memberLoans = activeLoans.filter((loan) =>
      loan.memberId.equals(member.id)
    );
    return Math.max(0, member.getLoanLimit() - memberLoans.length);
  }

  /**
   * ペナルティ期間終了後の復帰処理
   */
  reinstateFromPenalty(member: Member): void {
    if (member.status === MemberStatus.SUSPENDED) {
      member.reactivate();
    }
  }
}
