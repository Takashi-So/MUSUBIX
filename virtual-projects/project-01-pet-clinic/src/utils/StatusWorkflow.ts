/**
 * StatusWorkflow - ステータス遷移管理
 * 
 * @requirement REQ-RESERVE-001, REQ-RESERVE-002, REQ-RESERVE-003
 * @design DES-PETCLINIC-001 Section 3.2
 * @pattern State
 */

export type ReservationStatus = 
  | 'pending'
  | 'confirmed'
  | 'rescheduled'
  | 'completed'
  | 'cancelled'
  | 'cancelled_with_fee';

export type ReservationAction = 
  | 'confirm'
  | 'reschedule'
  | 'complete'
  | 'cancel'
  | 'cancel_with_fee';

interface Transition {
  from: ReservationStatus[];
  to: ReservationStatus;
}

const transitions: Record<ReservationAction, Transition> = {
  confirm: { from: ['pending'], to: 'confirmed' },
  reschedule: { from: ['confirmed'], to: 'rescheduled' },
  complete: { from: ['confirmed', 'rescheduled'], to: 'completed' },
  cancel: { from: ['pending', 'confirmed', 'rescheduled'], to: 'cancelled' },
  cancel_with_fee: { from: ['confirmed', 'rescheduled'], to: 'cancelled_with_fee' },
};

export class StatusWorkflow {
  /**
   * ステータス遷移を実行
   * @param current 現在のステータス
   * @param action 実行するアクション
   * @returns 新しいステータス
   * @throws 無効な遷移の場合はエラー
   */
  transition(current: ReservationStatus, action: ReservationAction): ReservationStatus {
    const rule = transitions[action];
    if (!rule) {
      throw new Error(`Unknown action: ${action}`);
    }
    if (!rule.from.includes(current)) {
      throw new Error(`Invalid transition: ${current} -> ${action}`);
    }
    return rule.to;
  }

  /**
   * 指定ステータスから可能なアクションを取得
   * @param current 現在のステータス
   * @returns 可能なアクションの配列
   */
  getAvailableActions(current: ReservationStatus): ReservationAction[] {
    return (Object.entries(transitions) as [ReservationAction, Transition][])
      .filter(([, rule]) => rule.from.includes(current))
      .map(([action]) => action);
  }
}

export const reservationWorkflow = new StatusWorkflow();
