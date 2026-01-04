/**
 * PetHistoryRepository - ペット変更履歴の永続化
 * 
 * @requirement REQ-PET-002
 * @design DES-PETCLINIC-001 Section 3.1
 * @pattern Repository
 */

import type { Pet, PetHistoryEntry } from '../types/Pet.js';
import { IdGenerator } from '../utils/IdGenerator.js';

const historyIdGen = new IdGenerator('PETHIST');

export class PetHistoryRepository {
  private history: Map<string, PetHistoryEntry[]> = new Map();

  /**
   * ペットのスナップショットを履歴に保存
   * @param pet 保存するペットデータ
   * @param changedBy 変更者ID
   * @returns 作成された履歴エントリ
   */
  saveSnapshot(pet: Pet, changedBy: string): PetHistoryEntry {
    const entry: PetHistoryEntry = {
      id: historyIdGen.generate(),
      petId: pet.id,
      snapshot: { ...pet },
      changedAt: new Date(),
      changedBy,
    };

    const existing = this.history.get(pet.id) ?? [];
    existing.push(entry);
    this.history.set(pet.id, existing);

    return entry;
  }

  /**
   * ペットの変更履歴を取得
   * @param petId ペットID
   * @returns 履歴エントリの配列（新しい順）
   */
  getHistory(petId: string): PetHistoryEntry[] {
    const entries = this.history.get(petId) ?? [];
    return [...entries].sort(
      (a, b) => b.changedAt.getTime() - a.changedAt.getTime()
    );
  }

  /**
   * 履歴をクリア（テスト用）
   */
  clear(): void {
    this.history.clear();
  }
}
