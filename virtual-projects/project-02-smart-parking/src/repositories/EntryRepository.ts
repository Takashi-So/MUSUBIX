/**
 * Entry Repository
 * @requirement REQ-ENTRY-001, REQ-ENTRY-002, REQ-ENTRY-003
 * @design DES-PARKING-001 Section 4.3
 * @pattern Repository
 */

import { EntryRecord, EntryStatus } from '../types/Entry.js';
import { generateEntryId } from '../utils/IdGenerator.js';

export class EntryRepository {
  private entries: Map<string, EntryRecord> = new Map();

  /**
   * 入庫記録を作成
   */
  create(data: Omit<EntryRecord, 'id' | 'status' | 'createdAt' | 'updatedAt'>): EntryRecord {
    const now = new Date();
    const entry: EntryRecord = {
      ...data,
      id: generateEntryId(),
      status: 'active',
      createdAt: now,
      updatedAt: now,
    };
    this.entries.set(entry.id, entry);
    return entry;
  }

  /**
   * IDで記録を取得
   */
  findById(id: string): EntryRecord | null {
    return this.entries.get(id) ?? null;
  }

  /**
   * ナンバープレートで検索
   */
  findByPlate(plateNumber: string): EntryRecord[] {
    return Array.from(this.entries.values())
      .filter(e => e.plateNumber === plateNumber);
  }

  /**
   * ナンバープレートでアクティブな記録を検索
   */
  findActiveByPlate(plateNumber: string): EntryRecord | null {
    return Array.from(this.entries.values())
      .find(e => e.plateNumber === plateNumber && e.status === 'active') ?? null;
  }

  /**
   * 重複チェック（同じナンバーが入庫中）
   */
  checkDuplicate(plateNumber: string): boolean {
    return this.findActiveByPlate(plateNumber) !== null;
  }

  /**
   * スペースIDでアクティブな記録を検索
   */
  findActiveBySpaceId(spaceId: string): EntryRecord | null {
    return Array.from(this.entries.values())
      .find(e => e.spaceId === spaceId && e.status === 'active') ?? null;
  }

  /**
   * 状態でフィルタ
   */
  findByStatus(status: EntryStatus): EntryRecord[] {
    return Array.from(this.entries.values())
      .filter(e => e.status === status);
  }

  /**
   * 記録を更新
   */
  update(id: string, data: Partial<EntryRecord>): EntryRecord | null {
    const entry = this.entries.get(id);
    if (!entry) return null;

    const updated: EntryRecord = {
      ...entry,
      ...data,
      id: entry.id,
      createdAt: entry.createdAt,
      updatedAt: new Date(),
    };
    this.entries.set(id, updated);
    return updated;
  }

  /**
   * 出庫処理
   */
  completeExit(id: string, exitTime: Date, feeAmount: number): EntryRecord | null {
    return this.update(id, {
      status: 'completed',
      exitTime,
      feeAmount,
    });
  }

  /**
   * 全記録を取得
   */
  findAll(): EntryRecord[] {
    return Array.from(this.entries.values());
  }

  /**
   * 日付範囲で検索
   */
  findByDateRange(start: Date, end: Date): EntryRecord[] {
    return Array.from(this.entries.values())
      .filter(e => e.entryTime >= start && e.entryTime <= end);
  }

  /**
   * 記録を削除
   */
  delete(id: string): boolean {
    return this.entries.delete(id);
  }

  /**
   * 全データをクリア（テスト用）
   */
  clear(): void {
    this.entries.clear();
  }
}
