/**
 * Space Repository
 * @requirement REQ-SPACE-001, REQ-SPACE-002, REQ-SPACE-003
 * @design DES-PARKING-001 Section 4.3
 * @pattern Repository
 */

import { ParkingSpace, SpaceType, SpaceState, SpaceStats } from '../types/Space.js';
import { generateSpaceId } from '../utils/IdGenerator.js';

export class SpaceRepository {
  private spaces: Map<string, ParkingSpace> = new Map();

  /**
   * 駐車スペースを登録
   */
  create(data: Omit<ParkingSpace, 'id' | 'createdAt' | 'updatedAt'>): ParkingSpace {
    const now = new Date();
    const space: ParkingSpace = {
      ...data,
      id: generateSpaceId(),
      createdAt: now,
      updatedAt: now,
    };
    this.spaces.set(space.id, space);
    return space;
  }

  /**
   * IDでスペースを取得
   */
  findById(id: string): ParkingSpace | null {
    return this.spaces.get(id) ?? null;
  }

  /**
   * スペース番号でスペースを取得
   */
  findByNumber(spaceNumber: string): ParkingSpace | null {
    for (const space of this.spaces.values()) {
      if (space.spaceNumber === spaceNumber) {
        return space;
      }
    }
    return null;
  }

  /**
   * 状態でスペースをフィルタ
   */
  findByState(state: SpaceState): ParkingSpace[] {
    return Array.from(this.spaces.values()).filter(s => s.state === state);
  }

  /**
   * タイプでスペースをフィルタ
   */
  findByType(type: SpaceType): ParkingSpace[] {
    return Array.from(this.spaces.values()).filter(s => s.type === type);
  }

  /**
   * 空いているスペースを取得
   */
  findAvailable(type?: SpaceType): ParkingSpace[] {
    return Array.from(this.spaces.values())
      .filter(s => s.state === 'available')
      .filter(s => type ? s.type === type : true);
  }

  /**
   * スペースを更新
   */
  update(id: string, data: Partial<ParkingSpace>): ParkingSpace | null {
    const space = this.spaces.get(id);
    if (!space) return null;

    const updated: ParkingSpace = {
      ...space,
      ...data,
      id: space.id,
      createdAt: space.createdAt,
      updatedAt: new Date(),
    };
    this.spaces.set(id, updated);
    return updated;
  }

  /**
   * 状態を更新
   */
  updateState(id: string, state: SpaceState): ParkingSpace | null {
    return this.update(id, { state });
  }

  /**
   * 全スペースを取得
   */
  findAll(): ParkingSpace[] {
    return Array.from(this.spaces.values());
  }

  /**
   * 統計を計算
   */
  getStats(): SpaceStats {
    const all = this.findAll();
    return {
      total: all.length,
      available: all.filter(s => s.state === 'available').length,
      occupied: all.filter(s => s.state === 'occupied').length,
      reserved: all.filter(s => s.state === 'reserved').length,
      maintenance: all.filter(s => s.state === 'maintenance').length,
    };
  }

  /**
   * スペースを削除
   */
  delete(id: string): boolean {
    return this.spaces.delete(id);
  }

  /**
   * 全データをクリア（テスト用）
   */
  clear(): void {
    this.spaces.clear();
  }
}
