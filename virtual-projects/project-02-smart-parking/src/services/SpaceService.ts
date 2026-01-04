/**
 * Space Service
 * @requirement REQ-SPACE-001, REQ-SPACE-002, REQ-SPACE-003
 * @design DES-PARKING-001 Section 4.2
 * @pattern Service
 */

import { ParkingSpace, SpaceType, SpaceState, SpaceStats, SPACE_ERRORS } from '../types/Space.js';
import { SpaceRepository } from '../repositories/SpaceRepository.js';

export interface CreateSpaceInput {
  spaceNumber: string;
  type: SpaceType;
  floor?: number;
  section?: string;
}

export interface SpaceServiceResult<T> {
  success: boolean;
  data?: T;
  error?: string;
}

export class SpaceService {
  constructor(private repository: SpaceRepository) {}

  /**
   * 新しい駐車スペースを登録
   * @requirement REQ-SPACE-001: 初期状態は「空き」
   */
  createSpace(input: CreateSpaceInput): SpaceServiceResult<ParkingSpace> {
    // 重複チェック
    const existing = this.repository.findByNumber(input.spaceNumber);
    if (existing) {
      return { success: false, error: SPACE_ERRORS.ALREADY_EXISTS };
    }

    const space = this.repository.create({
      ...input,
      state: 'available',  // 初期状態は「空き」
    });

    return { success: true, data: space };
  }

  /**
   * 複数スペースを一括登録
   */
  createBulk(inputs: CreateSpaceInput[]): SpaceServiceResult<ParkingSpace[]> {
    const created: ParkingSpace[] = [];
    const errors: string[] = [];

    for (const input of inputs) {
      const result = this.createSpace(input);
      if (result.success && result.data) {
        created.push(result.data);
      } else {
        errors.push(`${input.spaceNumber}: ${result.error}`);
      }
    }

    if (errors.length > 0) {
      return { success: false, data: created, error: errors.join('; ') };
    }

    return { success: true, data: created };
  }

  /**
   * スペースを「使用中」に変更
   * @requirement REQ-SPACE-002: 満車時は入庫不可
   */
  occupy(spaceId: string): SpaceServiceResult<ParkingSpace> {
    const space = this.repository.findById(spaceId);
    if (!space) {
      return { success: false, error: SPACE_ERRORS.NOT_FOUND };
    }

    if (space.state !== 'available') {
      return { success: false, error: SPACE_ERRORS.OCCUPIED };
    }

    const updated = this.repository.updateState(spaceId, 'occupied');
    return { success: true, data: updated! };
  }

  /**
   * スペースを「空き」に変更
   */
  release(spaceId: string): SpaceServiceResult<ParkingSpace> {
    const space = this.repository.findById(spaceId);
    if (!space) {
      return { success: false, error: SPACE_ERRORS.NOT_FOUND };
    }

    if (space.state !== 'occupied') {
      return { success: false, error: SPACE_ERRORS.NOT_OCCUPIED };
    }

    const updated = this.repository.updateState(spaceId, 'available');
    return { success: true, data: updated! };
  }

  /**
   * スペースを「メンテナンス」に変更
   */
  setMaintenance(spaceId: string): SpaceServiceResult<ParkingSpace> {
    const space = this.repository.findById(spaceId);
    if (!space) {
      return { success: false, error: SPACE_ERRORS.NOT_FOUND };
    }

    const updated = this.repository.updateState(spaceId, 'maintenance');
    return { success: true, data: updated! };
  }

  /**
   * メンテナンスを終了
   */
  endMaintenance(spaceId: string): SpaceServiceResult<ParkingSpace> {
    const space = this.repository.findById(spaceId);
    if (!space) {
      return { success: false, error: SPACE_ERRORS.NOT_FOUND };
    }

    if (space.state !== 'maintenance') {
      return { success: false, error: 'Space is not under maintenance' };
    }

    const updated = this.repository.updateState(spaceId, 'available');
    return { success: true, data: updated! };
  }

  /**
   * 空きスペースを検索
   * @requirement REQ-SPACE-003: 空き状況をリアルタイム表示
   */
  findAvailable(type?: SpaceType): ParkingSpace[] {
    return this.repository.findAvailable(type);
  }

  /**
   * 統計を取得
   * @requirement REQ-SPACE-003: 空き状況をリアルタイム表示
   */
  getStats(): SpaceStats {
    return this.repository.getStats();
  }

  /**
   * 満車かどうかをチェック
   */
  isFull(type?: SpaceType): boolean {
    const available = this.findAvailable(type);
    return available.length === 0;
  }

  /**
   * スペースを取得
   */
  getSpace(id: string): ParkingSpace | null {
    return this.repository.findById(id);
  }

  /**
   * 全スペースを取得
   */
  getAllSpaces(): ParkingSpace[] {
    return this.repository.findAll();
  }
}
