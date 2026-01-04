/**
 * PetService - ペット管理のビジネスロジック
 * 
 * @requirement REQ-PET-001, REQ-PET-002, REQ-PET-003
 * @design DES-PETCLINIC-001 Section 3.1
 * @pattern Service
 */

import type { Pet, CreatePetInput, UpdatePetInput } from '../types/Pet.js';
import { PetRepository } from '../repositories/PetRepository.js';
import { PetHistoryRepository } from '../repositories/PetHistoryRepository.js';

export interface PetServiceResult<T> {
  success: boolean;
  data?: T;
  error?: string;
}

export class PetService {
  constructor(
    private readonly petRepo: PetRepository,
    private readonly historyRepo: PetHistoryRepository
  ) {}

  /**
   * ペットを登録
   * @requirement REQ-PET-001
   * @param input ペット情報
   * @returns 作成結果
   */
  register(input: CreatePetInput): PetServiceResult<Pet> {
    // バリデーション
    if (!input.name || input.name.trim() === '') {
      return { success: false, error: 'ペット名は必須です' };
    }
    if (!input.ownerId) {
      return { success: false, error: 'オーナーIDは必須です' };
    }
    if (input.weight < 0) {
      return { success: false, error: '体重は0以上である必要があります' };
    }

    const pet = this.petRepo.save(input);
    return { success: true, data: pet };
  }

  /**
   * ペット情報を更新
   * @requirement REQ-PET-002
   * @param id ペットID
   * @param input 更新データ
   * @param changedBy 変更者ID
   * @returns 更新結果
   */
  update(id: string, input: UpdatePetInput, changedBy: string): PetServiceResult<Pet> {
    const existing = this.petRepo.findById(id);
    if (!existing) {
      return { success: false, error: 'ペットが見つかりません' };
    }

    // 更新前のスナップショットを保存
    this.historyRepo.saveSnapshot(existing, changedBy);

    // 更新実行
    const updated = this.petRepo.update(id, input);
    if (!updated) {
      return { success: false, error: '更新に失敗しました' };
    }

    return { success: true, data: updated };
  }

  /**
   * オーナーに紐づくペット一覧を取得
   * @requirement REQ-PET-003
   * @param ownerId オーナーID
   * @returns ペット一覧
   */
  findByOwner(ownerId: string): Pet[] {
    return this.petRepo.findByOwner(ownerId);
  }

  /**
   * IDでペットを取得
   * @param id ペットID
   * @returns ペット
   */
  findById(id: string): Pet | null {
    return this.petRepo.findById(id);
  }

  /**
   * ペットの変更履歴を取得
   * @param petId ペットID
   * @returns 変更履歴
   */
  getHistory(petId: string) {
    return this.historyRepo.getHistory(petId);
  }
}
