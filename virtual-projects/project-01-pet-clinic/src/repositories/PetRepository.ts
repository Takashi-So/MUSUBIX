/**
 * PetRepository - ペットデータの永続化
 * 
 * @requirement REQ-PET-001, REQ-PET-003
 * @design DES-PETCLINIC-001 Section 3.1
 * @pattern Repository
 */

import type { Pet, CreatePetInput, UpdatePetInput } from '../types/Pet.js';
import { idGenerators } from '../utils/IdGenerator.js';

export class PetRepository {
  private pets: Map<string, Pet> = new Map();

  /**
   * ペットを保存
   * @param input 作成データ
   * @returns 作成されたペット
   */
  save(input: CreatePetInput): Pet {
    const now = new Date();
    const pet: Pet = {
      id: idGenerators.pet.generate(),
      ownerId: input.ownerId,
      name: input.name,
      species: input.species,
      breed: input.breed,
      birthDate: input.birthDate,
      weight: input.weight,
      allergies: input.allergies ?? [],
      createdAt: now,
      updatedAt: now,
    };
    this.pets.set(pet.id, pet);
    return pet;
  }

  /**
   * ペット情報を更新
   * @param id ペットID
   * @param input 更新データ
   * @returns 更新されたペット、存在しない場合はnull
   */
  update(id: string, input: UpdatePetInput): Pet | null {
    const pet = this.pets.get(id);
    if (!pet) return null;

    const updated: Pet = {
      ...pet,
      ...input,
      updatedAt: new Date(),
    };
    this.pets.set(id, updated);
    return updated;
  }

  /**
   * IDでペットを検索
   * @param id ペットID
   * @returns ペット、存在しない場合はnull
   */
  findById(id: string): Pet | null {
    return this.pets.get(id) ?? null;
  }

  /**
   * オーナーIDでペット一覧を取得
   * @param ownerId オーナーID
   * @returns ペットの配列
   */
  findByOwner(ownerId: string): Pet[] {
    return Array.from(this.pets.values()).filter(
      (pet) => pet.ownerId === ownerId
    );
  }

  /**
   * 全ペットを取得（テスト用）
   */
  findAll(): Pet[] {
    return Array.from(this.pets.values());
  }

  /**
   * ペットを削除（テスト用）
   */
  delete(id: string): boolean {
    return this.pets.delete(id);
  }

  /**
   * リポジトリをクリア（テスト用）
   */
  clear(): void {
    this.pets.clear();
  }
}
