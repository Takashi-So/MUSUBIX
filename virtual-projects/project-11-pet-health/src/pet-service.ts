// PetCare - ペットサービス実装
// REQ-PET-001-01, REQ-PET-001-02 対応

import {
  Pet,
  PetInput,
  Owner,
  QueryOptions,
} from './types';

// IdGenerator パターン（MUSUBIXから学習）
class PetIdGenerator {
  private counter = 0;

  generate(): string {
    const timestamp = Date.now();
    this.counter++;
    return `PET-${timestamp}-${this.counter}`;
  }

  reset(): void {
    this.counter = 0;
  }
}

// リポジトリインターフェース
export interface IPetRepository {
  save(pet: Pet): Promise<Pet>;
  findById(id: string): Promise<Pet | null>;
  findByOwnerId(ownerId: string): Promise<Pet[]>;
  update(id: string, data: Partial<Pet>): Promise<Pet>;
  delete(id: string): Promise<void>;
}

// インメモリリポジトリ実装
export class InMemoryPetRepository implements IPetRepository {
  private pets: Map<string, Pet> = new Map();

  async save(pet: Pet): Promise<Pet> {
    this.pets.set(pet.id, pet);
    return pet;
  }

  async findById(id: string): Promise<Pet | null> {
    return this.pets.get(id) || null;
  }

  async findByOwnerId(ownerId: string): Promise<Pet[]> {
    return Array.from(this.pets.values()).filter(
      (pet) => pet.ownerId === ownerId
    );
  }

  async update(id: string, data: Partial<Pet>): Promise<Pet> {
    const existing = this.pets.get(id);
    if (!existing) {
      throw new Error(`Pet not found: ${id}`);
    }
    const updated = { ...existing, ...data, updatedAt: new Date() };
    this.pets.set(id, updated);
    return updated;
  }

  async delete(id: string): Promise<void> {
    this.pets.delete(id);
  }

  // テスト用
  clear(): void {
    this.pets.clear();
  }
}

// サービス実装
export class PetService {
  private idGenerator = new PetIdGenerator();

  constructor(private repository: IPetRepository) {}

  /**
   * ペットを登録
   * REQ-PET-001-01: THE システム SHALL ペットの基本情報を登録できること
   */
  async register(ownerId: string, input: PetInput): Promise<Pet> {
    // バリデーション
    if (!input.name || input.name.trim() === '') {
      throw new Error('Pet name is required');
    }
    if (!input.type) {
      throw new Error('Pet type is required');
    }

    const now = new Date();
    const pet: Pet = {
      id: this.idGenerator.generate(),
      ownerId,
      name: input.name.trim(),
      type: input.type,
      breed: input.breed || '',
      birthDate: input.birthDate || now,
      weight: input.weight || 0,
      gender: input.gender || 'unknown',
      photoUrl: input.photoUrl,
      createdAt: now,
      updatedAt: now,
    };

    return this.repository.save(pet);
  }

  /**
   * ペット情報を更新
   */
  async update(petId: string, input: Partial<PetInput>): Promise<Pet> {
    const existing = await this.repository.findById(petId);
    if (!existing) {
      throw new Error(`Pet not found: ${petId}`);
    }

    return this.repository.update(petId, {
      ...input,
      updatedAt: new Date(),
    });
  }

  /**
   * オーナーの全ペットを取得
   * REQ-PET-001-02: THE システム SHALL 複数のペットを関連付けて管理できること
   */
  async getByOwner(ownerId: string): Promise<Pet[]> {
    return this.repository.findByOwnerId(ownerId);
  }

  /**
   * ペットをIDで取得
   */
  async getById(petId: string): Promise<Pet | null> {
    return this.repository.findById(petId);
  }

  /**
   * ペットを削除
   */
  async delete(petId: string): Promise<void> {
    const existing = await this.repository.findById(petId);
    if (!existing) {
      throw new Error(`Pet not found: ${petId}`);
    }
    return this.repository.delete(petId);
  }
}
