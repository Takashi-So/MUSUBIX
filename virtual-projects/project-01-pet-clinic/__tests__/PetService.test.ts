/**
 * PetService Tests
 * 
 * @requirement REQ-PET-001, REQ-PET-002, REQ-PET-003
 * @design DES-PETCLINIC-001 Section 3.1
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { PetService } from '../src/services/PetService.js';
import { PetRepository } from '../src/repositories/PetRepository.js';
import { PetHistoryRepository } from '../src/repositories/PetHistoryRepository.js';
import type { CreatePetInput } from '../src/types/Pet.js';

describe('PetService', () => {
  let petService: PetService;
  let petRepo: PetRepository;
  let historyRepo: PetHistoryRepository;

  beforeEach(() => {
    petRepo = new PetRepository();
    historyRepo = new PetHistoryRepository();
    petService = new PetService(petRepo, historyRepo);
  });

  describe('register', () => {
    it('should register a pet successfully (REQ-PET-001)', () => {
      const input: CreatePetInput = {
        ownerId: 'USR-001',
        name: 'ポチ',
        species: 'dog',
        breed: '柴犬',
        birthDate: new Date('2020-01-15'),
        weight: 10.5,
        allergies: ['チキン'],
      };

      const result = petService.register(input);

      expect(result.success).toBe(true);
      expect(result.data).toBeDefined();
      expect(result.data!.name).toBe('ポチ');
      expect(result.data!.id).toMatch(/^PET-/);
    });

    it('should fail when name is empty', () => {
      const input: CreatePetInput = {
        ownerId: 'USR-001',
        name: '',
        species: 'dog',
        breed: '柴犬',
        birthDate: new Date(),
        weight: 10,
      };

      const result = petService.register(input);

      expect(result.success).toBe(false);
      expect(result.error).toBe('ペット名は必須です');
    });

    it('should fail when weight is negative', () => {
      const input: CreatePetInput = {
        ownerId: 'USR-001',
        name: 'ポチ',
        species: 'dog',
        breed: '柴犬',
        birthDate: new Date(),
        weight: -5,
      };

      const result = petService.register(input);

      expect(result.success).toBe(false);
      expect(result.error).toBe('体重は0以上である必要があります');
    });
  });

  describe('update', () => {
    it('should update pet and save history (REQ-PET-002)', () => {
      // 先にペットを登録
      const createResult = petService.register({
        ownerId: 'USR-001',
        name: 'ポチ',
        species: 'dog',
        breed: '柴犬',
        birthDate: new Date('2020-01-15'),
        weight: 10.5,
      });

      const petId = createResult.data!.id;

      // 更新
      const updateResult = petService.update(
        petId,
        { weight: 11.0, name: 'ポチ太郎' },
        'USR-001'
      );

      expect(updateResult.success).toBe(true);
      expect(updateResult.data!.weight).toBe(11.0);
      expect(updateResult.data!.name).toBe('ポチ太郎');

      // 履歴を確認
      const history = petService.getHistory(petId);
      expect(history.length).toBe(1);
      expect(history[0].snapshot.weight).toBe(10.5);
    });

    it('should fail when pet not found', () => {
      const result = petService.update('NONEXISTENT', { weight: 10 }, 'USR-001');

      expect(result.success).toBe(false);
      expect(result.error).toBe('ペットが見つかりません');
    });
  });

  describe('findByOwner', () => {
    it('should return all pets for owner (REQ-PET-003)', () => {
      // 同じオーナーで複数ペットを登録
      petService.register({
        ownerId: 'USR-001',
        name: 'ポチ',
        species: 'dog',
        breed: '柴犬',
        birthDate: new Date(),
        weight: 10,
      });

      petService.register({
        ownerId: 'USR-001',
        name: 'タマ',
        species: 'cat',
        breed: '三毛猫',
        birthDate: new Date(),
        weight: 4,
      });

      petService.register({
        ownerId: 'USR-002',
        name: 'ミケ',
        species: 'cat',
        breed: 'アメショー',
        birthDate: new Date(),
        weight: 5,
      });

      const pets = petService.findByOwner('USR-001');

      expect(pets.length).toBe(2);
      expect(pets.map(p => p.name).sort()).toEqual(['タマ', 'ポチ']);
    });

    it('should return empty array when owner has no pets', () => {
      const pets = petService.findByOwner('NONEXISTENT');
      expect(pets).toEqual([]);
    });
  });
});
