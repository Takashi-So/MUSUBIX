/**
 * Pet Types - ペットエンティティの型定義
 * 
 * @requirement REQ-PET-001, REQ-PET-002, REQ-PET-003
 * @design DES-PETCLINIC-001 Section 4.1
 */

export type PetSpecies = 'dog' | 'cat' | 'bird' | 'rabbit' | 'hamster' | 'other';

export interface Pet {
  id: string;
  ownerId: string;
  name: string;
  species: PetSpecies;
  breed: string;
  birthDate: Date;
  weight: number;
  allergies: string[];
  createdAt: Date;
  updatedAt: Date;
}

export interface CreatePetInput {
  ownerId: string;
  name: string;
  species: PetSpecies;
  breed: string;
  birthDate: Date;
  weight: number;
  allergies?: string[];
}

export interface UpdatePetInput {
  name?: string;
  species?: PetSpecies;
  breed?: string;
  birthDate?: Date;
  weight?: number;
  allergies?: string[];
}

export interface PetHistoryEntry {
  id: string;
  petId: string;
  snapshot: Pet;
  changedAt: Date;
  changedBy: string;
}
