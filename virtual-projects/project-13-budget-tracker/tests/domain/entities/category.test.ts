/**
 * Category Entity Tests
 * Traces to: REQ-BT-001, REQ-BT-002, REQ-BT-003, REQ-BT-004
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { 
  createCategory, 
  generateCategoryId, 
  resetCategoryCounter,
  CategoryStatus,
  isValidCategoryTransition 
} from '../../../src/domain/entities/category';
import { Money } from '../../../src/domain/value-objects/money';

describe('Category Entity', () => {
  beforeEach(() => {
    resetCategoryCounter();
  });

  describe('createCategory', () => {
    it('should create a category with valid input', () => {
      const result = createCategory({
        userId: 'USR-A1B2C3D4',
        name: '食費',
        description: '日常の食料品',
        monthlyLimit: 50000,
      });

      expect(result.isOk()).toBe(true);
      const category = result.unwrap();
      expect(category.name).toBe('食費');
      expect(category.description).toBe('日常の食料品');
      expect(category.monthlyLimit.toNumber()).toBe(50000);
      expect(category.status).toBe('active');
    });

    it('should reject name longer than 50 characters', () => {
      const result = createCategory({
        userId: 'USR-A1B2C3D4',
        name: 'a'.repeat(51),
        description: 'test',
        monthlyLimit: 10000,
      });

      expect(result.isErr()).toBe(true);
      expect(result.unwrapErr().message).toContain('1-50');
    });

    it('should reject empty name', () => {
      const result = createCategory({
        userId: 'USR-A1B2C3D4',
        name: '',
        description: 'test',
        monthlyLimit: 10000,
      });

      expect(result.isErr()).toBe(true);
    });

    it('should reject invalid monthly limit', () => {
      const result = createCategory({
        userId: 'USR-A1B2C3D4',
        name: '食費',
        description: 'test',
        monthlyLimit: 0,
      });

      expect(result.isErr()).toBe(true);
    });

    it('should accept name with exactly 50 characters', () => {
      const result = createCategory({
        userId: 'USR-A1B2C3D4',
        name: 'a'.repeat(50),
        description: 'test',
        monthlyLimit: 10000,
      });

      expect(result.isOk()).toBe(true);
    });

    it('should accept name with exactly 1 character', () => {
      const result = createCategory({
        userId: 'USR-A1B2C3D4',
        name: 'A',
        description: 'test',
        monthlyLimit: 10000,
      });

      expect(result.isOk()).toBe(true);
    });
  });

  describe('generateCategoryId', () => {
    it('should generate ID in CAT-YYYYMMDD-NNN format', () => {
      const id = generateCategoryId();
      expect(id).toMatch(/^CAT-\d{8}-\d{3}$/);
    });

    it('should increment counter for each call', () => {
      const id1 = generateCategoryId();
      const id2 = generateCategoryId();
      expect(id1).toMatch(/-001$/);
      expect(id2).toMatch(/-002$/);
    });

    it('should reset counter correctly', () => {
      generateCategoryId();
      generateCategoryId();
      resetCategoryCounter();
      const id = generateCategoryId();
      expect(id).toMatch(/-001$/);
    });
  });

  describe('CategoryStatus transitions (BP-DESIGN-001)', () => {
    it('should allow transition from active to archived', () => {
      expect(isValidCategoryTransition('active', 'archived')).toBe(true);
    });

    it('should not allow transition from archived to active', () => {
      expect(isValidCategoryTransition('archived', 'active')).toBe(false);
    });

    it('should not allow transition from archived to archived', () => {
      expect(isValidCategoryTransition('archived', 'archived')).toBe(false);
    });

    it('should not allow transition from active to active', () => {
      expect(isValidCategoryTransition('active', 'active')).toBe(false);
    });
  });
});
