/**
 * SeatConfig Value Object Tests
 * Traces to: REQ-TR-012
 */
import { describe, it, expect } from 'vitest';
import { createSeatConfig } from '../../../src/domain/value-objects/seat-config.js';

describe('SeatConfig Value Object', () => {
  describe('createSeatConfig', () => {
    it('should create valid seat config', () => {
      const result = createSeatConfig(10, 20);
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.rows).toBe(10);
        expect(result.value.seatsPerRow).toBe(20);
        expect(result.value.totalSeats).toBe(200);
      }
    });

    it('should reject 0 rows', () => {
      const result = createSeatConfig(0, 20);
      expect(result.isErr()).toBe(true);
    });

    it('should reject 0 seats per row', () => {
      const result = createSeatConfig(10, 0);
      expect(result.isErr()).toBe(true);
    });

    it('should accept maximum total seats (10,000)', () => {
      const result = createSeatConfig(100, 100);
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.totalSeats).toBe(10000);
      }
    });

    it('should reject total seats exceeding 10,000', () => {
      // 100 rows × 101 seats = 10,100 > 10,000
      const result = createSeatConfig(100, 101);
      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('10,');
      }
    });

    it('should reject negative rows', () => {
      const result = createSeatConfig(-1, 20);
      expect(result.isErr()).toBe(true);
    });

    it('should reject negative seats per row', () => {
      const result = createSeatConfig(10, -1);
      expect(result.isErr()).toBe(true);
    });
  });

  describe('generateSeatCodes', () => {
    it('should generate correct seat codes for small config', () => {
      const result = createSeatConfig(2, 3);
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        const codes = result.value.generateSeatCodes();
        expect(codes).toHaveLength(6);
        expect(codes[0].code).toBe('A-1');
        expect(codes[1].code).toBe('A-2');
        expect(codes[2].code).toBe('A-3');
        expect(codes[3].code).toBe('B-1');
        expect(codes[4].code).toBe('B-2');
        expect(codes[5].code).toBe('B-3');
      }
    });

    it('should handle rows beyond Z (AA, AB, etc.)', () => {
      const result = createSeatConfig(27, 1);
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        const codes = result.value.generateSeatCodes();
        expect(codes[0].code).toBe('A-1');
        expect(codes[25].code).toBe('Z-1');
        expect(codes[26].code).toBe('AA-1');
      }
    });
  });
});
