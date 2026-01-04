/**
 * SeatCode Value Object Tests
 * Traces to: REQ-TR-011
 */
import { describe, it, expect } from 'vitest';
import { createSeatCode, parseSeatCode, seatCodeEquals } from '../../../src/domain/value-objects/seat-code.js';

describe('SeatCode Value Object', () => {
  describe('createSeatCode', () => {
    it('should create valid seat code', () => {
      const result = createSeatCode('A', 1);
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.row).toBe('A');
        expect(result.value.number).toBe(1);
        expect(result.value.code).toBe('A-1');
      }
    });

    it('should support multiple letters (AA-1)', () => {
      const result = createSeatCode('AA', 1);
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.code).toBe('AA-1');
      }
    });

    it('should reject empty row', () => {
      const result = createSeatCode('', 1);
      expect(result.isErr()).toBe(true);
    });

    it('should reject seat number 0', () => {
      const result = createSeatCode('A', 0);
      expect(result.isErr()).toBe(true);
    });

    it('should reject negative seat number', () => {
      const result = createSeatCode('A', -1);
      expect(result.isErr()).toBe(true);
    });

    it('should reject non-alphabetic row', () => {
      const result = createSeatCode('1', 1);
      expect(result.isErr()).toBe(true);
    });

    it('should reject seat number > 100', () => {
      const result = createSeatCode('A', 101);
      expect(result.isErr()).toBe(true);
    });
  });

  describe('parseSeatCode', () => {
    it('should parse valid seat code string', () => {
      const result = parseSeatCode('B-5');
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.row).toBe('B');
        expect(result.value.number).toBe(5);
      }
    });

    it('should parse multi-letter row (AA-10)', () => {
      const result = parseSeatCode('AA-10');
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.row).toBe('AA');
        expect(result.value.number).toBe(10);
      }
    });

    it('should reject invalid format', () => {
      const result = parseSeatCode('A1');
      expect(result.isErr()).toBe(true);
    });

    it('should reject empty string', () => {
      const result = parseSeatCode('');
      expect(result.isErr()).toBe(true);
    });

    it('should be case-insensitive for row', () => {
      const result = parseSeatCode('a-1');
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.row).toBe('A'); // normalized to uppercase
      }
    });
  });

  describe('seatCodeEquals', () => {
    it('should return true for identical seat codes', () => {
      const s1 = createSeatCode('A', 1);
      const s2 = createSeatCode('A', 1);
      
      if (s1.isOk() && s2.isOk()) {
        expect(seatCodeEquals(s1.value, s2.value)).toBe(true);
      }
    });

    it('should return false for different seat codes', () => {
      const s1 = createSeatCode('A', 1);
      const s2 = createSeatCode('A', 2);
      
      if (s1.isOk() && s2.isOk()) {
        expect(seatCodeEquals(s1.value, s2.value)).toBe(false);
      }
    });
  });
});
