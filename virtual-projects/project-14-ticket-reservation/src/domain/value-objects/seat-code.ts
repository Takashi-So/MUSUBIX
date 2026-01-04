/**
 * SeatCode Value Object
 * Traces to: REQ-TR-010
 * 
 * Represents a seat identifier in format "ROW-NUM" (e.g., "A-1", "B-12")
 */
import { Result, ok, err, ValidationError } from '../../shared/result.js';

const ROW_PATTERN = /^[A-Z]{1,2}$/;
const MAX_NUMBER = 100;

export interface SeatCode {
  readonly row: string;
  readonly number: number;
  readonly code: string;
}

/**
 * Create a SeatCode from row letter and seat number
 */
export function createSeatCode(row: string, num: number): Result<SeatCode, ValidationError> {
  const normalizedRow = row.toUpperCase();
  
  if (!normalizedRow || !ROW_PATTERN.test(normalizedRow)) {
    return err(new ValidationError('Row must be 1-2 uppercase letters (A-Z, AA-ZZ)'));
  }
  
  if (!Number.isInteger(num) || num < 1 || num > MAX_NUMBER) {
    return err(new ValidationError(`Seat number must be between 1 and ${MAX_NUMBER}`));
  }
  
  return ok({
    row: normalizedRow,
    number: num,
    code: `${normalizedRow}-${num}`,
  });
}

/**
 * Parse from string format "ROW-NUM"
 */
export function parseSeatCode(code: string): Result<SeatCode, ValidationError> {
  if (!code) {
    return err(new ValidationError('Seat code cannot be empty'));
  }
  
  const match = code.match(/^([A-Za-z]{1,2})-(\d+)$/);
  
  if (!match) {
    return err(new ValidationError('Invalid seat code format. Expected "ROW-NUM" (e.g., "A-1", "B-12")'));
  }
  
  const row = match[1].toUpperCase();
  const num = parseInt(match[2], 10);
  
  return createSeatCode(row, num);
}

/**
 * Check equality
 */
export function seatCodeEquals(s1: SeatCode, s2: SeatCode): boolean {
  return s1.row === s2.row && s1.number === s2.number;
}

/**
 * Compare for sorting (by row then number)
 */
export function compareSeatCodes(s1: SeatCode, s2: SeatCode): number {
  if (s1.row !== s2.row) {
    return s1.row.localeCompare(s2.row);
  }
  return s1.number - s2.number;
}
