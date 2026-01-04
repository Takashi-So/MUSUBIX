/**
 * SeatConfig Value Object
 * Traces to: REQ-TR-005
 * 
 * Represents venue seat configuration (rows × seats per row)
 */
import { Result, ok, err, ValidationError } from '../../shared/result.js';
import { SeatCode, createSeatCode } from './seat-code.js';

const MAX_TOTAL_SEATS = 10_000;
const MAX_ROWS = 100; // Support larger venues
const MAX_SEATS_PER_ROW = 1000;

export interface SeatConfig {
  readonly rows: number;
  readonly seatsPerRow: number;
  readonly totalSeats: number;
  generateSeatCodes(): SeatCode[];
}

/**
 * Convert row index (0-based) to letter(s) (A, B, ..., Z, AA, AB, ...)
 */
function numberToRowLetter(index: number): string {
  if (index < 26) {
    return String.fromCharCode(65 + index); // A-Z
  }
  // For rows beyond Z, use AA, AB, etc.
  const first = Math.floor(index / 26) - 1;
  const second = index % 26;
  return String.fromCharCode(65 + first) + String.fromCharCode(65 + second);
}

/**
 * Create a SeatConfig with validation
 */
export function createSeatConfig(rows: number, seatsPerRow: number): Result<SeatConfig, ValidationError> {
  if (!Number.isInteger(rows) || rows < 1) {
    return err(new ValidationError('Rows must be at least 1'));
  }
  
  if (rows > MAX_ROWS) {
    return err(new ValidationError(`Rows must not exceed ${MAX_ROWS}`));
  }
  
  if (!Number.isInteger(seatsPerRow) || seatsPerRow < 1) {
    return err(new ValidationError('Seats per row must be at least 1'));
  }
  
  if (seatsPerRow > MAX_SEATS_PER_ROW) {
    return err(new ValidationError(`Seats per row must not exceed ${MAX_SEATS_PER_ROW}`));
  }
  
  const totalSeats = rows * seatsPerRow;
  if (totalSeats > MAX_TOTAL_SEATS) {
    return err(new ValidationError(
      `Total seats (${totalSeats.toLocaleString()}) exceeds maximum of ${MAX_TOTAL_SEATS.toLocaleString()}`
    ));
  }
  
  return ok({
    rows,
    seatsPerRow,
    totalSeats,
    generateSeatCodes(): SeatCode[] {
      const codes: SeatCode[] = [];
      
      for (let r = 0; r < rows; r++) {
        const rowLetter = numberToRowLetter(r);
        for (let s = 1; s <= seatsPerRow; s++) {
          const result = createSeatCode(rowLetter, s);
          if (result.isOk()) {
            codes.push(result.value);
          }
        }
      }
      
      return codes;
    },
  });
}
