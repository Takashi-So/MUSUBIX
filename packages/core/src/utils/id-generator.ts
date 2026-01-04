/**
 * ID Generator Utility
 * 
 * Generates unique IDs with counter to prevent duplicates in rapid succession.
 * Based on learnings from 10-project validation (2026-01-04).
 * 
 * @requirement REQ-LEARN-001 - Self-learning system pattern application
 * @pattern unique-id-counter - Combine Date.now() with counter for uniqueness
 * 
 * @packageDocumentation
 * @module utils/id-generator
 */

/**
 * ID Generator class that ensures unique IDs even in rapid succession
 * 
 * Problem solved: Date.now() alone can produce duplicate IDs when
 * multiple entities are created within the same millisecond.
 * 
 * Solution: Combine timestamp with instance counter for guaranteed uniqueness.
 * 
 * @example
 * ```typescript
 * const petIdGen = new IdGenerator('PET');
 * const id1 = petIdGen.generate(); // 'PET-1704326400000-1'
 * const id2 = petIdGen.generate(); // 'PET-1704326400000-2'
 * 
 * // Or use static method for one-off generation
 * const id = IdGenerator.unique('REQ'); // 'REQ-1704326400001-1'
 * ```
 */
export class IdGenerator {
  private counter = 0;
  private lastTimestamp = 0;

  /**
   * Creates a new ID generator with the specified prefix
   * @param prefix - The prefix for generated IDs (e.g., 'PET', 'REQ', 'USR')
   */
  constructor(private readonly prefix: string) {}

  /**
   * Generates a unique ID with format: PREFIX-TIMESTAMP-COUNTER
   * 
   * The counter resets when timestamp changes, but increments
   * within the same millisecond to ensure uniqueness.
   * 
   * @returns A unique ID string
   */
  generate(): string {
    const now = Date.now();
    
    if (now === this.lastTimestamp) {
      this.counter++;
    } else {
      this.counter = 1;
      this.lastTimestamp = now;
    }
    
    return `${this.prefix}-${now}-${this.counter}`;
  }

  /**
   * Generates a short unique ID with format: PREFIX-COUNTER
   * Useful for test fixtures or when timestamp is not needed.
   * 
   * @returns A short unique ID string
   */
  generateShort(): string {
    this.counter++;
    return `${this.prefix}-${this.counter}`;
  }

  /**
   * Resets the counter (useful for testing)
   */
  reset(): void {
    this.counter = 0;
    this.lastTimestamp = 0;
  }

  /**
   * Static method for one-off unique ID generation
   * Creates a new generator instance for each call.
   * 
   * @param prefix - The prefix for the ID
   * @returns A unique ID string
   */
  static unique(prefix: string): string {
    return `${prefix}-${Date.now()}-${Math.random().toString(36).substring(2, 8)}`;
  }

  /**
   * Static method for UUID v4 generation
   * @returns A UUID v4 string
   */
  static uuid(): string {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, (c) => {
      const r = (Math.random() * 16) | 0;
      const v = c === 'x' ? r : (r & 0x3) | 0x8;
      return v.toString(16);
    });
  }
}

/**
 * Pre-configured ID generators for common entity types
 * 
 * @example
 * ```typescript
 * import { idGenerators } from '@nahisaho/musubix-core';
 * 
 * const reqId = idGenerators.requirement.generate(); // 'REQ-...'
 * const desId = idGenerators.design.generate();      // 'DES-...'
 * ```
 */
export const idGenerators = {
  requirement: new IdGenerator('REQ'),
  design: new IdGenerator('DES'),
  task: new IdGenerator('TSK'),
  component: new IdGenerator('CMP'),
  pattern: new IdGenerator('PAT'),
  feedback: new IdGenerator('FB'),
  trace: new IdGenerator('TRC'),
};

/**
 * Validates an ID format
 * @param id - The ID to validate
 * @param prefix - Expected prefix (optional)
 * @returns True if valid format
 */
export function isValidId(id: string, prefix?: string): boolean {
  if (!id || typeof id !== 'string') return false;
  
  const pattern = prefix 
    ? new RegExp(`^${prefix}-\\d+-\\d+$`)
    : /^[A-Z]+-\d+-\d+$/;
  
  return pattern.test(id);
}

/**
 * Extracts timestamp from an ID
 * @param id - The ID to extract timestamp from
 * @returns Date object or null if invalid
 */
export function extractTimestamp(id: string): Date | null {
  const match = id.match(/^[A-Z]+-(\d+)-\d+$/);
  if (!match) return null;
  
  const timestamp = parseInt(match[1], 10);
  if (isNaN(timestamp)) return null;
  
  return new Date(timestamp);
}
