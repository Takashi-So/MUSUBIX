/**
 * ID Generator Tests
 * 
 * @description Tests for the ID generation utility discovered from 10-project validation
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { 
  IdGenerator, 
  idGenerators, 
  isValidId, 
  extractTimestamp 
} from '../../../src/utils/id-generator.js';

describe('IdGenerator', () => {
  let generator: IdGenerator;

  beforeEach(() => {
    generator = new IdGenerator('TEST');
  });

  describe('generate()', () => {
    it('should generate unique IDs with prefix', () => {
      const id = generator.generate();
      expect(id).toMatch(/^TEST-\d+-\d+$/);
    });

    it('should generate different IDs on successive calls', () => {
      const id1 = generator.generate();
      const id2 = generator.generate();
      const id3 = generator.generate();
      
      expect(id1).not.toBe(id2);
      expect(id2).not.toBe(id3);
      expect(id1).not.toBe(id3);
    });

    it('should increment counter within same millisecond', () => {
      // Generate multiple IDs rapidly
      const ids = Array.from({ length: 100 }, () => generator.generate());
      const uniqueIds = new Set(ids);
      
      // All IDs should be unique
      expect(uniqueIds.size).toBe(100);
    });

    it('should handle high-volume ID generation without duplicates', () => {
      const ids = new Set<string>();
      
      for (let i = 0; i < 1000; i++) {
        const id = generator.generate();
        expect(ids.has(id)).toBe(false);
        ids.add(id);
      }
      
      expect(ids.size).toBe(1000);
    });
  });

  describe('generateShort()', () => {
    it('should generate short IDs without timestamp', () => {
      const id = generator.generateShort();
      expect(id).toMatch(/^TEST-\d+$/);
    });

    it('should increment counter for short IDs', () => {
      const id1 = generator.generateShort();
      const id2 = generator.generateShort();
      
      expect(id1).toBe('TEST-1');
      expect(id2).toBe('TEST-2');
    });
  });

  describe('reset()', () => {
    it('should reset counter', () => {
      generator.generateShort();
      generator.generateShort();
      generator.reset();
      
      const id = generator.generateShort();
      expect(id).toBe('TEST-1');
    });
  });

  describe('static unique()', () => {
    it('should generate unique ID with random suffix', () => {
      const id = IdGenerator.unique('REQ');
      expect(id).toMatch(/^REQ-\d+-[a-z0-9]+$/);
    });

    it('should generate different IDs each time', () => {
      const id1 = IdGenerator.unique('REQ');
      const id2 = IdGenerator.unique('REQ');
      
      expect(id1).not.toBe(id2);
    });
  });

  describe('static uuid()', () => {
    it('should generate valid UUID v4 format', () => {
      const uuid = IdGenerator.uuid();
      expect(uuid).toMatch(/^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/);
    });

    it('should generate unique UUIDs', () => {
      const uuids = Array.from({ length: 100 }, () => IdGenerator.uuid());
      const uniqueUuids = new Set(uuids);
      
      expect(uniqueUuids.size).toBe(100);
    });
  });
});

describe('idGenerators', () => {
  it('should have pre-configured generators for common types', () => {
    expect(idGenerators.requirement).toBeInstanceOf(IdGenerator);
    expect(idGenerators.design).toBeInstanceOf(IdGenerator);
    expect(idGenerators.task).toBeInstanceOf(IdGenerator);
    expect(idGenerators.component).toBeInstanceOf(IdGenerator);
    expect(idGenerators.pattern).toBeInstanceOf(IdGenerator);
    expect(idGenerators.feedback).toBeInstanceOf(IdGenerator);
    expect(idGenerators.trace).toBeInstanceOf(IdGenerator);
  });

  it('should generate IDs with correct prefixes', () => {
    expect(idGenerators.requirement.generate()).toMatch(/^REQ-/);
    expect(idGenerators.design.generate()).toMatch(/^DES-/);
    expect(idGenerators.task.generate()).toMatch(/^TSK-/);
    expect(idGenerators.component.generate()).toMatch(/^CMP-/);
    expect(idGenerators.pattern.generate()).toMatch(/^PAT-/);
    expect(idGenerators.feedback.generate()).toMatch(/^FB-/);
    expect(idGenerators.trace.generate()).toMatch(/^TRC-/);
  });
});

describe('isValidId()', () => {
  it('should validate correct ID format', () => {
    expect(isValidId('REQ-1704326400000-1')).toBe(true);
    expect(isValidId('DES-1704326400000-42')).toBe(true);
    expect(isValidId('TSK-1704326400000-100')).toBe(true);
  });

  it('should validate with specific prefix', () => {
    expect(isValidId('REQ-1704326400000-1', 'REQ')).toBe(true);
    expect(isValidId('REQ-1704326400000-1', 'DES')).toBe(false);
  });

  it('should reject invalid formats', () => {
    expect(isValidId('')).toBe(false);
    expect(isValidId('invalid')).toBe(false);
    expect(isValidId('REQ-abc-1')).toBe(false);
    expect(isValidId('req-1704326400000-1')).toBe(false); // lowercase
    expect(isValidId(null as any)).toBe(false);
    expect(isValidId(undefined as any)).toBe(false);
  });
});

describe('extractTimestamp()', () => {
  it('should extract timestamp from valid ID', () => {
    const timestamp = 1704326400000;
    const date = extractTimestamp(`REQ-${timestamp}-1`);
    
    expect(date).toBeInstanceOf(Date);
    expect(date?.getTime()).toBe(timestamp);
  });

  it('should return null for invalid ID', () => {
    expect(extractTimestamp('invalid')).toBeNull();
    expect(extractTimestamp('')).toBeNull();
    expect(extractTimestamp('REQ-abc-1')).toBeNull();
  });
});
