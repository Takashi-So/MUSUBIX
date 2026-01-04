/**
 * Entry Exit Service Tests
 * @requirement REQ-ENTRY-001, REQ-ENTRY-002, REQ-ENTRY-003
 * @requirement REQ-FEE-001, REQ-FEE-002, REQ-FEE-003
 * @design DES-PARKING-001 Section 4
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { EntryExitService } from '../src/services/EntryExitService.js';
import { SpaceService } from '../src/services/SpaceService.js';
import { FeeCalculator } from '../src/services/FeeCalculator.js';
import { SpaceRepository } from '../src/repositories/SpaceRepository.js';
import { EntryRepository } from '../src/repositories/EntryRepository.js';
import { ENTRY_ERRORS } from '../src/types/Entry.js';

describe('EntryExitService', () => {
  let entryExitService: EntryExitService;
  let spaceService: SpaceService;
  let spaceRepository: SpaceRepository;
  let entryRepository: EntryRepository;
  let feeCalculator: FeeCalculator;

  beforeEach(() => {
    spaceRepository = new SpaceRepository();
    entryRepository = new EntryRepository();
    spaceService = new SpaceService(spaceRepository);
    feeCalculator = new FeeCalculator();
    entryExitService = new EntryExitService(entryRepository, spaceService, feeCalculator);
  });

  describe('entry', () => {
    it('should create entry record and occupy space', () => {
      // @requirement REQ-ENTRY-001: 入庫時にナンバープレート自動認識
      const space = spaceService.createSpace({ spaceNumber: 'A-001', type: 'standard' }).data!;

      const result = entryExitService.entry({
        plateNumber: '品川300あ1234',
        spaceId: space.id,
        vehicleType: 'car',
      });

      expect(result.success).toBe(true);
      expect(result.data).toBeDefined();
      expect(result.data!.plateNumber).toBe('品川300あ1234');
      expect(result.data!.status).toBe('active');

      // Space should be occupied
      const updatedSpace = spaceService.getSpace(space.id);
      expect(updatedSpace!.state).toBe('occupied');
    });

    it('should reject duplicate entry with same plate number', () => {
      // @requirement REQ-ENTRY-002: 同一ナンバー重複入庫を防止
      const space1 = spaceService.createSpace({ spaceNumber: 'A-001', type: 'standard' }).data!;
      const space2 = spaceService.createSpace({ spaceNumber: 'A-002', type: 'standard' }).data!;

      entryExitService.entry({
        plateNumber: '品川300あ1234',
        spaceId: space1.id,
        vehicleType: 'car',
      });

      const result = entryExitService.entry({
        plateNumber: '品川300あ1234',
        spaceId: space2.id,
        vehicleType: 'car',
      });

      expect(result.success).toBe(false);
      expect(result.error).toBe(ENTRY_ERRORS.DUPLICATE_ENTRY);
    });

    it('should reject if space is not available', () => {
      const space = spaceService.createSpace({ spaceNumber: 'A-001', type: 'standard' }).data!;
      spaceService.occupy(space.id);

      const result = entryExitService.entry({
        plateNumber: '品川300あ1234',
        spaceId: space.id,
        vehicleType: 'car',
      });

      expect(result.success).toBe(false);
      expect(result.error).toBe(ENTRY_ERRORS.SPACE_UNAVAILABLE);
    });

    it('should reject for non-existent space', () => {
      const result = entryExitService.entry({
        plateNumber: '品川300あ1234',
        spaceId: 'non-existent',
        vehicleType: 'car',
      });

      expect(result.success).toBe(false);
      expect(result.error).toBe(ENTRY_ERRORS.SPACE_UNAVAILABLE);
    });
  });

  describe('exit', () => {
    it('should complete exit and calculate fee', () => {
      // @requirement REQ-ENTRY-003: 出庫時に料金自動計算
      const space = spaceService.createSpace({ spaceNumber: 'A-001', type: 'standard' }).data!;
      const entryResult = entryExitService.entry({
        plateNumber: '品川300あ1234',
        spaceId: space.id,
        vehicleType: 'car',
      });

      const exitResult = entryExitService.exit({
        entryId: entryResult.data!.id,
      });

      expect(exitResult.success).toBe(true);
      expect(exitResult.data).toBeDefined();
      expect(exitResult.data!.entry.status).toBe('completed');
      expect(exitResult.data!.entry.exitTime).toBeDefined();
      expect(exitResult.data!.fee).toBeDefined();

      // Space should be released
      const updatedSpace = spaceService.getSpace(space.id);
      expect(updatedSpace!.state).toBe('available');
    });

    it('should reject exit for non-existent entry', () => {
      const result = entryExitService.exit({ entryId: 'non-existent' });

      expect(result.success).toBe(false);
      expect(result.error).toBe(ENTRY_ERRORS.NOT_FOUND);
    });

    it('should reject exit for already exited entry', () => {
      const space = spaceService.createSpace({ spaceNumber: 'A-001', type: 'standard' }).data!;
      const entryResult = entryExitService.entry({
        plateNumber: '品川300あ1234',
        spaceId: space.id,
        vehicleType: 'car',
      });
      entryExitService.exit({ entryId: entryResult.data!.id });

      const result = entryExitService.exit({ entryId: entryResult.data!.id });

      expect(result.success).toBe(false);
      expect(result.error).toBe(ENTRY_ERRORS.ALREADY_EXITED);
    });
  });

  describe('findByPlate', () => {
    it('should find active entry by plate number', () => {
      const space = spaceService.createSpace({ spaceNumber: 'A-001', type: 'standard' }).data!;
      entryExitService.entry({
        plateNumber: '品川300あ1234',
        spaceId: space.id,
        vehicleType: 'car',
      });

      const found = entryExitService.findByPlate('品川300あ1234');

      expect(found).toBeDefined();
      expect(found!.plateNumber).toBe('品川300あ1234');
    });

    it('should return null for exited entry', () => {
      const space = spaceService.createSpace({ spaceNumber: 'A-001', type: 'standard' }).data!;
      const entry = entryExitService.entry({
        plateNumber: '品川300あ1234',
        spaceId: space.id,
        vehicleType: 'car',
      }).data!;
      entryExitService.exit({ entryId: entry.id });

      const found = entryExitService.findByPlate('品川300あ1234');

      expect(found).toBeNull();
    });
  });

  describe('getActiveEntries', () => {
    it('should return all active entries', () => {
      const space1 = spaceService.createSpace({ spaceNumber: 'A-001', type: 'standard' }).data!;
      const space2 = spaceService.createSpace({ spaceNumber: 'A-002', type: 'standard' }).data!;

      entryExitService.entry({
        plateNumber: '品川300あ1234',
        spaceId: space1.id,
        vehicleType: 'car',
      });
      entryExitService.entry({
        plateNumber: '横浜500い5678',
        spaceId: space2.id,
        vehicleType: 'car',
      });

      const activeEntries = entryExitService.getActiveEntries();

      expect(activeEntries).toHaveLength(2);
    });
  });
});
