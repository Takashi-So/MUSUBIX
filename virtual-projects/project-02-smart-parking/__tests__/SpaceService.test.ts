/**
 * Space Service Tests
 * @requirement REQ-SPACE-001, REQ-SPACE-002, REQ-SPACE-003
 * @design DES-PARKING-001 Section 4
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { SpaceService } from '../src/services/SpaceService.js';
import { SpaceRepository } from '../src/repositories/SpaceRepository.js';
import { SPACE_ERRORS } from '../src/types/Space.js';

describe('SpaceService', () => {
  let service: SpaceService;
  let repository: SpaceRepository;

  beforeEach(() => {
    repository = new SpaceRepository();
    service = new SpaceService(repository);
  });

  describe('createSpace', () => {
    it('should create a new parking space with available state', () => {
      // @requirement REQ-SPACE-001: 初期状態は「空き」
      const result = service.createSpace({
        spaceNumber: 'A-001',
        type: 'standard',
        floor: 1,
        section: 'A',
      });

      expect(result.success).toBe(true);
      expect(result.data).toBeDefined();
      expect(result.data!.spaceNumber).toBe('A-001');
      expect(result.data!.state).toBe('available');
      expect(result.data!.type).toBe('standard');
    });

    it('should reject duplicate space numbers', () => {
      service.createSpace({ spaceNumber: 'A-001', type: 'standard' });
      const result = service.createSpace({ spaceNumber: 'A-001', type: 'standard' });

      expect(result.success).toBe(false);
      expect(result.error).toBe(SPACE_ERRORS.ALREADY_EXISTS);
    });
  });

  describe('createBulk', () => {
    it('should create multiple spaces at once', () => {
      const result = service.createBulk([
        { spaceNumber: 'A-001', type: 'standard' },
        { spaceNumber: 'A-002', type: 'standard' },
        { spaceNumber: 'A-003', type: 'compact' },
      ]);

      expect(result.success).toBe(true);
      expect(result.data).toHaveLength(3);
    });
  });

  describe('occupy', () => {
    it('should change space state to occupied', () => {
      const createResult = service.createSpace({ spaceNumber: 'A-001', type: 'standard' });
      const spaceId = createResult.data!.id;

      const result = service.occupy(spaceId);

      expect(result.success).toBe(true);
      expect(result.data!.state).toBe('occupied');
    });

    it('should reject if space is already occupied', () => {
      // @requirement REQ-SPACE-002: 満車時は入庫不可
      const createResult = service.createSpace({ spaceNumber: 'A-001', type: 'standard' });
      const spaceId = createResult.data!.id;
      service.occupy(spaceId);

      const result = service.occupy(spaceId);

      expect(result.success).toBe(false);
      expect(result.error).toBe(SPACE_ERRORS.OCCUPIED);
    });

    it('should return error for non-existent space', () => {
      const result = service.occupy('non-existent-id');

      expect(result.success).toBe(false);
      expect(result.error).toBe(SPACE_ERRORS.NOT_FOUND);
    });
  });

  describe('release', () => {
    it('should change space state back to available', () => {
      const createResult = service.createSpace({ spaceNumber: 'A-001', type: 'standard' });
      const spaceId = createResult.data!.id;
      service.occupy(spaceId);

      const result = service.release(spaceId);

      expect(result.success).toBe(true);
      expect(result.data!.state).toBe('available');
    });

    it('should reject if space is not occupied', () => {
      const createResult = service.createSpace({ spaceNumber: 'A-001', type: 'standard' });
      const spaceId = createResult.data!.id;

      const result = service.release(spaceId);

      expect(result.success).toBe(false);
      expect(result.error).toBe(SPACE_ERRORS.NOT_OCCUPIED);
    });
  });

  describe('setMaintenance', () => {
    it('should change space state to maintenance', () => {
      const createResult = service.createSpace({ spaceNumber: 'A-001', type: 'standard' });
      const spaceId = createResult.data!.id;

      const result = service.setMaintenance(spaceId);

      expect(result.success).toBe(true);
      expect(result.data!.state).toBe('maintenance');
    });
  });

  describe('findAvailable', () => {
    it('should return only available spaces', () => {
      // @requirement REQ-SPACE-003: 空き状況をリアルタイム表示
      const space1 = service.createSpace({ spaceNumber: 'A-001', type: 'standard' }).data!;
      const space2 = service.createSpace({ spaceNumber: 'A-002', type: 'standard' }).data!;
      service.createSpace({ spaceNumber: 'A-003', type: 'compact' });
      service.occupy(space2.id);

      const available = service.findAvailable();

      expect(available).toHaveLength(2);
    });

    it('should filter by type', () => {
      service.createSpace({ spaceNumber: 'A-001', type: 'standard' });
      service.createSpace({ spaceNumber: 'A-002', type: 'compact' });
      service.createSpace({ spaceNumber: 'A-003', type: 'handicap' });

      const compactOnly = service.findAvailable('compact');

      expect(compactOnly).toHaveLength(1);
      expect(compactOnly[0].type).toBe('compact');
    });
  });

  describe('getStats', () => {
    it('should return correct statistics', () => {
      // @requirement REQ-SPACE-003: 空き状況をリアルタイム表示
      const space1 = service.createSpace({ spaceNumber: 'A-001', type: 'standard' }).data!;
      service.createSpace({ spaceNumber: 'A-002', type: 'standard' });
      const space3 = service.createSpace({ spaceNumber: 'A-003', type: 'standard' }).data!;
      service.occupy(space1.id);
      service.setMaintenance(space3.id);

      const stats = service.getStats();

      expect(stats.total).toBe(3);
      expect(stats.available).toBe(1);
      expect(stats.occupied).toBe(1);
      expect(stats.maintenance).toBe(1);
      expect(stats.reserved).toBe(0);
    });
  });

  describe('isFull', () => {
    it('should return true when all spaces are occupied', () => {
      const space = service.createSpace({ spaceNumber: 'A-001', type: 'standard' }).data!;
      service.occupy(space.id);

      expect(service.isFull()).toBe(true);
    });

    it('should return false when spaces are available', () => {
      service.createSpace({ spaceNumber: 'A-001', type: 'standard' });

      expect(service.isFull()).toBe(false);
    });
  });
});
