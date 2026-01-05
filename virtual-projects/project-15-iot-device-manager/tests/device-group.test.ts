// Tests for DeviceGroup entity
// REQ-DEV-003

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createDeviceGroup,
  addDeviceToGroup,
  removeDeviceFromGroup,
  resetGroupCounter,
  type DeviceGroupInput,
} from '../src/domain/device-group.js';
import { resetDeviceCounter, generateDeviceId } from '../src/domain/device.js';

describe('DeviceGroup', () => {
  beforeEach(() => {
    resetGroupCounter();
    resetDeviceCounter();
  });

  describe('createDeviceGroup', () => {
    it('should create group with valid input', () => {
      const input: DeviceGroupInput = {
        name: 'Floor 1 Sensors',
        description: 'All sensors on floor 1',
      };

      const group = createDeviceGroup(input);

      expect(group.id.value).toMatch(/^GRP-\d{8}-001$/);
      expect(group.name).toBe('Floor 1 Sensors');
      expect(group.description).toBe('All sensors on floor 1');
      expect(group.deviceIds).toEqual([]);
      expect(group.version).toBe(1);
    });

    it('should create group without description', () => {
      const input: DeviceGroupInput = { name: 'Test Group' };
      const group = createDeviceGroup(input);
      expect(group.description).toBeUndefined();
    });

    it('should throw if name is empty', () => {
      expect(() => createDeviceGroup({ name: '' })).toThrow('Group name is required');
    });

    it('should throw if name is too long', () => {
      expect(() => createDeviceGroup({ name: 'a'.repeat(101) })).toThrow(
        '100 characters or less'
      );
    });
  });

  describe('addDeviceToGroup', () => {
    it('should add device to group', () => {
      const group = createDeviceGroup({ name: 'Test Group' });
      const deviceId = generateDeviceId();

      const updated = addDeviceToGroup(group, deviceId);

      expect(updated.deviceIds).toHaveLength(1);
      expect(updated.deviceIds[0].value).toBe(deviceId.value);
      expect(updated.version).toBe(2);
    });

    it('should not add duplicate device', () => {
      const group = createDeviceGroup({ name: 'Test Group' });
      const deviceId = generateDeviceId();

      const updated1 = addDeviceToGroup(group, deviceId);
      const updated2 = addDeviceToGroup(updated1, deviceId);

      expect(updated2.deviceIds).toHaveLength(1);
      expect(updated2.version).toBe(2); // Version unchanged
    });

    it('should allow adding multiple devices', () => {
      const group = createDeviceGroup({ name: 'Test Group' });
      const deviceId1 = generateDeviceId();
      const deviceId2 = generateDeviceId();

      const updated = addDeviceToGroup(addDeviceToGroup(group, deviceId1), deviceId2);

      expect(updated.deviceIds).toHaveLength(2);
    });
  });

  describe('removeDeviceFromGroup', () => {
    it('should remove device from group', () => {
      const group = createDeviceGroup({ name: 'Test Group' });
      const deviceId = generateDeviceId();

      const withDevice = addDeviceToGroup(group, deviceId);
      const removed = removeDeviceFromGroup(withDevice, deviceId);

      expect(removed.deviceIds).toHaveLength(0);
      expect(removed.version).toBe(3);
    });

    it('should do nothing if device not in group', () => {
      const group = createDeviceGroup({ name: 'Test Group' });
      const deviceId = generateDeviceId();

      const removed = removeDeviceFromGroup(group, deviceId);

      expect(removed.deviceIds).toHaveLength(0);
      expect(removed.version).toBe(1); // Version unchanged
    });
  });
});
