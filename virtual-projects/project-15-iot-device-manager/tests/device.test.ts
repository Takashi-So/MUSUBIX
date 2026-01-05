// Tests for Device entity
// REQ-DEV-001, REQ-DEV-002

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createDevice,
  updateDeviceStatus,
  generateDeviceId,
  parseFirmwareVersion,
  formatFirmwareVersion,
  isValidStatusTransition,
  resetDeviceCounter,
  type DeviceInput,
  type DeviceStatus,
} from '../src/domain/device.js';

describe('Device', () => {
  beforeEach(() => {
    resetDeviceCounter();
  });

  describe('generateDeviceId', () => {
    it('should generate ID with DEV prefix', () => {
      const id = generateDeviceId();
      expect(id.value).toMatch(/^DEV-\d{8}-\d{3}$/);
    });

    it('should generate sequential IDs', () => {
      const id1 = generateDeviceId();
      const id2 = generateDeviceId();
      expect(id1.value).toMatch(/-001$/);
      expect(id2.value).toMatch(/-002$/);
    });
  });

  describe('parseFirmwareVersion', () => {
    it('should parse valid version', () => {
      const version = parseFirmwareVersion('2.1.3');
      expect(version).toEqual({ major: 2, minor: 1, patch: 3 });
    });

    it('should throw for invalid format', () => {
      expect(() => parseFirmwareVersion('v2.1.3')).toThrow();
      expect(() => parseFirmwareVersion('2.1')).toThrow();
      expect(() => parseFirmwareVersion('invalid')).toThrow();
    });
  });

  describe('formatFirmwareVersion', () => {
    it('should format version correctly', () => {
      const formatted = formatFirmwareVersion({ major: 2, minor: 1, patch: 3 });
      expect(formatted).toBe('2.1.3');
    });
  });

  describe('createDevice', () => {
    it('should create device with valid input', () => {
      const input: DeviceInput = {
        name: 'Temperature Sensor',
        type: 'sensor',
        protocol: 'mqtt',
        location: 'Room A',
        firmwareVersion: '1.2.0',
      };

      const device = createDevice(input);

      expect(device.id.value).toMatch(/^DEV-/);
      expect(device.name).toBe('Temperature Sensor');
      expect(device.type).toBe('sensor');
      expect(device.status).toBe('offline');
      expect(device.protocol).toBe('mqtt');
      expect(device.location).toBe('Room A');
      expect(device.firmwareVersion).toEqual({ major: 1, minor: 2, patch: 0 });
      expect(device.version).toBe(1);
      expect(device.registeredAt).toBeInstanceOf(Date);
    });

    it('should use default firmware version if not provided', () => {
      const input: DeviceInput = {
        name: 'Actuator',
        type: 'actuator',
        protocol: 'http',
      };

      const device = createDevice(input);
      expect(device.firmwareVersion).toEqual({ major: 1, minor: 0, patch: 0 });
    });

    it('should throw if name is empty', () => {
      const input: DeviceInput = { name: '', type: 'sensor', protocol: 'mqtt' };
      expect(() => createDevice(input)).toThrow('Device name is required');
    });

    it('should throw if name is too long', () => {
      const input: DeviceInput = {
        name: 'a'.repeat(101),
        type: 'sensor',
        protocol: 'mqtt',
      };
      expect(() => createDevice(input)).toThrow('100 characters or less');
    });

    it('should throw for invalid device type', () => {
      const input = {
        name: 'Test',
        type: 'invalid' as any,
        protocol: 'mqtt',
      };
      expect(() => createDevice(input)).toThrow('Invalid device type');
    });

    it('should throw for invalid protocol', () => {
      const input: DeviceInput = {
        name: 'Test',
        type: 'sensor',
        protocol: 'invalid' as any,
      };
      expect(() => createDevice(input)).toThrow('Invalid protocol');
    });
  });

  describe('isValidStatusTransition', () => {
    const testCases: { from: DeviceStatus; to: DeviceStatus; valid: boolean }[] = [
      { from: 'offline', to: 'online', valid: true },
      { from: 'offline', to: 'maintenance', valid: true },
      { from: 'offline', to: 'error', valid: true },
      { from: 'online', to: 'offline', valid: true },
      { from: 'online', to: 'maintenance', valid: true },
      { from: 'online', to: 'error', valid: true },
      { from: 'maintenance', to: 'offline', valid: true },
      { from: 'maintenance', to: 'online', valid: true },
      { from: 'maintenance', to: 'error', valid: false },
      { from: 'error', to: 'offline', valid: true },
      { from: 'error', to: 'maintenance', valid: true },
      { from: 'error', to: 'online', valid: false },
      { from: 'online', to: 'online', valid: true }, // Same status
    ];

    testCases.forEach(({ from, to, valid }) => {
      it(`should ${valid ? 'allow' : 'reject'} transition from '${from}' to '${to}'`, () => {
        expect(isValidStatusTransition(from, to)).toBe(valid);
      });
    });
  });

  describe('updateDeviceStatus', () => {
    it('should update status with valid transition', () => {
      const input: DeviceInput = {
        name: 'Sensor',
        type: 'sensor',
        protocol: 'mqtt',
      };
      const device = createDevice(input);
      const updated = updateDeviceStatus(device, 'online');

      expect(updated.status).toBe('online');
      expect(updated.version).toBe(2);
      expect(updated.lastSeenAt).toBeInstanceOf(Date);
    });

    it('should throw for invalid transition', () => {
      const input: DeviceInput = {
        name: 'Sensor',
        type: 'sensor',
        protocol: 'mqtt',
      };
      const device = createDevice(input);
      const onlineDevice = updateDeviceStatus(device, 'online');
      const errorDevice = updateDeviceStatus(onlineDevice, 'error');

      // error -> online is invalid
      expect(() => updateDeviceStatus(errorDevice, 'online')).toThrow(
        "Invalid status transition from 'error' to 'online'"
      );
    });
  });
});
