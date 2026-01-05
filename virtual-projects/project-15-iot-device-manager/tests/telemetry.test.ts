// Tests for Telemetry entity
// REQ-DATA-001, REQ-DATA-002, REQ-DATA-003

import { describe, it, expect, beforeEach } from 'vitest';
import {
  validateAndCreateTelemetry,
  validateTelemetryQuery,
  resetTelemetryCounter,
  type TelemetryInput,
  type TelemetryQuery,
} from '../src/domain/telemetry.js';

describe('Telemetry', () => {
  beforeEach(() => {
    resetTelemetryCounter();
  });

  describe('validateAndCreateTelemetry', () => {
    it('should create telemetry with valid input', () => {
      const input: TelemetryInput = {
        deviceId: 'DEV-20250106-001',
        timestamp: new Date().toISOString(),
        value: 25.5,
        unit: '°C',
        metadata: { location: 'Room A' },
      };

      const result = validateAndCreateTelemetry(input);

      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.telemetry.deviceId.value).toBe('DEV-20250106-001');
        expect(result.telemetry.value).toBe(25.5);
        expect(result.telemetry.unit).toBe('°C');
        expect(result.telemetry.metadata).toEqual({ location: 'Room A' });
      }
    });

    it('should reject invalid device ID format', () => {
      const input: TelemetryInput = {
        deviceId: 'invalid-id',
        timestamp: new Date().toISOString(),
        value: 25.5,
        unit: '°C',
      };

      const result = validateAndCreateTelemetry(input);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('Invalid device ID format');
      }
    });

    it('should reject empty device ID', () => {
      const input: TelemetryInput = {
        deviceId: '',
        timestamp: new Date().toISOString(),
        value: 25.5,
        unit: '°C',
      };

      const result = validateAndCreateTelemetry(input);

      expect(result.valid).toBe(false);
    });

    it('should reject invalid timestamp', () => {
      const input: TelemetryInput = {
        deviceId: 'DEV-20250106-001',
        timestamp: 'not-a-date',
        value: 25.5,
        unit: '°C',
      };

      const result = validateAndCreateTelemetry(input);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('Invalid timestamp');
      }
    });

    it('should reject future timestamp', () => {
      const future = new Date(Date.now() + 10 * 60 * 1000); // 10 minutes in future
      const input: TelemetryInput = {
        deviceId: 'DEV-20250106-001',
        timestamp: future.toISOString(),
        value: 25.5,
        unit: '°C',
      };

      const result = validateAndCreateTelemetry(input);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('future');
      }
    });

    it('should reject invalid value', () => {
      const input = {
        deviceId: 'DEV-20250106-001',
        timestamp: new Date().toISOString(),
        value: NaN,
        unit: '°C',
      };

      const result = validateAndCreateTelemetry(input);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('valid number');
      }
    });

    it('should reject empty unit', () => {
      const input: TelemetryInput = {
        deviceId: 'DEV-20250106-001',
        timestamp: new Date().toISOString(),
        value: 25.5,
        unit: '',
      };

      const result = validateAndCreateTelemetry(input);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('Unit is required');
      }
    });
  });

  describe('validateTelemetryQuery', () => {
    it('should accept valid query', () => {
      const query: TelemetryQuery = {
        deviceId: 'DEV-20250106-001',
        startTime: new Date(Date.now() - 24 * 60 * 60 * 1000), // 1 day ago
        endTime: new Date(),
      };

      const result = validateTelemetryQuery(query);
      expect(result.valid).toBe(true);
    });

    it('should reject if end time before start time', () => {
      const query: TelemetryQuery = {
        deviceId: 'DEV-20250106-001',
        startTime: new Date(),
        endTime: new Date(Date.now() - 24 * 60 * 60 * 1000),
      };

      const result = validateTelemetryQuery(query);
      expect(result.valid).toBe(false);
      expect(result.error).toContain('End time must be after start time');
    });

    it('should reject query range exceeding 30 days', () => {
      const query: TelemetryQuery = {
        deviceId: 'DEV-20250106-001',
        startTime: new Date(Date.now() - 40 * 24 * 60 * 60 * 1000), // 40 days ago
        endTime: new Date(),
      };

      const result = validateTelemetryQuery(query);
      expect(result.valid).toBe(false);
      expect(result.error).toContain('cannot exceed 30 days');
    });

    it('should accept query exactly 30 days', () => {
      const query: TelemetryQuery = {
        deviceId: 'DEV-20250106-001',
        startTime: new Date(Date.now() - 30 * 24 * 60 * 60 * 1000), // 30 days ago
        endTime: new Date(),
      };

      const result = validateTelemetryQuery(query);
      expect(result.valid).toBe(true);
    });
  });
});
