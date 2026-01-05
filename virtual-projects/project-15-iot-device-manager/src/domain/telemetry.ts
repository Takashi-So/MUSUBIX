// REQ-DATA-001, REQ-DATA-002: Telemetry entity
// Traces to: DES-DATA-001, DES-DATA-002

import type { DeviceId } from './device.js';

/**
 * Telemetry ID value object
 */
export interface TelemetryId {
  readonly value: string;
}

/**
 * Telemetry input
 * @requirement REQ-DATA-001
 */
export interface TelemetryInput {
  deviceId: string;
  timestamp: string;
  value: number;
  unit: string;
  metadata?: Record<string, unknown>;
}

/**
 * Telemetry entity
 * @requirement REQ-DATA-001, REQ-DATA-002
 */
export interface Telemetry {
  readonly id: TelemetryId;
  deviceId: DeviceId;
  timestamp: Date;
  value: number;
  unit: string;
  metadata?: Record<string, unknown>;
  receivedAt: Date;
}

let telemetryCounter = 0;

/**
 * Reset telemetry counter (for testing)
 */
export function resetTelemetryCounter(): void {
  telemetryCounter = 0;
}

/**
 * Generate telemetry ID
 */
export function generateTelemetryId(): TelemetryId {
  telemetryCounter++;
  const ts = Date.now();
  const seq = String(telemetryCounter).padStart(6, '0');
  return { value: `TEL-${ts}-${seq}` };
}

/**
 * Validation result type
 */
export type ValidationResult =
  | { valid: true; telemetry: Telemetry }
  | { valid: false; error: string };

/**
 * Validate and create telemetry
 * @requirement REQ-DATA-001
 */
export function validateAndCreateTelemetry(input: TelemetryInput): ValidationResult {
  // Validate device ID format
  if (!input.deviceId || !input.deviceId.match(/^DEV-\d{8}-\d{3}$/)) {
    return { valid: false, error: 'Invalid device ID format' };
  }

  // Validate timestamp (ISO8601)
  const timestamp = new Date(input.timestamp);
  if (isNaN(timestamp.getTime())) {
    return { valid: false, error: 'Invalid timestamp format. Expected ISO8601' };
  }

  // Validate timestamp is not in future
  if (timestamp.getTime() > Date.now() + 60000) {
    // 1 minute tolerance
    return { valid: false, error: 'Timestamp cannot be in the future' };
  }

  // Validate value is a number
  if (typeof input.value !== 'number' || isNaN(input.value)) {
    return { valid: false, error: 'Value must be a valid number' };
  }

  // Validate unit is provided
  if (!input.unit || input.unit.length === 0) {
    return { valid: false, error: 'Unit is required' };
  }

  const telemetry: Telemetry = {
    id: generateTelemetryId(),
    deviceId: { value: input.deviceId },
    timestamp,
    value: input.value,
    unit: input.unit,
    metadata: input.metadata,
    receivedAt: new Date(),
  };

  return { valid: true, telemetry };
}

/**
 * Query parameters for telemetry
 * @requirement REQ-DATA-003
 */
export interface TelemetryQuery {
  deviceId: string;
  startTime: Date;
  endTime: Date;
  aggregation?: 'raw' | 'hourly' | 'daily';
  limit?: number;
  offset?: number;
}

/**
 * Validate query parameters
 * @requirement REQ-DATA-003
 */
export function validateTelemetryQuery(query: TelemetryQuery): { valid: boolean; error?: string } {
  // Check time range
  const rangeMs = query.endTime.getTime() - query.startTime.getTime();
  const maxRangeMs = 30 * 24 * 60 * 60 * 1000; // 30 days

  if (rangeMs <= 0) {
    return { valid: false, error: 'End time must be after start time' };
  }

  if (rangeMs > maxRangeMs) {
    return { valid: false, error: 'Query range cannot exceed 30 days' };
  }

  return { valid: true };
}
