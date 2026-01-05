// REQ-DEV-001, REQ-DEV-002: Device entity and status management
// Traces to: DES-DEV-001, DES-DEV-002

/**
 * Device type enumeration
 * @requirement REQ-DEV-001
 */
export type DeviceType = 'sensor' | 'actuator' | 'gateway';

/**
 * Device status enumeration
 * @requirement REQ-DEV-002
 */
export type DeviceStatus = 'online' | 'offline' | 'maintenance' | 'error';

/**
 * Communication protocol
 * @requirement REQ-DEV-001
 */
export type Protocol = 'mqtt' | 'http' | 'coap';

/**
 * Device ID value object
 */
export interface DeviceId {
  readonly value: string;
}

/**
 * Firmware version value object
 * @requirement REQ-LIFE-001
 */
export interface FirmwareVersion {
  readonly major: number;
  readonly minor: number;
  readonly patch: number;
}

/**
 * Device registration input
 * @requirement REQ-DEV-001
 */
export interface DeviceInput {
  name: string;
  type: DeviceType;
  protocol: Protocol;
  location?: string;
  firmwareVersion?: string;
}

/**
 * Device entity
 * @requirement REQ-DEV-001, REQ-DEV-002
 */
export interface Device {
  readonly id: DeviceId;
  name: string;
  type: DeviceType;
  status: DeviceStatus;
  protocol: Protocol;
  location?: string;
  firmwareVersion: FirmwareVersion;
  registeredAt: Date;
  lastSeenAt?: Date;
  version: number; // Optimistic locking
}

// Counter for generating unique IDs
let deviceCounter = 0;

/**
 * Reset device counter (for testing)
 */
export function resetDeviceCounter(): void {
  deviceCounter = 0;
}

/**
 * Generate device ID in format DEV-YYYYMMDD-NNN
 * @requirement REQ-DEV-001
 */
export function generateDeviceId(): DeviceId {
  deviceCounter++;
  const date = new Date();
  const dateStr = date.toISOString().slice(0, 10).replace(/-/g, '');
  const seq = String(deviceCounter).padStart(3, '0');
  return { value: `DEV-${dateStr}-${seq}` };
}

/**
 * Parse firmware version string to FirmwareVersion
 * @requirement REQ-LIFE-001
 */
export function parseFirmwareVersion(version: string): FirmwareVersion {
  const match = version.match(/^(\d+)\.(\d+)\.(\d+)$/);
  if (!match) {
    throw new Error(`Invalid firmware version format: ${version}. Expected x.y.z`);
  }
  return {
    major: parseInt(match[1], 10),
    minor: parseInt(match[2], 10),
    patch: parseInt(match[3], 10),
  };
}

/**
 * Format FirmwareVersion to string
 */
export function formatFirmwareVersion(version: FirmwareVersion): string {
  return `${version.major}.${version.minor}.${version.patch}`;
}

/**
 * Valid status transitions
 * @requirement REQ-DEV-002
 */
const validStatusTransitions: Record<DeviceStatus, DeviceStatus[]> = {
  offline: ['online', 'maintenance', 'error'],
  online: ['offline', 'maintenance', 'error'],
  maintenance: ['offline', 'online'],
  error: ['offline', 'maintenance'],
};

/**
 * Check if status transition is valid
 * @requirement REQ-DEV-002
 */
export function isValidStatusTransition(from: DeviceStatus, to: DeviceStatus): boolean {
  if (from === to) return true;
  return validStatusTransitions[from].includes(to);
}

/**
 * Create a new device
 * @requirement REQ-DEV-001
 */
export function createDevice(input: DeviceInput): Device {
  // Validation
  if (!input.name || input.name.length === 0) {
    throw new Error('Device name is required');
  }
  if (input.name.length > 100) {
    throw new Error('Device name must be 100 characters or less');
  }

  const validTypes: DeviceType[] = ['sensor', 'actuator', 'gateway'];
  if (!validTypes.includes(input.type)) {
    throw new Error(`Invalid device type: ${input.type}`);
  }

  const validProtocols: Protocol[] = ['mqtt', 'http', 'coap'];
  if (!validProtocols.includes(input.protocol)) {
    throw new Error(`Invalid protocol: ${input.protocol}`);
  }

  const firmwareVersion = input.firmwareVersion
    ? parseFirmwareVersion(input.firmwareVersion)
    : { major: 1, minor: 0, patch: 0 };

  return {
    id: generateDeviceId(),
    name: input.name,
    type: input.type,
    status: 'offline', // Initial status
    protocol: input.protocol,
    location: input.location,
    firmwareVersion,
    registeredAt: new Date(),
    lastSeenAt: undefined,
    version: 1,
  };
}

/**
 * Update device status
 * @requirement REQ-DEV-002
 */
export function updateDeviceStatus(device: Device, newStatus: DeviceStatus): Device {
  if (!isValidStatusTransition(device.status, newStatus)) {
    throw new Error(
      `Invalid status transition from '${device.status}' to '${newStatus}'`
    );
  }

  return {
    ...device,
    status: newStatus,
    lastSeenAt: newStatus === 'online' ? new Date() : device.lastSeenAt,
    version: device.version + 1,
  };
}
