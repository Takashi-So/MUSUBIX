// REQ-DEV-003: Device grouping
// Traces to: DES-DEV-003

import type { DeviceId } from './device.js';

/**
 * Group ID value object
 */
export interface GroupId {
  readonly value: string;
}

/**
 * Device group input
 * @requirement REQ-DEV-003
 */
export interface DeviceGroupInput {
  name: string;
  description?: string;
}

/**
 * Device group entity
 * @requirement REQ-DEV-003
 */
export interface DeviceGroup {
  readonly id: GroupId;
  name: string;
  description?: string;
  deviceIds: DeviceId[];
  createdAt: Date;
  updatedAt: Date;
  version: number;
}

let groupCounter = 0;

/**
 * Reset group counter (for testing)
 */
export function resetGroupCounter(): void {
  groupCounter = 0;
}

/**
 * Generate group ID in format GRP-YYYYMMDD-NNN
 */
export function generateGroupId(): GroupId {
  groupCounter++;
  const date = new Date();
  const dateStr = date.toISOString().slice(0, 10).replace(/-/g, '');
  const seq = String(groupCounter).padStart(3, '0');
  return { value: `GRP-${dateStr}-${seq}` };
}

/**
 * Create a new device group
 * @requirement REQ-DEV-003
 */
export function createDeviceGroup(input: DeviceGroupInput): DeviceGroup {
  if (!input.name || input.name.length === 0) {
    throw new Error('Group name is required');
  }
  if (input.name.length > 100) {
    throw new Error('Group name must be 100 characters or less');
  }

  const now = new Date();
  return {
    id: generateGroupId(),
    name: input.name,
    description: input.description,
    deviceIds: [],
    createdAt: now,
    updatedAt: now,
    version: 1,
  };
}

/**
 * Add device to group
 * @requirement REQ-DEV-003
 */
export function addDeviceToGroup(group: DeviceGroup, deviceId: DeviceId): DeviceGroup {
  if (group.deviceIds.some((id) => id.value === deviceId.value)) {
    return group; // Already in group
  }

  return {
    ...group,
    deviceIds: [...group.deviceIds, deviceId],
    updatedAt: new Date(),
    version: group.version + 1,
  };
}

/**
 * Remove device from group
 * @requirement REQ-DEV-003
 */
export function removeDeviceFromGroup(group: DeviceGroup, deviceId: DeviceId): DeviceGroup {
  const filteredIds = group.deviceIds.filter((id) => id.value !== deviceId.value);
  
  if (filteredIds.length === group.deviceIds.length) {
    return group; // Device not in group
  }

  return {
    ...group,
    deviceIds: filteredIds,
    updatedAt: new Date(),
    version: group.version + 1,
  };
}
