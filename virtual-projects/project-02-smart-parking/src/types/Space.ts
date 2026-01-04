/**
 * ParkingSpace Types
 * @requirement REQ-SPACE-001, REQ-SPACE-002, REQ-SPACE-003
 * @design DES-PARKING-001 Section 4
 */

export type SpaceType = 'standard' | 'compact' | 'handicap' | 'motorcycle';
export type SpaceState = 'available' | 'occupied' | 'reserved' | 'maintenance';

export interface ParkingSpace {
  id: string;
  spaceNumber: string;
  type: SpaceType;
  floor?: number;
  section?: string;
  state: SpaceState;
  createdAt: Date;
  updatedAt: Date;
}

export interface SpaceStats {
  total: number;
  available: number;
  occupied: number;
  reserved: number;
  maintenance: number;
}

export const SPACE_ERRORS = {
  NOT_FOUND: 'space_not_found',
  ALREADY_EXISTS: 'space_already_exists',
  OCCUPIED: 'space_occupied',
  NOT_OCCUPIED: 'space_not_occupied',
} as const;
