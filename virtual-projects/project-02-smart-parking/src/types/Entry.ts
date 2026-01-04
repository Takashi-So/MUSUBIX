/**
 * Entry Types
 * @requirement REQ-ENTRY-001, REQ-ENTRY-002, REQ-ENTRY-003
 * @design DES-PARKING-001 Section 4
 */

export type VehicleType = 'regular' | 'large' | 'motorcycle';
export type EntryStatus = 'active' | 'completed' | 'cancelled';

export interface EntryRecord {
  id: string;
  licensePlate: string;
  vehicleType: VehicleType;
  entryTime: Date;
  exitTime?: Date;
  spaceId?: string;
  status: EntryStatus;
  createdAt: Date;
}

export interface CreateEntryInput {
  licensePlate: string;
  vehicleType: VehicleType;
  spaceId?: string;
}

export interface EntryError {
  code: string;
  message: string;
}

export const ENTRY_ERRORS = {
  NO_ENTRY_RECORD: { code: 'ERR-NO-ENTRY-001', message: '入庫記録が見つかりません' },
  ALREADY_EXITED: { code: 'ERR-EXITED-001', message: '既に出庫処理済みです' },
  INVALID_PLATE: { code: 'ERR-PLATE-001', message: '無効なナンバープレートです' },
} as const;
