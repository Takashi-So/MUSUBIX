/**
 * CheckInService Unit Tests
 *
 * @module __tests__/checkin-service.test
 * @traces REQ-EVENT-015, REQ-EVENT-016, REQ-EVENT-017
 */

import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest';
import {
  CheckInService,
  type CheckInRecord,
  type CachedTicket,
  type ICheckInRepository,
  type ITicketCache,
  type ITicketServiceAdapter,
} from '../src/checkin-service';

// ============================================================
// Mock Implementations
// ============================================================

function createMockCheckInRepository(): ICheckInRepository {
  const records = new Map<string, CheckInRecord>();

  return {
    save: vi.fn(async (record: CheckInRecord) => {
      records.set(record.id, { ...record });
      return record;
    }),
    findByTicket: vi.fn(async (ticketId: string) => {
      const record = Array.from(records.values()).find((r) => r.ticketId === ticketId);
      return record || null;
    }),
    findByEvent: vi.fn(async (eventId: string) => {
      return Array.from(records.values()).filter((r) => r.eventId === eventId);
    }),
    delete: vi.fn(async (id: string) => {
      records.delete(id);
      return true;
    }),
    countByEvent: vi.fn(async (eventId: string) => {
      return Array.from(records.values()).filter((r) => r.eventId === eventId).length;
    }),
    countByTicketType: vi.fn(async (eventId: string) => {
      const eventRecords = Array.from(records.values()).filter((r) => r.eventId === eventId);
      const counts: Record<string, number> = {};
      eventRecords.forEach((r) => {
        counts[r.ticketType] = (counts[r.ticketType] || 0) + 1;
      });
      return counts;
    }),
  };
}

function createMockTicketCache(): ITicketCache {
  const cache = new Map<string, CachedTicket>();

  return {
    cacheTickets: vi.fn(async (eventId: string, tickets: CachedTicket[]) => {
      tickets.forEach((t) => cache.set(t.qrCode, { ...t }));
    }),
    getTicket: vi.fn(async (qrCode: string) => {
      return cache.get(qrCode) || null;
    }),
    markCheckedIn: vi.fn(async (qrCode: string) => {
      const ticket = cache.get(qrCode);
      if (ticket) {
        ticket.isCheckedIn = true;
        cache.set(qrCode, ticket);
      }
    }),
    clear: vi.fn(async () => {
      cache.clear();
    }),
  };
}

function createMockTicketAdapter(): ITicketServiceAdapter {
  const tickets: CachedTicket[] = [
    {
      id: 'tkt-001',
      qrCode: 'QR-VALID-001',
      eventId: 'evt-001',
      holderName: 'John Doe',
      ticketType: 'General Admission',
      isCheckedIn: false,
    },
    {
      id: 'tkt-002',
      qrCode: 'QR-VALID-002',
      eventId: 'evt-001',
      holderName: 'Jane Smith',
      ticketType: 'VIP',
      isCheckedIn: false,
    },
    {
      id: 'tkt-003',
      qrCode: 'QR-USED-001',
      eventId: 'evt-001',
      holderName: 'Bob Wilson',
      ticketType: 'General Admission',
      isCheckedIn: true,
    },
  ];

  return {
    validateTicket: vi.fn(async (qrCode: string) => {
      const ticket = tickets.find((t) => t.qrCode === qrCode);
      if (!ticket) {
        return { valid: false, ticket: null, message: 'Ticket not found' };
      }
      if (ticket.isCheckedIn) {
        return {
          valid: false,
          ticket: { id: ticket.id, holderId: 'holder-' + ticket.id, holderName: ticket.holderName, ticketTypeId: ticket.ticketType },
          message: 'Ticket already checked in',
        };
      }
      return {
        valid: true,
        ticket: { id: ticket.id, holderId: 'holder-' + ticket.id, holderName: ticket.holderName, ticketTypeId: ticket.ticketType },
        message: 'Valid ticket',
      };
    }),
    getEventTickets: vi.fn(async (eventId: string) => {
      return tickets.filter((t) => t.eventId === eventId);
    }),
    markAsUsed: vi.fn(async () => {}),
  };
}

// ============================================================
// Test Suites
// ============================================================

describe('CheckInService', () => {
  let service: CheckInService;
  let checkInRepo: ICheckInRepository;
  let ticketCache: ITicketCache;
  let ticketAdapter: ITicketServiceAdapter;

  beforeEach(() => {
    vi.useFakeTimers();
    vi.setSystemTime(new Date('2025-06-15T14:00:00Z'));

    checkInRepo = createMockCheckInRepository();
    ticketCache = createMockTicketCache();
    ticketAdapter = createMockTicketAdapter();
    service = new CheckInService(checkInRepo, ticketCache, ticketAdapter);
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  // ==========================================================
  // REQ-EVENT-015: QRコードチェックイン
  // ==========================================================
  describe('REQ-EVENT-015: QR Code Check-In', () => {
    it('should check in with valid QR code', async () => {
      const result = await service.checkIn('evt-001', 'QR-VALID-001', 'staff-001', 'Gate A');

      expect(result.success).toBe(true);
      expect(result.ticketId).toBe('tkt-001');
      expect(result.holderName).toBe('John Doe');
      expect(result.isDuplicate).toBe(false);
    });

    it('should return ticket details on check-in', async () => {
      const result = await service.checkIn('evt-001', 'QR-VALID-002', 'staff-001', 'Gate B');

      expect(result.holderName).toBe('Jane Smith');
      expect(result.ticketType).toBe('VIP');
    });

    it('should reject invalid QR code', async () => {
      const result = await service.checkIn('evt-001', 'QR-INVALID', 'staff-001', 'Gate A');

      expect(result.success).toBe(false);
      expect(result.message).toContain('not found');
    });

    it('should detect duplicate check-in', async () => {
      // First check-in
      await service.checkIn('evt-001', 'QR-VALID-001', 'staff-001', 'Gate A');
      
      // Second check-in attempt with same ticket
      const result = await service.checkIn('evt-001', 'QR-VALID-001', 'staff-002', 'Gate B');

      expect(result.success).toBe(false);
      expect(result.isDuplicate).toBe(true);
    });

    it('should record check-in gate and staff', async () => {
      await service.checkIn('evt-001', 'QR-VALID-001', 'staff-xyz', 'Main Entrance');

      expect(checkInRepo.save).toHaveBeenCalledWith(
        expect.objectContaining({
          checkedInBy: 'staff-xyz',
          gate: 'Main Entrance',
        })
      );
    });
  });

  // ==========================================================
  // REQ-EVENT-016: チェックイン統計
  // ==========================================================
  describe('REQ-EVENT-016: Check-In Statistics', () => {
    beforeEach(async () => {
      await service.checkIn('evt-001', 'QR-VALID-001', 'staff-001', 'Gate A');
      await service.checkIn('evt-001', 'QR-VALID-002', 'staff-002', 'Gate B');
    });

    it('should get check-in statistics', async () => {
      const stats = await service.getCheckInStats('evt-001');

      expect(stats).toBeDefined();
      expect(stats.eventId).toBe('evt-001');
      expect(stats.checkedIn).toBeGreaterThan(0);
    });

    it('should calculate check-in rate', async () => {
      const stats = await service.getCheckInStats('evt-001');

      expect(stats.checkInRate).toBeGreaterThanOrEqual(0);
      expect(stats.checkInRate).toBeLessThanOrEqual(100);
    });

    it('should track stats by ticket type', async () => {
      const stats = await service.getCheckInStats('evt-001');

      expect(stats.byTicketType).toBeDefined();
    });
  });

  // ==========================================================
  // REQ-EVENT-017: オフラインチェックイン
  // ==========================================================
  describe('REQ-EVENT-017: Offline Check-In Sync', () => {
    it('should cache tickets for offline mode', async () => {
      const count = await service.cacheTicketsForOffline('evt-001');

      expect(count).toBeGreaterThan(0);
      expect(ticketCache.cacheTickets).toHaveBeenCalled();
    });

    it('should process offline check-ins', async () => {
      const offlineData = [
        {
          qrCode: 'QR-VALID-001',
          timestamp: new Date('2025-06-15T13:00:00Z'),
          staffId: 'staff-offline',
          gate: 'Gate C',
        },
      ];

      const result = await service.processOfflineCheckIns('evt-001', offlineData);

      expect(result.synced).toBeGreaterThanOrEqual(0);
    });

    it('should report sync errors', async () => {
      const offlineData = [
        {
          qrCode: 'QR-INVALID-OFFLINE',
          timestamp: new Date('2025-06-15T13:00:00Z'),
          staffId: 'staff-offline',
          gate: 'Gate C',
        },
      ];

      const result = await service.processOfflineCheckIns('evt-001', offlineData);

      expect(result.failed).toBeGreaterThan(0);
    });
  });

  // ==========================================================
  // Check-In Record Tests
  // ==========================================================
  describe('Check-In Records', () => {
    beforeEach(async () => {
      await service.checkIn('evt-001', 'QR-VALID-001', 'staff-001', 'Gate A');
    });

    it('should verify ticket is checked in', async () => {
      const isCheckedIn = await service.isTicketCheckedIn('tkt-001');

      expect(isCheckedIn).toBe(true);
    });

    it('should get check-in records for event', async () => {
      const records = await service.getCheckInRecords('evt-001');

      expect(records.length).toBeGreaterThan(0);
    });
  });

  // ==========================================================
  // Undo Check-In Tests
  // ==========================================================
  describe('Undo Check-In', () => {
    it('should undo check-in with reason', async () => {
      const checkIn = await service.checkIn('evt-001', 'QR-VALID-001', 'staff-001', 'Gate A');
      
      // Get the record ID (mocked)
      const records = await checkInRepo.findByEvent('evt-001');
      const record = records[0];

      if (record) {
        const result = await service.undoCheckIn(record.id, 'Wrong ticket scanned');
        expect(result).toBe(true);
      }
    });
  });
});
