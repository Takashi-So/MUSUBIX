/**
 * ReservationService Tests
 * 
 * @requirement REQ-RESERVE-001, REQ-RESERVE-002, REQ-RESERVE-003, REQ-RESERVE-004
 * @design DES-PETCLINIC-001 Section 3.2
 */

import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest';
import { ReservationService } from '../src/services/ReservationService.js';
import { ReservationRepository } from '../src/repositories/ReservationRepository.js';
import type { CreateReservationInput } from '../src/types/Reservation.js';

describe('ReservationService', () => {
  let reservationService: ReservationService;
  let reservationRepo: ReservationRepository;

  beforeEach(() => {
    reservationRepo = new ReservationRepository();
    reservationService = new ReservationService(reservationRepo);
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  const createFutureDate = (hoursFromNow: number): Date => {
    return new Date(Date.now() + hoursFromNow * 60 * 60 * 1000);
  };

  describe('book', () => {
    it('should create a reservation successfully (REQ-RESERVE-001)', () => {
      const input: CreateReservationInput = {
        petId: 'PET-001',
        vetId: 'VET-001',
        ownerId: 'USR-001',
        startTime: createFutureDate(48),
        endTime: createFutureDate(49),
        type: 'checkup',
      };

      const result = reservationService.book(input);

      expect(result.success).toBe(true);
      expect(result.data).toBeDefined();
      expect(result.data!.status).toBe('confirmed');
      expect(result.data!.id).toMatch(/^RES-/);
    });

    it('should prevent duplicate booking for same pet (REQ-RESERVE-004)', () => {
      const startTime = createFutureDate(48);
      const endTime = createFutureDate(49);

      // 最初の予約
      reservationService.book({
        petId: 'PET-001',
        vetId: 'VET-001',
        ownerId: 'USR-001',
        startTime,
        endTime,
        type: 'checkup',
      });

      // 同じペットで重複予約
      const result = reservationService.book({
        petId: 'PET-001',
        vetId: 'VET-002', // 別の獣医師でも
        ownerId: 'USR-001',
        startTime,
        endTime,
        type: 'vaccination',
      });

      expect(result.success).toBe(false);
      expect(result.error?.code).toBe('ERR-DUP-001');
    });

    it('should prevent booking when vet slot is occupied', () => {
      const startTime = createFutureDate(48);
      const endTime = createFutureDate(49);

      // 最初の予約
      reservationService.book({
        petId: 'PET-001',
        vetId: 'VET-001',
        ownerId: 'USR-001',
        startTime,
        endTime,
        type: 'checkup',
      });

      // 同じ獣医師・同じ時間で別ペットの予約
      const result = reservationService.book({
        petId: 'PET-002',
        vetId: 'VET-001',
        ownerId: 'USR-002',
        startTime,
        endTime,
        type: 'checkup',
      });

      expect(result.success).toBe(false);
      expect(result.error?.code).toBe('ERR-SLOT-001');
    });
  });

  describe('reschedule', () => {
    it('should reschedule when more than 24 hours before (REQ-RESERVE-002)', () => {
      const originalStart = createFutureDate(48);
      const originalEnd = createFutureDate(49);

      const bookResult = reservationService.book({
        petId: 'PET-001',
        vetId: 'VET-001',
        ownerId: 'USR-001',
        startTime: originalStart,
        endTime: originalEnd,
        type: 'checkup',
      });

      const newStart = createFutureDate(72);
      const newEnd = createFutureDate(73);

      const result = reservationService.reschedule({
        reservationId: bookResult.data!.id,
        newStartTime: newStart,
        newEndTime: newEnd,
      });

      expect(result.success).toBe(true);
      expect(result.data!.status).toBe('rescheduled');
      expect(result.data!.startTime.getTime()).toBe(newStart.getTime());
    });

    it('should fail when less than 24 hours before', () => {
      // 23時間後の予約を作成
      vi.useFakeTimers();
      const now = new Date('2026-01-04T10:00:00Z');
      vi.setSystemTime(now);

      const originalStart = new Date('2026-01-05T09:00:00Z'); // 23時間後
      const originalEnd = new Date('2026-01-05T10:00:00Z');

      // 予約を直接リポジトリに追加（bookだとconfirmedになるため）
      const reservation = reservationRepo.save({
        petId: 'PET-001',
        vetId: 'VET-001',
        ownerId: 'USR-001',
        startTime: originalStart,
        endTime: originalEnd,
        type: 'checkup',
      });
      reservationRepo.updateStatus(reservation.id, 'confirmed');

      const result = reservationService.reschedule({
        reservationId: reservation.id,
        newStartTime: createFutureDate(96),
        newEndTime: createFutureDate(97),
      });

      expect(result.success).toBe(false);
      expect(result.error?.code).toBe('ERR-TIME-001');
    });
  });

  describe('cancel', () => {
    it('should cancel without fee when more than 24 hours before', () => {
      const startTime = createFutureDate(48);
      const endTime = createFutureDate(49);

      const bookResult = reservationService.book({
        petId: 'PET-001',
        vetId: 'VET-001',
        ownerId: 'USR-001',
        startTime,
        endTime,
        type: 'checkup',
      });

      const result = reservationService.cancel(bookResult.data!.id);

      expect(result.success).toBe(true);
      expect(result.data!.status).toBe('cancelled');
      expect(result.requiresFee).toBe(false);
    });

    it('should cancel with fee when less than 24 hours before (REQ-RESERVE-003)', () => {
      vi.useFakeTimers();
      const now = new Date('2026-01-04T10:00:00Z');
      vi.setSystemTime(now);

      const startTime = new Date('2026-01-05T08:00:00Z'); // 22時間後
      const endTime = new Date('2026-01-05T09:00:00Z');

      const reservation = reservationRepo.save({
        petId: 'PET-001',
        vetId: 'VET-001',
        ownerId: 'USR-001',
        startTime,
        endTime,
        type: 'checkup',
      });
      reservationRepo.updateStatus(reservation.id, 'confirmed');

      const result = reservationService.cancel(reservation.id);

      expect(result.success).toBe(true);
      expect(result.data!.status).toBe('cancelled_with_fee');
      expect(result.requiresFee).toBe(true);
    });
  });

  describe('complete', () => {
    it('should complete a confirmed reservation', () => {
      const bookResult = reservationService.book({
        petId: 'PET-001',
        vetId: 'VET-001',
        ownerId: 'USR-001',
        startTime: createFutureDate(48),
        endTime: createFutureDate(49),
        type: 'checkup',
      });

      const result = reservationService.complete(bookResult.data!.id);

      expect(result.success).toBe(true);
      expect(result.data!.status).toBe('completed');
    });
  });
});
