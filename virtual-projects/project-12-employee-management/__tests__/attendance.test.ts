/**
 * Attendance Entity and Service Tests
 * REQ-EMPLOYEE-001-F020, F021, F022, F042
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createAttendance,
  recordClockOut,
  calculateWorkHours,
  calculateMonthlySummary,
  resetAttendanceCounter,
} from '../src/domain/attendance.js';
import { createEmployee, resetEmployeeCounter, createPersonName } from '../src/domain/employee.js';
import { createDepartment, resetDepartmentCounter } from '../src/domain/department.js';
import { createMoney } from '../src/domain/money.js';
import {
  AlreadyClockedInError,
  NotClockedInError,
  AlreadyClockedOutError,
  EmployeeNotFoundError,
} from '../src/domain/errors.js';
import { InMemoryAttendanceRepository } from '../src/infrastructure/attendance-repository.js';
import { InMemoryEmployeeRepository } from '../src/infrastructure/employee-repository.js';
import { InMemoryDepartmentRepository } from '../src/infrastructure/department-repository.js';
import { AttendanceService } from '../src/application/attendance-service.js';

describe('Attendance Entity', () => {
  beforeEach(() => {
    resetAttendanceCounter();
  });

  describe('createAttendance (REQ-EMPLOYEE-001-F020)', () => {
    it('should create attendance with correct ID format', () => {
      const clockIn = new Date('2026-01-15T09:00:00');
      const attendance = createAttendance({
        employeeId: 'EMP-20260115-001',
        clockIn,
      });

      expect(attendance.id).toMatch(/^ATT-\d{8}-001$/);
      expect(attendance.employeeId).toBe('EMP-20260115-001');
      expect(attendance.clockIn).toEqual(clockIn);
      expect(attendance.clockOut).toBeUndefined();
    });
  });

  describe('calculateWorkHours (REQ-EMPLOYEE-001-F021)', () => {
    it('should calculate regular hours (<=8 hours)', () => {
      const clockIn = new Date('2026-01-15T09:00:00');
      const clockOut = new Date('2026-01-15T17:00:00'); // 8 hours total

      const result = calculateWorkHours(clockIn, clockOut);

      // 8 hours worked, 1 hour break = 7 regular hours
      expect(result.regularHours).toBe(7);
      expect(result.overtimeHours).toBe(0);
      expect(result.breakMinutes).toBe(60);
    });

    it('should calculate overtime hours (>8 hours)', () => {
      const clockIn = new Date('2026-01-15T09:00:00');
      const clockOut = new Date('2026-01-15T20:00:00'); // 11 hours total

      const result = calculateWorkHours(clockIn, clockOut);

      // 11 hours - 1 hour break = 10 actual hours
      // 8 regular + 2 overtime
      expect(result.regularHours).toBe(8);
      expect(result.overtimeHours).toBe(2);
      expect(result.breakMinutes).toBe(60);
    });

    it('should not apply break for short work (<6 hours)', () => {
      const clockIn = new Date('2026-01-15T09:00:00');
      const clockOut = new Date('2026-01-15T14:00:00'); // 5 hours

      const result = calculateWorkHours(clockIn, clockOut);

      expect(result.regularHours).toBe(5);
      expect(result.overtimeHours).toBe(0);
      expect(result.breakMinutes).toBe(0);
    });
  });

  describe('recordClockOut', () => {
    it('should record clock out and calculate hours', () => {
      const clockIn = new Date('2026-01-15T09:00:00');
      const clockOut = new Date('2026-01-15T18:00:00');

      const attendance = createAttendance({
        employeeId: 'EMP-001',
        clockIn,
      });

      const updated = recordClockOut(attendance, clockOut);

      expect(updated.clockOut).toEqual(clockOut);
      expect(updated.regularHours).toBe(8);
      expect(updated.overtimeHours).toBe(0);
    });
  });

  describe('calculateMonthlySummary (REQ-EMPLOYEE-001-F022)', () => {
    it('should calculate monthly summary correctly', () => {
      const records = [
        {
          id: 'ATT-001',
          employeeId: 'EMP-001',
          date: new Date('2026-01-01'),
          clockIn: new Date('2026-01-01T09:00:00'),
          clockOut: new Date('2026-01-01T18:00:00'),
          breakMinutes: 60,
          regularHours: 8,
          overtimeHours: 0,
          createdAt: new Date(),
          updatedAt: new Date(),
        },
        {
          id: 'ATT-002',
          employeeId: 'EMP-001',
          date: new Date('2026-01-02'),
          clockIn: new Date('2026-01-02T09:00:00'),
          clockOut: new Date('2026-01-02T20:00:00'),
          breakMinutes: 60,
          regularHours: 8,
          overtimeHours: 2,
          createdAt: new Date(),
          updatedAt: new Date(),
        },
      ];

      const summary = calculateMonthlySummary('EMP-001', 2026, 1, records);

      expect(summary.totalWorkedDays).toBe(2);
      expect(summary.totalRegularHours).toBe(16);
      expect(summary.totalOvertimeHours).toBe(2);
    });
  });
});

describe('AttendanceService', () => {
  let attendanceRepository: InMemoryAttendanceRepository;
  let employeeRepository: InMemoryEmployeeRepository;
  let departmentRepository: InMemoryDepartmentRepository;
  let attendanceService: AttendanceService;
  let testEmployeeId: string;

  beforeEach(async () => {
    resetAttendanceCounter();
    resetEmployeeCounter();
    resetDepartmentCounter();

    attendanceRepository = new InMemoryAttendanceRepository();
    employeeRepository = new InMemoryEmployeeRepository();
    departmentRepository = new InMemoryDepartmentRepository();
    attendanceService = new AttendanceService(attendanceRepository, employeeRepository);

    // Setup test employee
    const dept = createDepartment({ name: 'Engineering', code: 'ENG' });
    await departmentRepository.save(dept);

    const name = createPersonName('太郎', '山田');
    const employee = createEmployee({
      name,
      email: 'test@example.com',
      hireDate: new Date(),
      departmentId: dept.id,
      position: 'Engineer',
      employmentType: 'full_time',
      salary: createMoney(500000),
    });
    await employeeRepository.save(employee);
    testEmployeeId = employee.id;
  });

  describe('clockIn (REQ-EMPLOYEE-001-F020)', () => {
    it('should clock in successfully', async () => {
      const attendance = await attendanceService.clockIn(testEmployeeId);

      expect(attendance.employeeId).toBe(testEmployeeId);
      expect(attendance.clockIn).toBeDefined();
      expect(attendance.clockOut).toBeUndefined();
    });

    it('should reject clock in for non-existent employee', async () => {
      await expect(attendanceService.clockIn('NON-EXISTENT'))
        .rejects.toThrow(EmployeeNotFoundError);
    });

    it('should reject duplicate clock in', async () => {
      await attendanceService.clockIn(testEmployeeId);

      await expect(attendanceService.clockIn(testEmployeeId))
        .rejects.toThrow(AlreadyClockedInError);
    });
  });

  describe('clockOut (REQ-EMPLOYEE-001-F021, F042)', () => {
    it('should clock out successfully', async () => {
      await attendanceService.clockIn(testEmployeeId);
      const attendance = await attendanceService.clockOut(testEmployeeId);

      expect(attendance.clockOut).toBeDefined();
      expect(attendance.regularHours).toBeGreaterThanOrEqual(0);
    });

    it('should reject clock out without clock in (REQ-EMPLOYEE-001-F042)', async () => {
      await expect(attendanceService.clockOut(testEmployeeId))
        .rejects.toThrow(NotClockedInError);
    });

    it('should reject duplicate clock out', async () => {
      await attendanceService.clockIn(testEmployeeId);
      await attendanceService.clockOut(testEmployeeId);

      await expect(attendanceService.clockOut(testEmployeeId))
        .rejects.toThrow(AlreadyClockedOutError);
    });
  });
});
