/**
 * Attendance Repository
 * REQ-EMPLOYEE-001-F020, F022 対応
 */

import {
  Attendance,
  AttendanceId,
  EmployeeId,
  AttendanceRepository,
} from '../domain/types.js';
import { isSameDate } from '../domain/attendance.js';

/**
 * InMemory Attendance Repository
 * BP-DESIGN-002: Repository Async Pattern
 */
export class InMemoryAttendanceRepository implements AttendanceRepository {
  private attendances: Map<AttendanceId, Attendance> = new Map();

  async save(attendance: Attendance): Promise<void> {
    this.attendances.set(attendance.id, attendance);
  }

  async findById(id: AttendanceId): Promise<Attendance | null> {
    return this.attendances.get(id) ?? null;
  }

  async findByEmployeeAndDate(employeeId: EmployeeId, date: Date): Promise<Attendance | null> {
    for (const attendance of this.attendances.values()) {
      if (
        attendance.employeeId === employeeId &&
        isSameDate(attendance.date, date)
      ) {
        return attendance;
      }
    }
    return null;
  }

  async findByEmployeeAndMonth(
    employeeId: EmployeeId,
    year: number,
    month: number
  ): Promise<Attendance[]> {
    const result: Attendance[] = [];
    
    for (const attendance of this.attendances.values()) {
      if (
        attendance.employeeId === employeeId &&
        attendance.date.getFullYear() === year &&
        attendance.date.getMonth() + 1 === month // month is 1-indexed in parameters
      ) {
        result.push(attendance);
      }
    }
    
    return result.sort((a, b) => a.date.getTime() - b.date.getTime());
  }

  async findAll(): Promise<Attendance[]> {
    return Array.from(this.attendances.values());
  }

  async delete(id: AttendanceId): Promise<void> {
    this.attendances.delete(id);
  }

  /** テスト用: 全データクリア */
  clear(): void {
    this.attendances.clear();
  }
}
