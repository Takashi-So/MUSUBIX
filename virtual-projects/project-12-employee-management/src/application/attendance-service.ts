/**
 * Attendance Service
 * REQ-EMPLOYEE-001-F020, F021, F022, F042 対応
 * BP-DESIGN-003: Service Layer with DI
 */

import {
  Attendance,
  EmployeeId,
  MonthlySummary,
  AttendanceRepository,
  EmployeeRepository,
} from '../domain/types.js';
import { createAttendance, recordClockOut, calculateMonthlySummary } from '../domain/attendance.js';
import {
  EmployeeNotFoundError,
  AlreadyClockedInError,
  NotClockedInError,
  AlreadyClockedOutError,
} from '../domain/errors.js';

export class AttendanceService {
  constructor(
    private readonly attendanceRepository: AttendanceRepository,
    private readonly employeeRepository: EmployeeRepository
  ) {}

  /**
   * クロックイン (REQ-EMPLOYEE-001-F020)
   * @param employeeId 従業員ID
   * @throws EmployeeNotFoundError 従業員が存在しない場合
   * @throws AlreadyClockedInError 既にクロックイン済みの場合
   */
  async clockIn(employeeId: EmployeeId): Promise<Attendance> {
    // 従業員存在チェック
    const employee = await this.employeeRepository.findById(employeeId);
    if (!employee) {
      throw new EmployeeNotFoundError(employeeId);
    }

    // 本日の勤怠記録チェック
    const today = new Date();
    const existing = await this.attendanceRepository.findByEmployeeAndDate(employeeId, today);
    if (existing?.clockIn) {
      throw new AlreadyClockedInError(employeeId);
    }

    const attendance = createAttendance({
      employeeId,
      clockIn: new Date(),
    });
    await this.attendanceRepository.save(attendance);
    return attendance;
  }

  /**
   * クロックアウト (REQ-EMPLOYEE-001-F021, F042)
   * @param employeeId 従業員ID
   * @throws EmployeeNotFoundError 従業員が存在しない場合
   * @throws NotClockedInError クロックインしていない場合
   * @throws AlreadyClockedOutError 既にクロックアウト済みの場合
   */
  async clockOut(employeeId: EmployeeId): Promise<Attendance> {
    // 従業員存在チェック
    const employee = await this.employeeRepository.findById(employeeId);
    if (!employee) {
      throw new EmployeeNotFoundError(employeeId);
    }

    // 本日の勤怠記録チェック
    const today = new Date();
    const attendance = await this.attendanceRepository.findByEmployeeAndDate(employeeId, today);
    
    // REQ-EMPLOYEE-001-F042: クロックインなしのクロックアウト防止
    if (!attendance?.clockIn) {
      throw new NotClockedInError(employeeId);
    }
    if (attendance.clockOut) {
      throw new AlreadyClockedOutError(employeeId);
    }

    const updatedAttendance = recordClockOut(attendance, new Date());
    await this.attendanceRepository.save(updatedAttendance);
    return updatedAttendance;
  }

  /**
   * 月次勤怠サマリー取得 (REQ-EMPLOYEE-001-F022)
   * @param employeeId 従業員ID
   * @param year 年
   * @param month 月（1-12）
   * @throws EmployeeNotFoundError 従業員が存在しない場合
   */
  async getMonthlySummary(
    employeeId: EmployeeId,
    year: number,
    month: number
  ): Promise<MonthlySummary> {
    // 従業員存在チェック
    const employee = await this.employeeRepository.findById(employeeId);
    if (!employee) {
      throw new EmployeeNotFoundError(employeeId);
    }

    const records = await this.attendanceRepository.findByEmployeeAndMonth(
      employeeId,
      year,
      month
    );
    
    return calculateMonthlySummary(employeeId, year, month, records);
  }

  /**
   * 本日の勤怠状況取得
   * @param employeeId 従業員ID
   */
  async getTodayAttendance(employeeId: EmployeeId): Promise<Attendance | null> {
    const today = new Date();
    return this.attendanceRepository.findByEmployeeAndDate(employeeId, today);
  }

  /**
   * 月間勤怠記録取得
   * @param employeeId 従業員ID
   * @param year 年
   * @param month 月（1-12）
   */
  async getMonthlyRecords(
    employeeId: EmployeeId,
    year: number,
    month: number
  ): Promise<Attendance[]> {
    return this.attendanceRepository.findByEmployeeAndMonth(employeeId, year, month);
  }
}
