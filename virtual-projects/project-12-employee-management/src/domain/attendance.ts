/**
 * Attendance Entity
 * REQ-EMPLOYEE-001-F020, F021, F022 対応
 */

import {
  Attendance,
  AttendanceId,
  EmployeeId,
  CreateAttendanceInput,
  MonthlySummary,
} from './types.js';

// ID生成カウンター（テスト用リセット対応: BP-TEST-001）
let attendanceCounter = 0;

/**
 * 勤怠IDカウンターリセット（テスト用）
 */
export function resetAttendanceCounter(): void {
  attendanceCounter = 0;
}

/**
 * 勤怠ID生成 (BP-CODE-002: Date-based ID Format)
 * Format: ATT-YYYYMMDD-NNN
 */
function generateAttendanceId(): AttendanceId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  attendanceCounter++;
  const seq = String(attendanceCounter).padStart(3, '0');
  return `ATT-${dateStr}-${seq}`;
}

/** 1日の標準勤務時間 */
const STANDARD_WORK_HOURS = 8;

/** 休憩時間が適用される最小勤務時間 */
const BREAK_THRESHOLD_HOURS = 6;

/** 標準休憩時間（分） */
const STANDARD_BREAK_MINUTES = 60;

/**
 * 勤怠記録作成（クロックイン） (REQ-EMPLOYEE-001-F020)
 * @param input 作成入力 (BP-CODE-001: Entity Input DTO)
 */
export function createAttendance(input: CreateAttendanceInput): Attendance {
  const now = new Date();
  const date = new Date(input.clockIn);
  date.setHours(0, 0, 0, 0); // 日付のみ

  return {
    id: generateAttendanceId(),
    employeeId: input.employeeId,
    date,
    clockIn: input.clockIn,
    clockOut: undefined,
    breakMinutes: 0,
    regularHours: 0,
    overtimeHours: 0,
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * クロックアウト記録 (REQ-EMPLOYEE-001-F021)
 * @param attendance 勤怠記録
 * @param clockOut クロックアウト時刻
 */
export function recordClockOut(attendance: Attendance, clockOut: Date): Attendance {
  if (!attendance.clockIn) {
    throw new Error('Cannot clock out without clocking in');
  }
  
  const { regularHours, overtimeHours, breakMinutes } = calculateWorkHours(
    attendance.clockIn,
    clockOut
  );
  
  return {
    ...attendance,
    clockOut,
    breakMinutes,
    regularHours,
    overtimeHours,
    updatedAt: new Date(),
  };
}

/**
 * 勤務時間計算 (REQ-EMPLOYEE-001-F021)
 * @param clockIn クロックイン時刻
 * @param clockOut クロックアウト時刻
 */
export function calculateWorkHours(
  clockIn: Date,
  clockOut: Date
): { regularHours: number; overtimeHours: number; breakMinutes: number } {
  const totalMinutes = (clockOut.getTime() - clockIn.getTime()) / (1000 * 60);
  const totalHours = totalMinutes / 60;
  
  // 6時間以上勤務した場合は休憩を控除
  const breakMinutes = totalHours >= BREAK_THRESHOLD_HOURS ? STANDARD_BREAK_MINUTES : 0;
  const actualWorkHours = Math.max(0, totalHours - breakMinutes / 60);
  
  // 通常時間と残業時間の分離
  const regularHours = Math.min(actualWorkHours, STANDARD_WORK_HOURS);
  const overtimeHours = Math.max(0, actualWorkHours - STANDARD_WORK_HOURS);
  
  return {
    regularHours: Math.round(regularHours * 100) / 100,
    overtimeHours: Math.round(overtimeHours * 100) / 100,
    breakMinutes,
  };
}

/**
 * 月次勤怠サマリー計算 (REQ-EMPLOYEE-001-F022)
 * @param employeeId 従業員ID
 * @param year 年
 * @param month 月（1-12）
 * @param records 勤怠記録リスト
 */
export function calculateMonthlySummary(
  employeeId: EmployeeId,
  year: number,
  month: number,
  records: Attendance[]
): MonthlySummary {
  let totalWorkedDays = 0;
  let totalRegularHours = 0;
  let totalOvertimeHours = 0;
  
  for (const record of records) {
    if (record.clockIn && record.clockOut) {
      totalWorkedDays++;
      totalRegularHours += record.regularHours;
      totalOvertimeHours += record.overtimeHours;
    }
  }
  
  return {
    employeeId,
    year,
    month,
    totalWorkedDays,
    totalRegularHours: Math.round(totalRegularHours * 100) / 100,
    totalOvertimeHours: Math.round(totalOvertimeHours * 100) / 100,
  };
}

/**
 * 日付を比較（日付部分のみ）
 */
export function isSameDate(date1: Date, date2: Date): boolean {
  return (
    date1.getFullYear() === date2.getFullYear() &&
    date1.getMonth() === date2.getMonth() &&
    date1.getDate() === date2.getDate()
  );
}
