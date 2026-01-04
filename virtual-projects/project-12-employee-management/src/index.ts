/**
 * Employee Management System - Main Exports
 */

// Domain Types
export * from './domain/types.js';

// Domain Entities
export * from './domain/employee.js';
export * from './domain/department.js';
export * from './domain/attendance.js';
export * from './domain/payroll.js';

// Value Objects
export * from './domain/money.js';

// Domain Errors
export * from './domain/errors.js';

// Repositories
export { InMemoryEmployeeRepository } from './infrastructure/employee-repository.js';
export { InMemoryDepartmentRepository } from './infrastructure/department-repository.js';
export { InMemoryAttendanceRepository } from './infrastructure/attendance-repository.js';
export { InMemoryPayrollRepository } from './infrastructure/payroll-repository.js';

// Application Services
export { EmployeeService } from './application/employee-service.js';
export { DepartmentService, DepartmentTreeNode } from './application/department-service.js';
export { AttendanceService } from './application/attendance-service.js';
export { PayrollService } from './application/payroll-service.js';
