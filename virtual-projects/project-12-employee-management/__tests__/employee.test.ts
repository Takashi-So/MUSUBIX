/**
 * Employee Entity and Service Tests
 * REQ-EMPLOYEE-001-F001, F002, F003, F040, F041
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createEmployee,
  changeEmployeeStatus,
  resetEmployeeCounter,
  createPersonName,
  employeeStatusTransitions,
} from '../src/domain/employee.js';
import { createMoney } from '../src/domain/money.js';
import { createDepartment, resetDepartmentCounter } from '../src/domain/department.js';
import { InvalidStatusTransitionError, DuplicateEmailError, DepartmentNotFoundError } from '../src/domain/errors.js';
import { InMemoryEmployeeRepository } from '../src/infrastructure/employee-repository.js';
import { InMemoryDepartmentRepository } from '../src/infrastructure/department-repository.js';
import { EmployeeService } from '../src/application/employee-service.js';

describe('Employee Entity', () => {
  // BP-TEST-001: Test Counter Reset
  beforeEach(() => {
    resetEmployeeCounter();
    resetDepartmentCounter();
  });

  describe('createEmployee', () => {
    it('should create employee with correct ID format (EMP-YYYYMMDD-NNN)', () => {
      const name = createPersonName('太郎', '山田');
      const employee = createEmployee({
        name,
        email: 'taro@example.com',
        hireDate: new Date('2026-01-15'),
        departmentId: 'DEPT-20260101-001',
        position: 'Engineer',
        employmentType: 'full_time',
        salary: createMoney(500000),
      });

      expect(employee.id).toMatch(/^EMP-\d{8}-001$/);
      expect(employee.name.fullName).toBe('山田 太郎');
      expect(employee.email).toBe('taro@example.com');
      expect(employee.status).toBe('active');
    });

    it('should generate sequential IDs', () => {
      const name1 = createPersonName('太郎', '山田');
      const name2 = createPersonName('花子', '佐藤');

      const emp1 = createEmployee({
        name: name1,
        email: 'emp1@example.com',
        hireDate: new Date(),
        departmentId: 'DEPT-001',
        position: 'Engineer',
        employmentType: 'full_time',
        salary: createMoney(500000),
      });

      const emp2 = createEmployee({
        name: name2,
        email: 'emp2@example.com',
        hireDate: new Date(),
        departmentId: 'DEPT-001',
        position: 'Designer',
        employmentType: 'part_time',
        salary: createMoney(300000),
      });

      expect(emp1.id).toMatch(/-001$/);
      expect(emp2.id).toMatch(/-002$/);
    });
  });

  describe('changeEmployeeStatus (REQ-EMPLOYEE-001-F002)', () => {
    it('should allow valid status transitions', () => {
      const name = createPersonName('太郎', '山田');
      const employee = createEmployee({
        name,
        email: 'test@example.com',
        hireDate: new Date(),
        departmentId: 'DEPT-001',
        position: 'Engineer',
        employmentType: 'full_time',
        salary: createMoney(500000),
      });

      // active → on_leave
      const onLeave = changeEmployeeStatus(employee, 'on_leave');
      expect(onLeave.status).toBe('on_leave');

      // on_leave → active
      const backToActive = changeEmployeeStatus(onLeave, 'active');
      expect(backToActive.status).toBe('active');
    });

    it('should reject invalid status transitions (REQ-EMPLOYEE-001-F041)', () => {
      const name = createPersonName('太郎', '山田');
      const employee = createEmployee({
        name,
        email: 'test@example.com',
        hireDate: new Date(),
        departmentId: 'DEPT-001',
        position: 'Engineer',
        employmentType: 'full_time',
        salary: createMoney(500000),
      });

      // active → paid (invalid)
      expect(() => changeEmployeeStatus(employee, 'terminated')).not.toThrow();
      
      // Create terminated employee
      const terminated = changeEmployeeStatus(employee, 'terminated');
      
      // terminated → active (invalid - no transitions from terminated)
      expect(() => changeEmployeeStatus(terminated, 'active'))
        .toThrow(InvalidStatusTransitionError);
    });
  });
});

describe('EmployeeService', () => {
  let employeeRepository: InMemoryEmployeeRepository;
  let departmentRepository: InMemoryDepartmentRepository;
  let employeeService: EmployeeService;

  beforeEach(() => {
    resetEmployeeCounter();
    resetDepartmentCounter();
    employeeRepository = new InMemoryEmployeeRepository();
    departmentRepository = new InMemoryDepartmentRepository();
    employeeService = new EmployeeService(employeeRepository, departmentRepository);
  });

  describe('registerEmployee (REQ-EMPLOYEE-001-F001)', () => {
    it('should register employee successfully', async () => {
      // Setup department
      const dept = createDepartment({ name: 'Engineering', code: 'ENG' });
      await departmentRepository.save(dept);

      const name = createPersonName('太郎', '山田');
      const employee = await employeeService.registerEmployee({
        name,
        email: 'taro@example.com',
        hireDate: new Date('2026-01-15'),
        departmentId: dept.id,
        position: 'Engineer',
        employmentType: 'full_time',
        salary: createMoney(500000),
      });

      expect(employee.id).toBeDefined();
      expect(employee.status).toBe('active');
    });

    it('should reject duplicate email (REQ-EMPLOYEE-001-F040)', async () => {
      const dept = createDepartment({ name: 'Engineering', code: 'ENG' });
      await departmentRepository.save(dept);

      const name = createPersonName('太郎', '山田');
      await employeeService.registerEmployee({
        name,
        email: 'duplicate@example.com',
        hireDate: new Date(),
        departmentId: dept.id,
        position: 'Engineer',
        employmentType: 'full_time',
        salary: createMoney(500000),
      });

      const name2 = createPersonName('花子', '佐藤');
      await expect(employeeService.registerEmployee({
        name: name2,
        email: 'duplicate@example.com', // Same email
        hireDate: new Date(),
        departmentId: dept.id,
        position: 'Designer',
        employmentType: 'full_time',
        salary: createMoney(400000),
      })).rejects.toThrow(DuplicateEmailError);
    });

    it('should reject non-existent department', async () => {
      const name = createPersonName('太郎', '山田');
      await expect(employeeService.registerEmployee({
        name,
        email: 'test@example.com',
        hireDate: new Date(),
        departmentId: 'NON-EXISTENT-DEPT',
        position: 'Engineer',
        employmentType: 'full_time',
        salary: createMoney(500000),
      })).rejects.toThrow(DepartmentNotFoundError);
    });
  });

  describe('searchEmployees (REQ-EMPLOYEE-001-F003)', () => {
    it('should search by name', async () => {
      const dept = createDepartment({ name: 'Engineering', code: 'ENG' });
      await departmentRepository.save(dept);

      const name1 = createPersonName('太郎', '山田');
      await employeeService.registerEmployee({
        name: name1,
        email: 'yamada@example.com',
        hireDate: new Date(),
        departmentId: dept.id,
        position: 'Engineer',
        employmentType: 'full_time',
        salary: createMoney(500000),
      });

      const name2 = createPersonName('花子', '佐藤');
      await employeeService.registerEmployee({
        name: name2,
        email: 'sato@example.com',
        hireDate: new Date(),
        departmentId: dept.id,
        position: 'Designer',
        employmentType: 'full_time',
        salary: createMoney(400000),
      });

      const results = await employeeService.searchEmployees({ name: '山田' });
      expect(results).toHaveLength(1);
      expect(results[0].name.lastName).toBe('山田');
    });

    it('should search by employment type', async () => {
      const dept = createDepartment({ name: 'Engineering', code: 'ENG' });
      await departmentRepository.save(dept);

      const name1 = createPersonName('太郎', '山田');
      await employeeService.registerEmployee({
        name: name1,
        email: 'ft@example.com',
        hireDate: new Date(),
        departmentId: dept.id,
        position: 'Engineer',
        employmentType: 'full_time',
        salary: createMoney(500000),
      });

      const name2 = createPersonName('花子', '佐藤');
      await employeeService.registerEmployee({
        name: name2,
        email: 'pt@example.com',
        hireDate: new Date(),
        departmentId: dept.id,
        position: 'Assistant',
        employmentType: 'part_time',
        salary: createMoney(200000),
      });

      const results = await employeeService.searchEmployees({ employmentType: 'part_time' });
      expect(results).toHaveLength(1);
      expect(results[0].employmentType).toBe('part_time');
    });
  });
});
