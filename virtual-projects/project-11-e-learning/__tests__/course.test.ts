/**
 * Course Entity Tests
 * Traceability: REQ-ELEARN-001-F001, F002, TEST-001, TEST-002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { 
  createCourse, 
  resetCourseCounter,
  canTransitionCourseStatus,
  transitionCourseStatus
} from '../src/domain/course.js';
import type { CreateCourseInput, InstructorId } from '../src/domain/types.js';

describe('Course Entity', () => {
  // BP-TEST-001: Test Counter Reset
  beforeEach(() => {
    resetCourseCounter();
  });

  describe('createCourse', () => {
    const validInput: CreateCourseInput = {
      title: 'TypeScript Fundamentals',
      description: 'Learn TypeScript from scratch',
      category: 'programming',
      difficultyLevel: 'beginner',
      instructorId: 'INS-20260104-001' as InstructorId,
    };

    it('should create a course with valid input', () => {
      const course = createCourse(validInput);
      
      expect(course.id).toMatch(/^CRS-\d{8}-001$/);
      expect(course.title).toBe('TypeScript Fundamentals');
      expect(course.description).toBe('Learn TypeScript from scratch');
      expect(course.category).toBe('programming');
      expect(course.difficultyLevel).toBe('beginner');
      expect(course.status).toBe('draft'); // Initial status
      expect(course.prerequisites).toEqual([]);
      expect(course.createdAt).toBeInstanceOf(Date);
      expect(course.updatedAt).toBeInstanceOf(Date);
    });

    it('should generate sequential IDs', () => {
      const course1 = createCourse(validInput);
      const course2 = createCourse(validInput);
      
      expect(course1.id).toMatch(/-001$/);
      expect(course2.id).toMatch(/-002$/);
    });

    it('should throw error for empty title', () => {
      expect(() => createCourse({ ...validInput, title: '' }))
        .toThrow('Course title is required');
    });

    it('should throw error for empty description', () => {
      expect(() => createCourse({ ...validInput, description: '' }))
        .toThrow('Course description is required');
    });

    it('should trim title and description', () => {
      const course = createCourse({
        ...validInput,
        title: '  Trimmed Title  ',
        description: '  Trimmed Description  ',
      });
      
      expect(course.title).toBe('Trimmed Title');
      expect(course.description).toBe('Trimmed Description');
    });

    it('should include optional fields when provided', () => {
      const course = createCourse({
        ...validInput,
        thumbnail: 'https://example.com/thumb.jpg',
        prerequisites: ['Basic JavaScript'],
        estimatedDurationMinutes: 120,
      });
      
      expect(course.thumbnail).toBe('https://example.com/thumb.jpg');
      expect(course.prerequisites).toEqual(['Basic JavaScript']);
      expect(course.estimatedDurationMinutes).toBe(120);
    });
  });

  describe('status transitions (BP-DESIGN-001)', () => {
    it('should allow draft → published', () => {
      expect(canTransitionCourseStatus('draft', 'published')).toBe(true);
    });

    it('should allow published → archived', () => {
      expect(canTransitionCourseStatus('published', 'archived')).toBe(true);
    });

    it('should allow archived → published', () => {
      expect(canTransitionCourseStatus('archived', 'published')).toBe(true);
    });

    it('should not allow draft → archived', () => {
      expect(canTransitionCourseStatus('draft', 'archived')).toBe(false);
    });

    it('should not allow published → draft', () => {
      expect(canTransitionCourseStatus('published', 'draft')).toBe(false);
    });

    it('should transition course status', () => {
      const validInput: CreateCourseInput = {
        title: 'Test Course',
        description: 'Test Description',
        category: 'programming',
        difficultyLevel: 'beginner',
        instructorId: 'INS-20260104-001' as InstructorId,
      };
      
      const course = createCourse(validInput);
      expect(course.status).toBe('draft');
      
      const published = transitionCourseStatus(course, 'published');
      expect(published.status).toBe('published');
    });

    it('should throw error for invalid transition', () => {
      const validInput: CreateCourseInput = {
        title: 'Test Course',
        description: 'Test Description',
        category: 'programming',
        difficultyLevel: 'beginner',
        instructorId: 'INS-20260104-001' as InstructorId,
      };
      
      const course = createCourse(validInput);
      
      expect(() => transitionCourseStatus(course, 'archived'))
        .toThrow('Invalid status transition from draft to archived');
    });
  });
});
