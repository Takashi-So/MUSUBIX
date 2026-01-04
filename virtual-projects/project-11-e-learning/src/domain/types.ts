/**
 * E-Learning Platform - Type Definitions
 * Traceability: DES-ELEARN-001 §4.2
 */

// =============================================================================
// ID Types (BP-CODE-002: Date-based ID Format)
// =============================================================================

export type InstructorId = `INS-${string}`;
export type CourseId = `CRS-${string}`;
export type LessonId = `LES-${string}`;
export type LearnerId = `LRN-${string}`;
export type EnrollmentId = `ENR-${string}`;
export type QuizId = `QIZ-${string}`;
export type QuizAttemptId = `ATT-${string}`;
export type CertificateId = `CERT-${string}`;
export type LessonProgressId = `LPG-${string}`;

// =============================================================================
// Enums
// =============================================================================

export type CourseCategory = 
  | 'programming' 
  | 'business' 
  | 'design' 
  | 'language' 
  | 'science' 
  | 'other';

export type DifficultyLevel = 'beginner' | 'intermediate' | 'advanced';

export type CourseStatus = 'draft' | 'published' | 'archived';

export type EnrollmentStatus = 'active' | 'completed' | 'dropped';

export type ContentType = 'video' | 'text' | 'quiz';

export type QuestionType = 'single-choice' | 'multiple-choice' | 'true-false';

// =============================================================================
// Status Transition Maps (BP-DESIGN-001)
// =============================================================================

export const validCourseStatusTransitions: Record<CourseStatus, CourseStatus[]> = {
  draft: ['published'],
  published: ['archived'],
  archived: ['published'],
};

export const validEnrollmentStatusTransitions: Record<EnrollmentStatus, EnrollmentStatus[]> = {
  active: ['completed', 'dropped'],
  completed: [],
  dropped: ['active'],
};

// =============================================================================
// Input DTOs (BP-CODE-001: Entity Input DTO)
// =============================================================================

export interface CreateInstructorInput {
  name: string;
  email: string;
  passwordHash: string;
  bio: string;
  profilePicture?: string;
  expertiseAreas?: string[];
}

export interface CreateCourseInput {
  title: string;
  description: string;
  category: CourseCategory;
  difficultyLevel: DifficultyLevel;
  instructorId: InstructorId;
  thumbnail?: string;
  prerequisites?: string[];
  estimatedDurationMinutes?: number;
}

export interface CreateLessonInput {
  courseId: CourseId;
  title: string;
  contentType: ContentType;
  content: string;
  order: number;
  durationMinutes?: number;
}

export interface CreateLearnerInput {
  name: string;
  email: string;
  passwordHash: string;
  profilePicture?: string;
  bio?: string;
  learningInterests?: string[];
}

export interface CreateEnrollmentInput {
  learnerId: LearnerId;
  courseId: CourseId;
}

export interface Question {
  id: string;
  text: string;
  type: QuestionType;
  options: string[];
  correctAnswers: number[];
  points: number;
}

export interface CreateQuizInput {
  lessonId: LessonId;
  title: string;
  questions: Question[];
  passingScorePercent: number;
  timeLimitMinutes?: number;
  maxAttempts?: number;
}

export interface CreateQuizAttemptInput {
  quizId: QuizId;
  learnerId: LearnerId;
  answers: Record<string, number[]>;
}

export interface CreateCertificateInput {
  enrollmentId: EnrollmentId;
  learnerId: LearnerId;
  courseId: CourseId;
  learnerName: string;
  courseTitle: string;
  instructorName: string;
}

// =============================================================================
// Entity Interfaces
// =============================================================================

export interface Instructor {
  id: InstructorId;
  name: string;
  email: string;
  passwordHash: string;
  bio: string;
  profilePicture?: string;
  expertiseAreas: string[];
  createdAt: Date;
  updatedAt: Date;
}

export interface Course {
  id: CourseId;
  title: string;
  description: string;
  category: CourseCategory;
  difficultyLevel: DifficultyLevel;
  instructorId: InstructorId;
  status: CourseStatus;
  thumbnail?: string;
  prerequisites: string[];
  estimatedDurationMinutes?: number;
  createdAt: Date;
  updatedAt: Date;
}

export interface Lesson {
  id: LessonId;
  courseId: CourseId;
  title: string;
  contentType: ContentType;
  content: string;
  order: number;
  durationMinutes?: number;
  createdAt: Date;
  updatedAt: Date;
}

export interface Learner {
  id: LearnerId;
  name: string;
  email: string;
  passwordHash: string;
  profilePicture?: string;
  bio?: string;
  learningInterests: string[];
  createdAt: Date;
  updatedAt: Date;
}

export interface Enrollment {
  id: EnrollmentId;
  learnerId: LearnerId;
  courseId: CourseId;
  status: EnrollmentStatus;
  progressPercent: number;
  completedLessonIds: LessonId[];
  enrolledAt: Date;
  completedAt?: Date;
}

export interface Quiz {
  id: QuizId;
  lessonId: LessonId;
  title: string;
  questions: Question[];
  passingScorePercent: number;
  timeLimitMinutes?: number;
  maxAttempts?: number;
  createdAt: Date;
  updatedAt: Date;
}

export interface QuizAttempt {
  id: QuizAttemptId;
  quizId: QuizId;
  learnerId: LearnerId;
  answers: Record<string, number[]>;
  scorePercent: number;
  passed: boolean;
  startedAt: Date;
  completedAt: Date;
}

export interface Certificate {
  id: CertificateId;
  enrollmentId: EnrollmentId;
  learnerId: LearnerId;
  courseId: CourseId;
  learnerName: string;
  courseTitle: string;
  instructorName: string;
  issuedAt: Date;
}

// =============================================================================
// Search Criteria
// =============================================================================

export interface CourseSearchCriteria {
  titleKeyword?: string;
  category?: CourseCategory;
  difficultyLevel?: DifficultyLevel;
  instructorId?: InstructorId;
  status?: CourseStatus;
}
