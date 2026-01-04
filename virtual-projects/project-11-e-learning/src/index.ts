/**
 * E-Learning Platform - Main Entry Point
 * Traceability: Constitution Article II (CLI Interface)
 */

// Domain Types
export * from './domain/types.js';

// Domain Entities
export { createInstructor, resetInstructorCounter } from './domain/instructor.js';
export { 
  createCourse, 
  resetCourseCounter, 
  canTransitionCourseStatus, 
  transitionCourseStatus 
} from './domain/course.js';
export { createLesson, resetLessonCounter, updateLessonOrder } from './domain/lesson.js';
export { createLearner, resetLearnerCounter } from './domain/learner.js';
export { 
  createEnrollment, 
  resetEnrollmentCounter,
  canTransitionEnrollmentStatus,
  transitionEnrollmentStatus,
  completeLessonInEnrollment,
  calculateProgress
} from './domain/enrollment.js';
export { createQuiz, resetQuizCounter, getTotalPoints } from './domain/quiz.js';
export { 
  createQuizAttempt, 
  resetQuizAttemptCounter, 
  calculateQuizScore 
} from './domain/quiz-attempt.js';
export { createCertificate, resetCertificateCounter } from './domain/certificate.js';

// Repositories
export type { InstructorRepository } from './infrastructure/instructor-repository.js';
export { InMemoryInstructorRepository } from './infrastructure/instructor-repository.js';

export type { CourseRepository } from './infrastructure/course-repository.js';
export { InMemoryCourseRepository } from './infrastructure/course-repository.js';

export type { LessonRepository } from './infrastructure/lesson-repository.js';
export { InMemoryLessonRepository } from './infrastructure/lesson-repository.js';

export type { LearnerRepository } from './infrastructure/learner-repository.js';
export { InMemoryLearnerRepository } from './infrastructure/learner-repository.js';

export type { EnrollmentRepository } from './infrastructure/enrollment-repository.js';
export { InMemoryEnrollmentRepository } from './infrastructure/enrollment-repository.js';

export type { QuizRepository } from './infrastructure/quiz-repository.js';
export { InMemoryQuizRepository } from './infrastructure/quiz-repository.js';

export type { QuizAttemptRepository } from './infrastructure/quiz-attempt-repository.js';
export { InMemoryQuizAttemptRepository } from './infrastructure/quiz-attempt-repository.js';

export type { CertificateRepository } from './infrastructure/certificate-repository.js';
export { InMemoryCertificateRepository } from './infrastructure/certificate-repository.js';

// Services
export { 
  CourseService, 
  CourseNotFoundError, 
  CannotPublishCourseError 
} from './application/course-service.js';

export { 
  EnrollmentService,
  DuplicateEnrollmentError,
  EnrollmentNotFoundError as EnrollmentServiceNotFoundError,
  CourseNotPublishedError,
  LessonNotFoundError,
  LessonNotInCourseError
} from './application/enrollment-service.js';

export { 
  CertificateService,
  EnrollmentNotCompletedError,
  CertificateAlreadyExistsError,
  CertificateNotFoundError,
  EnrollmentNotFoundError
} from './application/certificate-service.js';
