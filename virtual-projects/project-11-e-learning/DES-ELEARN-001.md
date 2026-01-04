# Design Document: E-Learning Platform
## DES-ELEARN-001 v1.0.0

### 1. Document Information

| Item | Value |
|------|-------|
| **Version** | 1.0.0 |
| **Status** | Approved |
| **Created** | 2026-01-04 |
| **Author** | MUSUBIX SDD System |
| **Requirements** | REQ-ELEARN-001 v1.1.0 |

---

### 2. Design Overview

#### 2.1 Architecture Style
**Clean Architecture** with Domain-Driven Design (DDD) principles

#### 2.2 Design Patterns Applied

| Pattern | Usage | Rationale | Traceability |
|---------|-------|-----------|--------------|
| **Repository** | Data access abstraction | Decouple domain from persistence | BP-DESIGN-002 |
| **Service Layer** | Business logic encapsulation | Separation of concerns | BP-DESIGN-003 |
| **Factory** | Entity creation with Input DTO | Complex object instantiation | BP-CODE-001 |
| **Strategy** | Progress calculation | Multiple calculation algorithms | - |
| **Specification** | Search criteria | Flexible query composition | - |
| **Status Transition Map** | Course/Enrollment status | Valid state transitions | BP-DESIGN-001 |

---

### 3. C4 Model

#### 3.1 Level 1: System Context

```
┌─────────────────────────────────────────────────────────────────┐
│                        External Systems                          │
├─────────────────────────────────────────────────────────────────┤
│  ┌──────────┐  ┌──────────┐  ┌──────────┐                       │
│  │  Email   │  │  Video   │  │  Storage │                       │
│  │ Service  │  │ Hosting  │  │ Service  │                       │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘                       │
└───────┼─────────────┼────────────┼──────────────────────────────┘
        │             │            │
        └─────────────┴────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────────────────────────┐
│                  E-Learning Platform                             │
│                                                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                    API Gateway                           │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              │                                   │
│  ┌──────────┬──────────┬─────┴────┬──────────┬──────────────┐   │
│  │  Course  │  Lesson  │ Learner  │  Quiz    │ Certificate  │   │
│  │  Service │  Service │ Service  │ Service  │   Service    │   │
│  └──────────┴──────────┴──────────┴──────────┴──────────────┘   │
└─────────────────────────────────────────────────────────────────┘
                              │
        ┌─────────────────────┴─────────────────────┐
        ▼                     ▼                     ▼
┌──────────────┐    ┌──────────────┐    ┌──────────────────┐
│  Instructor  │    │   Learner    │    │  Administrator   │
└──────────────┘    └──────────────┘    └──────────────────┘
```

#### 3.2 Level 2: Container Diagram

```
┌─────────────────────────────────────────────────────────────────────┐
│                    E-Learning Platform                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │                     Web Application (SPA)                       │ │
│  │                     [React + TypeScript]                        │ │
│  └────────────────────────────────┬───────────────────────────────┘ │
│                                   │ HTTPS/REST                       │
│  ┌────────────────────────────────▼───────────────────────────────┐ │
│  │                       API Gateway                               │ │
│  │                    [Node.js + Express]                          │ │
│  │           Authentication, Rate Limiting, Routing                │ │
│  └────────────────────────────────┬───────────────────────────────┘ │
│                                   │                                  │
│  ┌────────────┬───────────┬───────┴────┬───────────┬─────────────┐  │
│  │            │           │            │           │             │  │
│  ▼            ▼           ▼            ▼           ▼             │  │
│ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌──────────┐        │  │
│ │ Course │ │ Lesson │ │Learner │ │  Quiz  │ │Certific. │        │  │
│ │Service │ │Service │ │Service │ │Service │ │ Service  │        │  │
│ │[Node]  │ │[Node]  │ │[Node]  │ │[Node]  │ │ [Node]   │        │  │
│ └───┬────┘ └───┬────┘ └───┬────┘ └───┬────┘ └────┬─────┘        │  │
│     │          │          │          │           │               │  │
│     └──────────┴──────────┴────┬─────┴───────────┘               │  │
│                                │                                  │  │
│                    ┌───────────▼───────────┐                     │  │
│                    │     PostgreSQL        │                     │  │
│                    │  [Relational DB]      │                     │  │
│                    └───────────────────────┘                     │  │
└─────────────────────────────────────────────────────────────────────┘
```

---

### 4. Domain Model

#### 4.1 Entity Definitions

##### 4.1.0 Instructor Entity
**Traceability**: REQ-ELEARN-001-F000

```typescript
interface CreateInstructorInput {
  name: string;
  email: string;
  passwordHash: string;
  bio: string;
  profilePicture?: string;
  expertiseAreas?: string[];
}

interface Instructor {
  id: InstructorId;           // INS-YYYYMMDD-NNN
  name: string;
  email: string;
  passwordHash: string;
  bio: string;
  profilePicture?: string;
  expertiseAreas: string[];
  createdAt: Date;
  updatedAt: Date;
}
```

##### 4.1.1 Course Entity
**Traceability**: REQ-ELEARN-001-F001, F002

```typescript
type CourseStatus = 'draft' | 'published' | 'archived';

// BP-DESIGN-001: Status Transition Map
const validCourseStatusTransitions: Record<CourseStatus, CourseStatus[]> = {
  draft: ['published'],       // requires at least 1 lesson
  published: ['archived'],
  archived: ['published'],
};

interface CreateCourseInput {
  title: string;
  description: string;
  category: CourseCategory;
  difficultyLevel: DifficultyLevel;
  instructorId: InstructorId;
  thumbnail?: string;
  prerequisites?: string[];
  estimatedDurationMinutes?: number;
}

interface Course {
  id: CourseId;               // CRS-YYYYMMDD-NNN
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
```

##### 4.1.2 Lesson Entity
**Traceability**: REQ-ELEARN-001-F010, F011

```typescript
type ContentType = 'video' | 'text' | 'quiz';

interface CreateLessonInput {
  courseId: CourseId;
  title: string;
  contentType: ContentType;
  content: string;            // URL for video, text content, or quiz ID
  order: number;
  durationMinutes?: number;
}

interface Lesson {
  id: LessonId;               // LES-YYYYMMDD-NNN
  courseId: CourseId;
  title: string;
  contentType: ContentType;
  content: string;
  order: number;
  durationMinutes?: number;
  createdAt: Date;
  updatedAt: Date;
}
```

##### 4.1.3 Learner Entity
**Traceability**: REQ-ELEARN-001-F020

```typescript
interface CreateLearnerInput {
  name: string;
  email: string;
  passwordHash: string;
  profilePicture?: string;
  bio?: string;
  learningInterests?: string[];
}

interface Learner {
  id: LearnerId;              // LRN-YYYYMMDD-NNN
  name: string;
  email: string;
  passwordHash: string;
  profilePicture?: string;
  bio?: string;
  learningInterests: string[];
  createdAt: Date;
  updatedAt: Date;
}
```

##### 4.1.4 Enrollment Entity
**Traceability**: REQ-ELEARN-001-F021, F030, F031, F032

```typescript
type EnrollmentStatus = 'active' | 'completed' | 'dropped';

// BP-DESIGN-001: Status Transition Map
const validEnrollmentStatusTransitions: Record<EnrollmentStatus, EnrollmentStatus[]> = {
  active: ['completed', 'dropped'],
  completed: [],              // terminal state
  dropped: ['active'],        // can re-enroll
};

interface CreateEnrollmentInput {
  learnerId: LearnerId;
  courseId: CourseId;
}

interface Enrollment {
  id: EnrollmentId;           // ENR-YYYYMMDD-NNN
  learnerId: LearnerId;
  courseId: CourseId;
  status: EnrollmentStatus;
  progressPercent: number;    // 0-100
  completedLessonIds: LessonId[];
  enrolledAt: Date;
  completedAt?: Date;
}
```

##### 4.1.5 LessonProgress Entity
**Traceability**: REQ-ELEARN-001-F030

```typescript
interface CreateLessonProgressInput {
  enrollmentId: EnrollmentId;
  lessonId: LessonId;
}

interface LessonProgress {
  id: LessonProgressId;
  enrollmentId: EnrollmentId;
  lessonId: LessonId;
  isCompleted: boolean;
  completedAt?: Date;
  lastAccessedAt: Date;
}
```

##### 4.1.6 Quiz Entity
**Traceability**: REQ-ELEARN-001-F040, F041, F042

```typescript
type QuestionType = 'single-choice' | 'multiple-choice' | 'true-false';

interface Question {
  id: string;
  text: string;
  type: QuestionType;
  options: string[];
  correctAnswers: number[];   // indices of correct options
  points: number;
}

interface CreateQuizInput {
  lessonId: LessonId;
  title: string;
  questions: Question[];
  passingScorePercent: number;
  timeLimitMinutes?: number;
  maxAttempts?: number;
}

interface Quiz {
  id: QuizId;                 // QIZ-YYYYMMDD-NNN
  lessonId: LessonId;
  title: string;
  questions: Question[];
  passingScorePercent: number;
  timeLimitMinutes?: number;
  maxAttempts?: number;
  createdAt: Date;
  updatedAt: Date;
}
```

##### 4.1.7 QuizAttempt Entity
**Traceability**: REQ-ELEARN-001-F041

```typescript
interface CreateQuizAttemptInput {
  quizId: QuizId;
  learnerId: LearnerId;
  answers: Record<string, number[]>;  // questionId -> selected option indices
}

interface QuizAttempt {
  id: QuizAttemptId;          // ATT-YYYYMMDD-NNN
  quizId: QuizId;
  learnerId: LearnerId;
  answers: Record<string, number[]>;
  scorePercent: number;
  passed: boolean;
  startedAt: Date;
  completedAt: Date;
}
```

##### 4.1.8 Certificate Entity
**Traceability**: REQ-ELEARN-001-F050

```typescript
interface CreateCertificateInput {
  enrollmentId: EnrollmentId;
  learnerId: LearnerId;
  courseId: CourseId;
}

interface Certificate {
  id: CertificateId;          // CERT-YYYYMMDD-NNN
  enrollmentId: EnrollmentId;
  learnerId: LearnerId;
  courseId: CourseId;
  learnerName: string;
  courseTitle: string;
  instructorName: string;
  issuedAt: Date;
}
```

#### 4.2 Value Objects

```typescript
// ID Types (BP-CODE-002: Date-based ID Format)
type InstructorId = `INS-${string}`;
type CourseId = `CRS-${string}`;
type LessonId = `LES-${string}`;
type LearnerId = `LRN-${string}`;
type EnrollmentId = `ENR-${string}`;
type QuizId = `QIZ-${string}`;
type QuizAttemptId = `ATT-${string}`;
type CertificateId = `CERT-${string}`;

// Enums
type CourseCategory = 
  | 'programming' 
  | 'business' 
  | 'design' 
  | 'language' 
  | 'science' 
  | 'other';

type DifficultyLevel = 'beginner' | 'intermediate' | 'advanced';
```

---

### 5. Service Layer

#### 5.1 CourseService
**Traceability**: REQ-ELEARN-001-F001, F002, F003

```typescript
interface CourseService {
  // Course CRUD
  createCourse(input: CreateCourseInput): Promise<Course>;
  getCourse(id: CourseId): Promise<Course | null>;
  updateCourse(id: CourseId, updates: Partial<CreateCourseInput>): Promise<Course>;
  
  // Status management (BP-DESIGN-001)
  publishCourse(id: CourseId): Promise<Course>;
  archiveCourse(id: CourseId): Promise<Course>;
  
  // Search
  searchCourses(criteria: CourseSearchCriteria): Promise<Course[]>;
  
  // Queries
  getCoursesByInstructor(instructorId: InstructorId): Promise<Course[]>;
  getLessonCount(courseId: CourseId): Promise<number>;
}
```

#### 5.2 EnrollmentService
**Traceability**: REQ-ELEARN-001-F021, F030, F031, F032, F060

```typescript
interface EnrollmentService {
  // Enrollment
  enrollLearner(input: CreateEnrollmentInput): Promise<Enrollment>;
  getEnrollment(id: EnrollmentId): Promise<Enrollment | null>;
  getEnrollmentByLearnerAndCourse(learnerId: LearnerId, courseId: CourseId): Promise<Enrollment | null>;
  
  // Progress tracking
  completeLesson(enrollmentId: EnrollmentId, lessonId: LessonId): Promise<Enrollment>;
  getProgress(enrollmentId: EnrollmentId): Promise<number>;
  
  // Status management
  dropEnrollment(enrollmentId: EnrollmentId): Promise<Enrollment>;
}
```

#### 5.3 QuizService
**Traceability**: REQ-ELEARN-001-F040, F041, F042

```typescript
interface QuizService {
  // Quiz CRUD
  createQuiz(input: CreateQuizInput): Promise<Quiz>;
  getQuiz(id: QuizId): Promise<Quiz | null>;
  
  // Attempt management
  submitQuizAttempt(input: CreateQuizAttemptInput): Promise<QuizAttempt>;
  getAttemptsByLearner(quizId: QuizId, learnerId: LearnerId): Promise<QuizAttempt[]>;
  canAttemptQuiz(quizId: QuizId, learnerId: LearnerId): Promise<boolean>;
}
```

#### 5.4 CertificateService
**Traceability**: REQ-ELEARN-001-F050

```typescript
interface CertificateService {
  generateCertificate(enrollmentId: EnrollmentId): Promise<Certificate>;
  getCertificate(id: CertificateId): Promise<Certificate | null>;
  verifyCertificate(id: CertificateId): Promise<boolean>;
}
```

---

### 6. Repository Layer

#### 6.1 Repository Interfaces (BP-DESIGN-002)

```typescript
interface InstructorRepository {
  save(instructor: Instructor): Promise<void>;
  findById(id: InstructorId): Promise<Instructor | null>;
  findByEmail(email: string): Promise<Instructor | null>;
  findAll(): Promise<Instructor[]>;
  delete(id: InstructorId): Promise<void>;
}

interface CourseRepository {
  save(course: Course): Promise<void>;
  findById(id: CourseId): Promise<Course | null>;
  findByInstructorId(instructorId: InstructorId): Promise<Course[]>;
  search(criteria: CourseSearchCriteria): Promise<Course[]>;
  findAll(): Promise<Course[]>;
  delete(id: CourseId): Promise<void>;
}

interface LessonRepository {
  save(lesson: Lesson): Promise<void>;
  findById(id: LessonId): Promise<Lesson | null>;
  findByCourseId(courseId: CourseId): Promise<Lesson[]>;
  delete(id: LessonId): Promise<void>;
  updateOrder(lessonIds: LessonId[]): Promise<void>;
}

interface LearnerRepository {
  save(learner: Learner): Promise<void>;
  findById(id: LearnerId): Promise<Learner | null>;
  findByEmail(email: string): Promise<Learner | null>;
  findAll(): Promise<Learner[]>;
  delete(id: LearnerId): Promise<void>;
}

interface EnrollmentRepository {
  save(enrollment: Enrollment): Promise<void>;
  findById(id: EnrollmentId): Promise<Enrollment | null>;
  findByLearnerAndCourse(learnerId: LearnerId, courseId: CourseId): Promise<Enrollment | null>;
  findByLearnerId(learnerId: LearnerId): Promise<Enrollment[]>;
  findByCourseId(courseId: CourseId): Promise<Enrollment[]>;
}

interface QuizRepository {
  save(quiz: Quiz): Promise<void>;
  findById(id: QuizId): Promise<Quiz | null>;
  findByLessonId(lessonId: LessonId): Promise<Quiz | null>;
}

interface QuizAttemptRepository {
  save(attempt: QuizAttempt): Promise<void>;
  findById(id: QuizAttemptId): Promise<QuizAttempt | null>;
  findByQuizAndLearner(quizId: QuizId, learnerId: LearnerId): Promise<QuizAttempt[]>;
  countByQuizAndLearner(quizId: QuizId, learnerId: LearnerId): Promise<number>;
}

interface CertificateRepository {
  save(certificate: Certificate): Promise<void>;
  findById(id: CertificateId): Promise<Certificate | null>;
  findByEnrollmentId(enrollmentId: EnrollmentId): Promise<Certificate | null>;
}
```

---

### 7. Error Handling

#### 7.1 Domain Errors

```typescript
class DuplicateEnrollmentError extends Error {
  constructor(learnerId: LearnerId, courseId: CourseId) {
    super(`Learner ${learnerId} is already enrolled in course ${courseId}`);
    this.name = 'DuplicateEnrollmentError';
  }
}

class InvalidProgressError extends Error {
  constructor(progress: number) {
    super(`Progress ${progress} is invalid. Must be between 0 and 100.`);
    this.name = 'InvalidProgressError';
  }
}

class InvalidStatusTransitionError extends Error {
  constructor(from: string, to: string) {
    super(`Invalid status transition from ${from} to ${to}`);
    this.name = 'InvalidStatusTransitionError';
  }
}

class CourseNotPublishedError extends Error {
  constructor(courseId: CourseId) {
    super(`Cannot enroll in unpublished course ${courseId}`);
    this.name = 'CourseNotPublishedError';
  }
}

class MaxAttemptsExceededError extends Error {
  constructor(quizId: QuizId, maxAttempts: number) {
    super(`Maximum attempts (${maxAttempts}) exceeded for quiz ${quizId}`);
    this.name = 'MaxAttemptsExceededError';
  }
}

class EnrollmentNotCompletedError extends Error {
  constructor(enrollmentId: EnrollmentId) {
    super(`Cannot generate certificate for incomplete enrollment ${enrollmentId}`);
    this.name = 'EnrollmentNotCompletedError';
  }
}
```

---

### 8. Traceability Matrix

| Requirement | Entity | Service | Repository | Test |
|-------------|--------|---------|------------|------|
| F000 | Instructor | InstructorService | InstructorRepository | TEST-000 |
| F001 | Course | CourseService.createCourse | CourseRepository | TEST-001 |
| F002 | Course | CourseService.publishCourse | CourseRepository | TEST-002 |
| F003 | - | CourseService.searchCourses | CourseRepository | TEST-003 |
| F010 | Lesson | LessonService.createLesson | LessonRepository | TEST-010 |
| F011 | Lesson | LessonService.reorderLessons | LessonRepository | TEST-011 |
| F020 | Learner | LearnerService.createLearner | LearnerRepository | TEST-020 |
| F021 | Enrollment | EnrollmentService.enrollLearner | EnrollmentRepository | TEST-021 |
| F030 | Enrollment | EnrollmentService.completeLesson | EnrollmentRepository | TEST-030 |
| F031 | Enrollment | - | EnrollmentRepository | TEST-031 |
| F032 | Enrollment | EnrollmentService.completeLesson | EnrollmentRepository | TEST-032 |
| F040 | Quiz | QuizService.createQuiz | QuizRepository | TEST-040 |
| F041 | QuizAttempt | QuizService.submitQuizAttempt | QuizAttemptRepository | TEST-041 |
| F042 | QuizAttempt | QuizService.canAttemptQuiz | QuizAttemptRepository | TEST-042 |
| F050 | Certificate | CertificateService.generateCertificate | CertificateRepository | TEST-050 |
| F060 | Enrollment | EnrollmentService.enrollLearner | EnrollmentRepository | TEST-060 |
| F061 | Enrollment | EnrollmentService.completeLesson | EnrollmentRepository | TEST-061 |

---

### 9. Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2026-01-04 | MUSUBIX SDD | Initial design based on REQ-ELEARN-001 v1.1.0 |
