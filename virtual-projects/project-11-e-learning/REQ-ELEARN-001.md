# Requirements Document: E-Learning Platform
## REQ-ELEARN-001 v1.1.0

### 1. Document Information

| Item | Value |
|------|-------|
| **Version** | 1.1.0 |
| **Status** | Approved |
| **Created** | 2026-01-04 |
| **Updated** | 2026-01-04 |
| **Author** | MUSUBIX SDD System |
| **Domain** | Education |
| **Review Status** | Reviewed and approved after v1.0.0 feedback |

---

### 2. System Overview

#### 2.1 Purpose
E-Learning Platform（eラーニングプラットフォーム）は、オンライン教育を提供するシステムです。講師がコースを作成・管理し、学習者がコースを受講して学習進捗を追跡できます。

#### 2.2 Scope
- コース管理（作成・編集・公開）
- レッスン管理（動画・テキスト・クイズ）
- 学習者管理（登録・プロファイル）
- 学習進捗管理
- クイズ・テスト管理
- 修了証発行

#### 2.3 Stakeholders

| Stakeholder | Role | Interest |
|-------------|------|----------|
| **Instructor** | 講師 | コース作成・管理、学習者の進捗確認 |
| **Learner** | 学習者 | コース受講、学習進捗確認 |
| **Administrator** | 管理者 | システム管理、ユーザー管理 |

---

### 3. Functional Requirements (EARS Format)

#### 3.0 Instructor Management Requirements

##### REQ-ELEARN-001-F000: Instructor Registration
**Category**: Instructor Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a new instructor registers, **THE** system **SHALL** store instructor information including name, email, bio, and expertise areas with a unique instructor ID.

**Instructor ID Format**: `INS-YYYYMMDD-NNN`

**Required Fields**:
- Name (display name)
- Email (unique)
- Password (hashed)
- Bio

**Optional Fields**:
- Profile picture
- Expertise areas
- Social links

---

#### 3.1 Course Management Requirements

##### REQ-ELEARN-001-F001: Course Creation
**Category**: Course Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** an instructor creates a new course, **THE** system **SHALL** store course details including title, description, category, difficulty level, and instructor ID with a unique course ID.

**Acceptance Criteria**:
1. Course ID format: `CRS-YYYYMMDD-NNN`
2. Required fields: title, description, category, difficulty_level, instructor_id
3. Optional fields: thumbnail, prerequisites, estimated_duration
4. Initial status: `draft`

---

##### REQ-ELEARN-001-F002: Course Publication
**Category**: Course Management
**Priority**: P0 (Must Have)
**EARS Pattern**: State-driven

> **WHILE** a course is in `draft` status and has at least one published lesson, **THE** system **SHALL** allow the instructor to publish the course.

**Status Transitions**:
| From | To | Condition |
|------|-----|-----------|
| `draft` | `published` | At least 1 lesson exists |
| `published` | `archived` | No active enrollments or instructor decision |
| `archived` | `published` | Instructor reactivation |

**Status Values**:
- `draft`: 下書き（編集可能、非公開）
- `published`: 公開中（受講受付中）
- `archived`: アーカイブ済み（新規受講停止、既存受講者は継続可能）

---

##### REQ-ELEARN-001-F003: Course Search
**Category**: Course Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a user searches for courses, **THE** system **SHALL** return matching courses based on criteria including title, category, difficulty level, and instructor within 2 seconds.

**Search Criteria**:
- Title keyword
- Category (programming, business, design, language, etc.)
- Difficulty level (beginner, intermediate, advanced)
- Instructor name
- Price range

---

#### 3.2 Lesson Management Requirements

##### REQ-ELEARN-001-F010: Lesson Creation
**Category**: Lesson Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** an instructor adds a lesson to a course, **THE** system **SHALL** store lesson details including title, content type, content, and order with a unique lesson ID.

**Lesson ID Format**: `LES-YYYYMMDD-NNN`

**Content Types**:
- `video`: 動画コンテンツ
- `text`: テキストコンテンツ
- `quiz`: クイズ

---

##### REQ-ELEARN-001-F011: Lesson Ordering
**Category**: Lesson Management
**Priority**: P1 (Should Have)
**EARS Pattern**: Event-driven

> **WHEN** an instructor reorders lessons, **THE** system **SHALL** update the order of all affected lessons while maintaining sequential numbering.

---

#### 3.3 Learner Management Requirements

##### REQ-ELEARN-001-F020: Learner Registration
**Category**: Learner Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a new learner registers, **THE** system **SHALL** store learner information including name, email, and preferences with a unique learner ID.

**Learner ID Format**: `LRN-YYYYMMDD-NNN`

**Required Fields**:
- Name (display name)
- Email (unique)
- Password (hashed)

**Optional Fields**:
- Profile picture
- Bio
- Learning interests

---

##### REQ-ELEARN-001-F021: Course Enrollment
**Category**: Learner Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a learner enrolls in a course, **THE** system **SHALL** create an enrollment record linking the learner to the course with enrollment date and initial progress of 0%.

**Enrollment ID Format**: `ENR-YYYYMMDD-NNN`

---

#### 3.4 Progress Tracking Requirements

##### REQ-ELEARN-001-F030: Lesson Completion Tracking
**Category**: Progress Tracking
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a learner completes a lesson, **THE** system **SHALL** record the completion and update the overall course progress percentage.

**Progress Calculation**:
- Progress % = (Completed Lessons / Total Lessons) × 100

---

##### REQ-ELEARN-001-F031: Progress Persistence
**Category**: Progress Tracking
**Priority**: P0 (Must Have)
**EARS Pattern**: Ubiquitous

> **THE** system **SHALL** persist learning progress so that learners can resume from where they left off.

---

##### REQ-ELEARN-001-F032: Course Completion
**Category**: Progress Tracking
**Priority**: P0 (Must Have)
**EARS Pattern**: State-driven

> **WHILE** a learner's progress reaches 100%, **THE** system **SHALL** mark the enrollment as completed and enable certificate generation.

---

#### 3.5 Quiz Management Requirements

##### REQ-ELEARN-001-F040: Quiz Creation
**Category**: Quiz Management
**Priority**: P1 (Should Have)
**EARS Pattern**: Event-driven

> **WHEN** an instructor creates a quiz, **THE** system **SHALL** store quiz details including questions, options, correct answers, passing score, and time limit.

**Quiz ID Format**: `QIZ-YYYYMMDD-NNN`

**Question Types**:
- `single-choice`: 単一選択
- `multiple-choice`: 複数選択
- `true-false`: 真偽

**Quiz Settings**:
- `passing_score`: 合格点（0-100%）
- `time_limit_minutes`: 制限時間（分）、null = 無制限
- `max_attempts`: 最大試行回数（null = 無制限）

---

##### REQ-ELEARN-001-F041: Quiz Attempt
**Category**: Quiz Management
**Priority**: P1 (Should Have)
**EARS Pattern**: Event-driven

> **WHEN** a learner submits a quiz, **THE** system **SHALL** calculate the score, determine pass/fail, and record the attempt.

**Attempt ID Format**: `ATT-YYYYMMDD-NNN`

---

##### REQ-ELEARN-001-F042: Quiz Retry
**Category**: Quiz Management
**Priority**: P1 (Should Have)
**EARS Pattern**: Optional

> **IF** the quiz allows retries, **THEN THE** system **SHALL** allow the learner to reattempt the quiz up to the maximum allowed attempts.

---

#### 3.6 Certificate Management Requirements

##### REQ-ELEARN-001-F050: Certificate Generation
**Category**: Certificate Management
**Priority**: P1 (Should Have)
**EARS Pattern**: State-driven

> **WHILE** an enrollment is in `completed` status, **THE** system **SHALL** allow the learner to generate a completion certificate.

**Certificate ID Format**: `CERT-YYYYMMDD-NNN`

**Certificate Content**:
- Learner name
- Course title
- Completion date
- Instructor name
- Certificate ID (for verification)

---

#### 3.7 Error Handling Requirements

##### REQ-ELEARN-001-F060: Duplicate Enrollment Prevention
**Category**: Error Handling
**Priority**: P0 (Must Have)
**EARS Pattern**: Unwanted

> **THE** system **SHALL NOT** allow a learner to enroll in the same course twice.

---

##### REQ-ELEARN-001-F061: Invalid Progress Prevention
**Category**: Error Handling
**Priority**: P0 (Must Have)
**EARS Pattern**: Unwanted

> **THE** system **SHALL NOT** allow progress to exceed 100% or fall below 0%.

---

### 4. Non-Functional Requirements

#### 4.1 Performance
- Course search response time: < 2 seconds
- Lesson content load time: < 3 seconds
- Quiz submission processing: < 1 second

#### 4.2 Scalability
- Support up to 10,000 concurrent learners
- Support up to 1,000 courses

#### 4.3 Security
- Password hashing (bcrypt)
- Session management
- Role-based access control

---

### 5. Traceability Matrix

| Requirement ID | Design | Task | Test |
|---------------|--------|------|------|
| REQ-ELEARN-001-F001 | DES-4.1.1 | TSK-004 | TEST-001 |
| REQ-ELEARN-001-F002 | DES-4.1.1 | TSK-004 | TEST-002 |
| REQ-ELEARN-001-F003 | DES-4.3.1 | TSK-010 | TEST-003 |
| REQ-ELEARN-001-F010 | DES-4.1.2 | TSK-005 | TEST-010 |
| REQ-ELEARN-001-F011 | DES-4.1.2 | TSK-005 | TEST-011 |
| REQ-ELEARN-001-F020 | DES-4.1.3 | TSK-006 | TEST-020 |
| REQ-ELEARN-001-F021 | DES-4.1.4 | TSK-007 | TEST-021 |
| REQ-ELEARN-001-F030 | DES-4.1.5 | TSK-008 | TEST-030 |
| REQ-ELEARN-001-F031 | DES-4.1.5 | TSK-008 | TEST-031 |
| REQ-ELEARN-001-F032 | DES-4.1.5 | TSK-008 | TEST-032 |
| REQ-ELEARN-001-F040 | DES-4.1.6 | TSK-009 | TEST-040 |
| REQ-ELEARN-001-F041 | DES-4.1.6 | TSK-009 | TEST-041 |
| REQ-ELEARN-001-F042 | DES-4.1.6 | TSK-009 | TEST-042 |
| REQ-ELEARN-001-F050 | DES-4.1.7 | TSK-011 | TEST-050 |
| REQ-ELEARN-001-F060 | DES-4.3.2 | TSK-007 | TEST-060 |
| REQ-ELEARN-001-F061 | DES-4.1.5 | TSK-008 | TEST-061 |

---

### 6. Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2026-01-04 | MUSUBIX SDD | Initial draft |
| 1.1.0 | 2026-01-04 | MUSUBIX SDD | Added F000 (Instructor), clarified status transitions, added quiz time limits |
