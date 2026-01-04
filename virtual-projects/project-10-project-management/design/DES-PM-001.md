# プロジェクト管理ツール設計書

## Document Information
- **Document ID**: DES-PM-001
- **Version**: 1.0.0
- **Status**: Draft
- **Created**: 2026-01-04
- **Requirements Reference**: REQ-PM-001

---

## 1. C4 Model - Level 1: System Context

### 1.1 System Context Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                      External Actors                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                   │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────┐     │
│  │   Project    │     │    Team      │     │    Admin     │     │
│  │    Owner     │     │   Member     │     │              │     │
│  └──────┬───────┘     └──────┬───────┘     └──────┬───────┘     │
│         │                    │                    │              │
│         │  プロジェクト管理  │  タスク作業        │  システム管理│
│         │                    │                    │              │
│         └────────────────────┼────────────────────┘              │
│                              │                                   │
│                              ▼                                   │
│              ┌───────────────────────────────┐                   │
│              │   Project Management          │                   │
│              │        Tool                   │                   │
│              │                               │                   │
│              │  - プロジェクト管理           │                   │
│              │  - タスク管理（カンバン）     │                   │
│              │  - メンバー管理               │                   │
│              │  - マイルストーン管理         │                   │
│              │  - 進捗レポート               │                   │
│              └───────────────────────────────┘                   │
│                                                                   │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 Actor Definitions

| Actor | Role | Primary Use Cases |
|-------|------|-------------------|
| Project Owner | プロジェクト所有者 | プロジェクト作成、設定変更、メンバー管理、レポート閲覧 |
| Team Member | チームメンバー | タスク作成・更新、進捗報告、マイルストーン確認 |
| Admin | システム管理者 | ユーザー管理、システム設定、全プロジェクト監視 |

---

## 2. C4 Model - Level 2: Container Diagram

### 2.1 Container Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                   Project Management Tool                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                   │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                    CLI Application                        │    │
│  │                    [TypeScript/Node.js]                   │    │
│  │                                                           │    │
│  │  Entry point for project and task management              │    │
│  └─────────────────────────────┬─────────────────────────────┘    │
│                                │                                  │
│                                ▼                                  │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                    Core Library                          │    │
│  │                    [TypeScript]                          │    │
│  │                                                           │    │
│  │  ┌───────────┐ ┌───────────┐ ┌───────────┐ ┌──────────┐ │    │
│  │  │  Project  │ │   Task    │ │  Member   │ │Milestone │ │    │
│  │  │  Module   │ │  Module   │ │  Module   │ │  Module  │ │    │
│  │  └───────────┘ └───────────┘ └───────────┘ └──────────┘ │    │
│  │  ┌───────────┐ ┌───────────┐ ┌───────────┐             │    │
│  │  │  Report   │ │   Auth    │ │   Audit   │             │    │
│  │  │  Module   │ │  Module   │ │  Module   │             │    │
│  │  └───────────┘ └───────────┘ └───────────┘             │    │
│  └─────────────────────────────┬─────────────────────────────┘    │
│                                │                                  │
│                                ▼                                  │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                    Data Store                            │    │
│  │                    [JSON Files / SQLite]                 │    │
│  │                                                           │    │
│  │  projects.json | tasks.json | members.json | users.json  │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                                                   │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 Container Specifications

| Container | Technology | Responsibility | Requirements Trace |
|-----------|------------|----------------|-------------------|
| CLI Application | TypeScript/Node.js | ユーザーインターフェース、コマンド処理 | REQ-PM-PRJ-*, REQ-PM-TSK-* |
| Core Library | TypeScript | ビジネスロジック、バリデーション | All REQ-PM-* |
| Data Store | JSON/SQLite | データ永続化、クエリ処理 | NFR-PM-DATA-* |

---

## 3. C4 Model - Level 3: Component Diagram

### 3.1 Core Library Components

```
┌─────────────────────────────────────────────────────────────────┐
│                        Core Library                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                   │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                    Domain Layer                          │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌─────────────┐  │    │
│  │  │    Project    │  │     Task      │  │  Subtask    │  │    │
│  │  │    Entity     │  │    Entity     │  │   Entity    │  │    │
│  │  └───────────────┘  └───────────────┘  └─────────────┘  │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌─────────────┐  │    │
│  │  │   Milestone   │  │    Member     │  │    User     │  │    │
│  │  │    Entity     │  │    Entity     │  │   Entity    │  │    │
│  │  └───────────────┘  └───────────────┘  └─────────────┘  │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌─────────────┐  │    │
│  │  │ProjectStatus  │  │  TaskStatus   │  │  Priority   │  │    │
│  │  │ Value Object  │  │ Value Object  │  │Value Object │  │    │
│  │  └───────────────┘  └───────────────┘  └─────────────┘  │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                │                                  │
│                                ▼                                  │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                   Service Layer                          │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌─────────────┐  │    │
│  │  │   Project     │  │    Task       │  │  Milestone  │  │    │
│  │  │   Service     │  │   Service     │  │  Service    │  │    │
│  │  │               │  │               │  │             │  │    │
│  │  │ REQ-PM-PRJ-*  │  │ REQ-PM-TSK-*  │  │REQ-PM-MIL-* │  │    │
│  │  └───────────────┘  └───────────────┘  └─────────────┘  │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌─────────────┐  │    │
│  │  │   Member      │  │    Report     │  │    Auth     │  │    │
│  │  │   Service     │  │   Service     │  │  Service    │  │    │
│  │  │               │  │               │  │             │  │    │
│  │  │ REQ-PM-MEM-*  │  │ REQ-PM-REP-*  │  │REQ-PM-AUTH-*│  │    │
│  │  └───────────────┘  └───────────────┘  └─────────────┘  │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                │                                  │
│                                ▼                                  │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                 Repository Layer                         │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌─────────────┐  │    │
│  │  │   Project     │  │    Task       │  │  Milestone  │  │    │
│  │  │  Repository   │  │  Repository   │  │ Repository  │  │    │
│  │  └───────────────┘  └───────────────┘  └─────────────┘  │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌─────────────┐  │    │
│  │  │   Member      │  │     User      │  │   Audit     │  │    │
│  │  │  Repository   │  │  Repository   │  │ Repository  │  │    │
│  │  └───────────────┘  └───────────────┘  └─────────────┘  │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                                                   │
└─────────────────────────────────────────────────────────────────┘
```

### 3.2 Component Specifications

#### 3.2.1 Domain Entities

| Entity | Attributes | Methods | Requirements |
|--------|------------|---------|--------------|
| Project | id, name, description, startDate, endDate, status, ownerId, isArchived, createdAt, updatedAt | updateStatus(), archive(), restore() | REQ-PM-PRJ-* |
| Task | id, projectId, title, description, status, priority, assigneeId, dueDate, milestoneId, version, createdAt, updatedAt | updateStatus(), assign(), isOverdue() | REQ-PM-TSK-* |
| Subtask | id, parentTaskId, title, status, createdAt | complete() | REQ-PM-TSK-005 |
| Milestone | id, projectId, name, description, targetDate, createdAt | getProgress() | REQ-PM-MIL-* |
| Member | id, projectId, userId, role, joinedAt | changeRole() | REQ-PM-MEM-* |
| User | id, username, email, passwordHash, isLocked, createdAt | authenticate(), lock() | REQ-PM-AUTH-* |

#### 3.2.2 Value Objects

| Value Object | Allowed Values | Validation |
|-------------|----------------|------------|
| ProjectStatus | planning, active, on-hold, completed, cancelled | Enum |
| TaskStatus | backlog, todo, in-progress, review, done | Enum |
| Priority | high, medium, low | Enum |
| ProjectRole | owner, admin, member, viewer | Enum |

#### 3.2.3 Services

| Service | Responsibilities | Dependencies | Requirements |
|---------|-----------------|--------------|--------------|
| ProjectService | プロジェクトCRUD、ステータス管理、アーカイブ | ProjectRepository, MemberRepository | REQ-PM-PRJ-* |
| TaskService | タスクCRUD、ステータス遷移、割り当て、検索 | TaskRepository, MemberRepository | REQ-PM-TSK-* |
| MilestoneService | マイルストーンCRUD、進捗計算 | MilestoneRepository, TaskRepository | REQ-PM-MIL-* |
| MemberService | メンバー招待、役割変更、削除 | MemberRepository, TaskRepository | REQ-PM-MEM-* |
| ReportService | サマリー生成、バーンダウンデータ、メンバーレポート | All Repositories | REQ-PM-REP-* |
| AuthService | 認証、認可、セッション管理 | UserRepository, MemberRepository | REQ-PM-AUTH-* |
| AuditService | 監査ログ記録 | AuditRepository | NFR-PM-DATA-002 |

#### 3.2.4 Repositories

| Repository | Interface Methods | Storage |
|------------|-------------------|---------|
| ProjectRepository | findById, findByOwnerId, findAccessible, save, delete | projects.json |
| TaskRepository | findById, findByProjectId, findByAssignee, findOverdue, save, delete | tasks.json |
| MilestoneRepository | findById, findByProjectId, save, delete | milestones.json |
| MemberRepository | findByProjectId, findByUserId, save, delete | members.json |
| UserRepository | findById, findByUsername, save | users.json |
| AuditRepository | log, findByDateRange | audit.json |

---

## 4. Design Patterns Applied

### 4.1 Pattern Usage

| Pattern | Applied To | Justification | Constitution Article |
|---------|-----------|---------------|---------------------|
| Repository | All data access | データアクセスの抽象化、テスト容易性 | VII |
| Service Layer | Business logic | ドメインロジックの分離 | VII |
| Value Object | Status, Priority, Role | 型安全性と列挙の明確化 | VII |
| Optimistic Locking | Task updates | 同時編集の競合検出（REQ-PM-TSK-007） | VII |
| Factory | Entity creation | 複雑な生成ロジックのカプセル化 | VII |

### 4.2 Status Transition Map (BP-DESIGN-001)

```typescript
// Project Status Transitions
const projectStatusTransitions: Record<ProjectStatus, ProjectStatus[]> = {
  planning: ['active'],
  active: ['on-hold', 'completed', 'cancelled'],
  'on-hold': ['active', 'cancelled'],
  completed: [], // Terminal (archivable)
  cancelled: [], // Terminal (archivable)
};

// Task Status Transitions (Kanban Flow)
const taskStatusTransitions: Record<TaskStatus, TaskStatus[]> = {
  backlog: ['todo'],
  todo: ['in-progress', 'backlog'],
  'in-progress': ['review', 'todo'],
  review: ['done', 'in-progress'],
  done: ['in-progress'], // Reopen
};
```

---

## 5. Interface Definitions

### 5.1 Entity Interfaces (BP-CODE-001: Entity Input DTO)

```typescript
// Project Entity
interface CreateProjectInput {
  name: string;
  description?: string;
  startDate: Date;
  endDate?: Date;
  ownerId: string;
}

interface Project {
  id: string; // PRJ-YYYYMMDD-NNN
  name: string;
  description: string;
  startDate: Date;
  endDate: Date | null;
  status: ProjectStatus;
  ownerId: string;
  isArchived: boolean;
  createdAt: Date;
  updatedAt: Date;
}

// Task Entity
interface CreateTaskInput {
  projectId: string;
  title: string;
  description?: string;
  priority: Priority;
  assigneeId?: string;
  dueDate?: Date;
  milestoneId?: string;
}

interface Task {
  id: string; // TSK-YYYYMMDD-NNN
  projectId: string;
  title: string;
  description: string;
  status: TaskStatus;
  priority: Priority;
  assigneeId: string | null;
  dueDate: Date | null;
  milestoneId: string | null;
  version: number; // Optimistic locking
  createdAt: Date;
  updatedAt: Date;
}

// Subtask Entity
interface CreateSubtaskInput {
  parentTaskId: string;
  title: string;
}

interface Subtask {
  id: string; // SUB-YYYYMMDD-NNN
  parentTaskId: string;
  title: string;
  status: 'pending' | 'done';
  createdAt: Date;
}

// Milestone Entity
interface CreateMilestoneInput {
  projectId: string;
  name: string;
  description?: string;
  targetDate: Date;
}

interface Milestone {
  id: string; // MIL-YYYYMMDD-NNN
  projectId: string;
  name: string;
  description: string;
  targetDate: Date;
  createdAt: Date;
}

// Member Entity
interface AddMemberInput {
  projectId: string;
  userId: string;
  role: ProjectRole;
}

interface Member {
  id: string; // MEM-YYYYMMDD-NNN
  projectId: string;
  userId: string;
  role: ProjectRole;
  joinedAt: Date;
}
```

### 5.2 Service Interfaces

```typescript
interface IProjectService {
  createProject(input: CreateProjectInput): Promise<Project>;
  findById(id: string): Promise<Project | null>;
  findAccessibleProjects(userId: string): Promise<Project[]>;
  updateStatus(id: string, newStatus: ProjectStatus): Promise<Project>;
  archiveProject(id: string): Promise<void>;
  restoreProject(id: string): Promise<Project>;
}

interface ITaskService {
  createTask(input: CreateTaskInput): Promise<Task>;
  findById(id: string): Promise<Task | null>;
  findByProject(projectId: string, filters?: TaskFilters): Promise<Task[]>;
  updateStatus(id: string, newStatus: TaskStatus, version: number): Promise<Task>;
  assignTask(id: string, assigneeId: string | null, version: number): Promise<Task>;
  findOverdueTasks(projectId: string): Promise<Task[]>;
}

interface IMilestoneService {
  createMilestone(input: CreateMilestoneInput): Promise<Milestone>;
  findById(id: string): Promise<Milestone | null>;
  findByProject(projectId: string): Promise<Milestone[]>;
  getProgress(id: string): Promise<MilestoneProgress>;
  getAtRiskMilestones(projectId: string): Promise<MilestoneWithWarning[]>;
}

interface IMemberService {
  addMember(input: AddMemberInput): Promise<Member>;
  findByProject(projectId: string): Promise<Member[]>;
  changeRole(memberId: string, newRole: ProjectRole): Promise<Member>;
  removeMember(memberId: string): Promise<void>;
}

interface IReportService {
  generateProjectSummary(projectId: string): Promise<ProjectSummary>;
  getBurndownData(projectId: string, startDate: Date, endDate: Date): Promise<BurndownData>;
  getMemberTaskReport(projectId: string): Promise<MemberTaskReport[]>;
}
```

### 5.3 Repository Interfaces (BP-DESIGN-002: Repository Async Pattern)

```typescript
interface IProjectRepository {
  findById(id: string): Promise<Project | null>;
  findByOwnerId(ownerId: string): Promise<Project[]>;
  findAccessible(userId: string): Promise<Project[]>;
  findAll(): Promise<Project[]>;
  save(project: Project): Promise<Project>;
  delete(id: string): Promise<void>;
}

interface ITaskRepository {
  findById(id: string): Promise<Task | null>;
  findByProjectId(projectId: string): Promise<Task[]>;
  findByAssigneeId(assigneeId: string): Promise<Task[]>;
  findByMilestoneId(milestoneId: string): Promise<Task[]>;
  findOverdue(projectId: string): Promise<Task[]>;
  save(task: Task): Promise<Task>;
  delete(id: string): Promise<void>;
}

interface IMilestoneRepository {
  findById(id: string): Promise<Milestone | null>;
  findByProjectId(projectId: string): Promise<Milestone[]>;
  save(milestone: Milestone): Promise<Milestone>;
  delete(id: string): Promise<void>;
}

interface IMemberRepository {
  findById(id: string): Promise<Member | null>;
  findByProjectId(projectId: string): Promise<Member[]>;
  findByUserId(userId: string): Promise<Member[]>;
  findByProjectAndUser(projectId: string, userId: string): Promise<Member | null>;
  save(member: Member): Promise<Member>;
  delete(id: string): Promise<void>;
}
```

---

## 6. Data Model

### 6.1 JSON Schema

```json
{
  "projects": {
    "type": "array",
    "items": {
      "type": "object",
      "properties": {
        "id": { "type": "string", "pattern": "^PRJ-\\d{8}-\\d{3}$" },
        "name": { "type": "string", "minLength": 1, "maxLength": 100 },
        "status": { "enum": ["planning", "active", "on-hold", "completed", "cancelled"] },
        "isArchived": { "type": "boolean" }
      },
      "required": ["id", "name", "status", "startDate", "ownerId"]
    }
  },
  "tasks": {
    "type": "array",
    "items": {
      "type": "object",
      "properties": {
        "id": { "type": "string", "pattern": "^TSK-\\d{8}-\\d{3}$" },
        "title": { "type": "string", "minLength": 1, "maxLength": 200 },
        "status": { "enum": ["backlog", "todo", "in-progress", "review", "done"] },
        "priority": { "enum": ["high", "medium", "low"] },
        "version": { "type": "integer", "minimum": 1 }
      },
      "required": ["id", "projectId", "title", "status", "priority", "version"]
    }
  }
}
```

### 6.2 ID Format (BP-CODE-002: Date-based ID Format)

| Entity | Format | Example |
|--------|--------|---------|
| Project | PRJ-YYYYMMDD-NNN | PRJ-20260104-001 |
| Task | TSK-YYYYMMDD-NNN | TSK-20260104-001 |
| Subtask | SUB-YYYYMMDD-NNN | SUB-20260104-001 |
| Milestone | MIL-YYYYMMDD-NNN | MIL-20260104-001 |
| Member | MEM-YYYYMMDD-NNN | MEM-20260104-001 |
| User | USR-YYYYMMDD-NNN | USR-20260104-001 |

---

## 7. Error Handling

### 7.1 Error Types

```typescript
class ProjectManagementError extends Error {
  constructor(
    public code: string,
    message: string,
    public details?: Record<string, unknown>
  ) {
    super(message);
    this.name = 'ProjectManagementError';
  }
}

// Error Codes
const ErrorCodes = {
  // Project errors
  PROJECT_NOT_FOUND: 'PM-001',
  INVALID_PROJECT_STATUS_TRANSITION: 'PM-002',
  PROJECT_ARCHIVED: 'PM-003',
  PROJECT_COMPLETED: 'PM-004',
  
  // Task errors
  TASK_NOT_FOUND: 'PM-101',
  INVALID_TASK_STATUS_TRANSITION: 'PM-102',
  TASK_CONCURRENT_UPDATE: 'PM-103',
  TASK_INVALID_ASSIGNEE: 'PM-104',
  
  // Member errors
  MEMBER_NOT_FOUND: 'PM-201',
  CANNOT_REMOVE_SOLE_OWNER: 'PM-202',
  INSUFFICIENT_PERMISSIONS: 'PM-203',
  
  // Milestone errors
  MILESTONE_NOT_FOUND: 'PM-301',
  
  // Auth errors
  UNAUTHORIZED: 'AUTH-001',
  FORBIDDEN: 'AUTH-002',
  ACCOUNT_LOCKED: 'AUTH-003',
} as const;
```

---

## 8. Traceability Matrix

| Design Component | Requirements | Priority |
|-----------------|--------------|----------|
| ProjectService | REQ-PM-PRJ-001~006 | P0~P2 |
| TaskService | REQ-PM-TSK-001~007 | P0~P2 |
| MilestoneService | REQ-PM-MIL-001~004 | P1~P2 |
| MemberService | REQ-PM-MEM-001~004 | P0~P1 |
| ReportService | REQ-PM-REP-001~003 | P1~P2 |
| AuthService | REQ-PM-AUTH-001~003 | P0 |
| Project Entity | REQ-PM-PRJ-001, PRJ-003 | P0 |
| Task Entity | REQ-PM-TSK-001, TSK-002, TSK-007 | P0 |
| Milestone Entity | REQ-PM-MIL-001 | P1 |
| Member Entity | REQ-PM-MEM-001 | P0 |

---

## 9. ADR (Architecture Decision Records)

### ADR-PM-001: Optimistic Locking for Tasks

**Context**: タスクの同時編集による競合を防止する必要がある（REQ-PM-TSK-007）

**Decision**: バージョン番号による楽観的ロックを実装

**Rationale**:
- パフォーマンスへの影響が最小限
- 競合は稀であり、発生時に対処すれば十分
- 悲観的ロックはCLIツールには過剰

**Consequences**:
- (+) 通常操作時のオーバーヘッドなし
- (+) 実装がシンプル
- (-) 競合時はユーザーが再操作必要

### ADR-PM-002: JSON File Storage

**Context**: データ永続化方式の選択

**Decision**: 初期バージョンではJSONファイルを使用

**Rationale**:
- Project-09 (Inventory)と同様の理由
- 将来のDB移行に備えてRepository Patternを採用

### ADR-PM-003: Kanban Status Flow

**Context**: タスクステータスの遷移ルールを定義

**Decision**: 5カラムカンバン（backlog → todo → in-progress → review → done）

**Rationale**:
- 一般的なアジャイル開発フローをカバー
- 柔軟性と構造のバランス
- レビュープロセスを明示的に含む

**Consequences**:
- (+) 標準的なワークフロー
- (+) 進捗の可視化が容易
- (-) シンプルなプロジェクトには過剰な場合あり
