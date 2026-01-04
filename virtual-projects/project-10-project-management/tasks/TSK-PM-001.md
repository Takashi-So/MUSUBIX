# Project-10 タスク分解書

## Document Information
- **Document ID**: TSK-PM-001
- **Version**: 1.0.0
- **Status**: Ready for Implementation
- **Created**: 2026-01-04
- **Design Reference**: DES-PM-001
- **Requirements Reference**: REQ-PM-001

---

## タスク概要

| カテゴリ | タスク数 | 見積時間 |
|---------|---------|---------|
| Domain Layer | 8 | 5h |
| Repository Layer | 6 | 4h |
| Service Layer | 7 | 8h |
| CLI Layer | 10 | 5h |
| Testing | 5 | 5h |
| **Total** | **36** | **27h** |

---

## Phase 1: Domain Layer (Foundation)

### TSK-PM-001: Value Objects実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: All  
**Design**: DES-PM-001 Section 3.2.2

**Description**:
ProjectStatus, TaskStatus, Priority, ProjectRole の Value Object を実装する。

**Acceptance Criteria**:
- [ ] ProjectStatus enum (5 values)
- [ ] TaskStatus enum (5 values)
- [ ] Priority enum (3 values)
- [ ] ProjectRole enum (4 values)
- [ ] ステータス遷移バリデーション関数

**Files**:
- `src/domain/value-objects/project-status.ts`
- `src/domain/value-objects/task-status.ts`
- `src/domain/value-objects/priority.ts`
- `src/domain/value-objects/project-role.ts`
- `src/domain/value-objects/index.ts`

---

### TSK-PM-002: Project Entity実装
**Priority**: P0  
**Estimate**: 45min  
**Requirements**: REQ-PM-PRJ-001, PRJ-003, PRJ-004, PRJ-005  
**Design**: DES-PM-001 Section 3.2.1

**Description**:
Project エンティティを実装する。Input DTOパターン（BP-CODE-001）を適用。

**Acceptance Criteria**:
- [ ] CreateProjectInput DTOを使用
- [ ] Date-based ID Format (PRJ-YYYYMMDD-NNN)
- [ ] ステータス遷移バリデーション (BP-DESIGN-001)
- [ ] archive(), restore() メソッド
- [ ] 完了/キャンセル状態での変更防止

**Files**:
- `src/domain/entities/project.ts`

---

### TSK-PM-003: Task Entity実装
**Priority**: P0  
**Estimate**: 1h  
**Requirements**: REQ-PM-TSK-001, TSK-002, TSK-006, TSK-007  
**Design**: DES-PM-001 Section 3.2.1

**Description**:
Task エンティティを実装する。楽観的ロック対応。

**Acceptance Criteria**:
- [ ] CreateTaskInput DTOを使用
- [ ] Date-based ID Format (TSK-YYYYMMDD-NNN)
- [ ] カンバンステータス遷移バリデーション
- [ ] version フィールド（楽観的ロック）
- [ ] isOverdue() メソッド
- [ ] assign() メソッド

**Files**:
- `src/domain/entities/task.ts`

---

### TSK-PM-004: Subtask Entity実装
**Priority**: P2  
**Estimate**: 30min  
**Requirements**: REQ-PM-TSK-005  
**Design**: DES-PM-001 Section 3.2.1

**Description**:
Subtask エンティティを実装する。

**Acceptance Criteria**:
- [ ] CreateSubtaskInput DTOを使用
- [ ] Date-based ID Format (SUB-YYYYMMDD-NNN)
- [ ] 'pending' | 'done' ステータス
- [ ] complete() メソッド

**Files**:
- `src/domain/entities/subtask.ts`

---

### TSK-PM-005: Milestone Entity実装
**Priority**: P1  
**Estimate**: 30min  
**Requirements**: REQ-PM-MIL-001  
**Design**: DES-PM-001 Section 3.2.1

**Description**:
Milestone エンティティを実装する。

**Acceptance Criteria**:
- [ ] CreateMilestoneInput DTOを使用
- [ ] Date-based ID Format (MIL-YYYYMMDD-NNN)
- [ ] targetDate バリデーション

**Files**:
- `src/domain/entities/milestone.ts`

---

### TSK-PM-006: Member Entity実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-PM-MEM-001, MEM-002  
**Design**: DES-PM-001 Section 3.2.1

**Description**:
Member エンティティを実装する。

**Acceptance Criteria**:
- [ ] AddMemberInput DTOを使用
- [ ] Date-based ID Format (MEM-YYYYMMDD-NNN)
- [ ] changeRole() メソッド
- [ ] 役割変更権限チェック

**Files**:
- `src/domain/entities/member.ts`

---

### TSK-PM-007: User Entity実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-PM-AUTH-001  
**Design**: DES-PM-001 Section 3.2.1

**Description**:
User エンティティを実装する。

**Acceptance Criteria**:
- [ ] パスワードハッシュ化
- [ ] authenticate() メソッド
- [ ] lock() メソッド

**Files**:
- `src/domain/entities/user.ts`

---

### TSK-PM-008: Error Types定義
**Priority**: P0  
**Estimate**: 20min  
**Requirements**: All  
**Design**: DES-PM-001 Section 7

**Description**:
カスタムエラークラスとエラーコードを定義する。

**Acceptance Criteria**:
- [ ] ProjectManagementError基底クラス
- [ ] エラーコード定数（PM-*, AUTH-*）
- [ ] ConcurrentUpdateError（楽観的ロック用）

**Files**:
- `src/domain/errors/project-management-error.ts`
- `src/domain/errors/error-codes.ts`

---

## Phase 2: Repository Layer

### TSK-PM-009: Repository Interface定義
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: NFR-PM-DATA-001  
**Design**: DES-PM-001 Section 5.3

**Description**:
全Repositoryのインターフェースを定義する（BP-DESIGN-002: Async Pattern）。

**Acceptance Criteria**:
- [ ] 全メソッドがPromiseを返す
- [ ] CRUD操作の標準化
- [ ] フィルタ・検索条件の型定義

**Files**:
- `src/repositories/interfaces.ts`

---

### TSK-PM-010: ProjectRepository実装
**Priority**: P0  
**Estimate**: 45min  
**Requirements**: REQ-PM-PRJ-002  
**Design**: DES-PM-001 Section 3.2.4

**Description**:
JSONファイルベースのProjectRepositoryを実装する。

**Acceptance Criteria**:
- [ ] findById, findByOwnerId
- [ ] findAccessible（メンバーシップベース）
- [ ] save, delete
- [ ] アーカイブフィルタ

**Files**:
- `src/repositories/project-repository.ts`

---

### TSK-PM-011: TaskRepository実装
**Priority**: P0  
**Estimate**: 45min  
**Requirements**: REQ-PM-TSK-004, TSK-006  
**Design**: DES-PM-001 Section 3.2.4

**Description**:
JSONファイルベースのTaskRepositoryを実装する。

**Acceptance Criteria**:
- [ ] findById, findByProjectId
- [ ] findByAssigneeId, findByMilestoneId
- [ ] findOverdue（期限超過検索）
- [ ] save, delete
- [ ] 楽観的ロックチェック

**Files**:
- `src/repositories/task-repository.ts`

---

### TSK-PM-012: MilestoneRepository実装
**Priority**: P1  
**Estimate**: 30min  
**Requirements**: REQ-PM-MIL-002  
**Design**: DES-PM-001 Section 3.2.4

**Description**:
JSONファイルベースのMilestoneRepositoryを実装する。

**Acceptance Criteria**:
- [ ] findById, findByProjectId
- [ ] save, delete

**Files**:
- `src/repositories/milestone-repository.ts`

---

### TSK-PM-013: MemberRepository実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-PM-MEM-001  
**Design**: DES-PM-001 Section 3.2.4

**Description**:
JSONファイルベースのMemberRepositoryを実装する。

**Acceptance Criteria**:
- [ ] findById, findByProjectId, findByUserId
- [ ] findByProjectAndUser
- [ ] save, delete

**Files**:
- `src/repositories/member-repository.ts`

---

### TSK-PM-014: UserRepository & AuditRepository実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-PM-AUTH-001, NFR-PM-DATA-002  
**Design**: DES-PM-001 Section 3.2.4

**Description**:
UserRepositoryとAuditRepositoryを実装する。

**Acceptance Criteria**:
- [ ] findById, findByUsername
- [ ] 監査ログの追記専用保存
- [ ] 1年分のログ保持

**Files**:
- `src/repositories/user-repository.ts`
- `src/repositories/audit-repository.ts`

---

## Phase 3: Service Layer

### TSK-PM-015: ProjectService実装
**Priority**: P0  
**Estimate**: 1.5h  
**Requirements**: REQ-PM-PRJ-001~006  
**Design**: DES-PM-001 Section 3.2.3

**Description**:
プロジェクト管理のビジネスロジックを実装する（BP-DESIGN-003: Service Layer with DI）。

**Acceptance Criteria**:
- [ ] createProject - プロジェクト作成
- [ ] findById, findAccessibleProjects - 検索
- [ ] updateStatus - ステータス変更（遷移バリデーション）
- [ ] archiveProject - アーカイブ
- [ ] restoreProject - 復元

**Files**:
- `src/services/project-service.ts`

---

### TSK-PM-016: TaskService実装
**Priority**: P0  
**Estimate**: 1.5h  
**Requirements**: REQ-PM-TSK-001~007  
**Design**: DES-PM-001 Section 3.2.3

**Description**:
タスク管理のビジネスロジックを実装する。

**Acceptance Criteria**:
- [ ] createTask - タスク作成
- [ ] findById, findByProject - 検索（フィルタ付き）
- [ ] updateStatus - カンバン移動（楽観的ロック）
- [ ] assignTask - 担当者割り当て
- [ ] findOverdueTasks - 期限超過タスク検索
- [ ] 同時編集検出（version check）

**Files**:
- `src/services/task-service.ts`

---

### TSK-PM-017: SubtaskService実装
**Priority**: P2  
**Estimate**: 30min  
**Requirements**: REQ-PM-TSK-005  
**Design**: DES-PM-001 Section 3.2.3

**Description**:
サブタスク管理のビジネスロジックを実装する。

**Acceptance Criteria**:
- [ ] createSubtask - サブタスク作成
- [ ] findByParentTaskId - 親タスクから検索
- [ ] completeSubtask - 完了マーク
- [ ] 親タスク進捗計算

**Files**:
- `src/services/subtask-service.ts`

---

### TSK-PM-018: MilestoneService実装
**Priority**: P1  
**Estimate**: 1h  
**Requirements**: REQ-PM-MIL-001~004  
**Design**: DES-PM-001 Section 3.2.3

**Description**:
マイルストーン管理のビジネスロジックを実装する。

**Acceptance Criteria**:
- [ ] createMilestone - マイルストーン作成
- [ ] findById, findByProject - 検索
- [ ] getProgress - 進捗計算（関連タスクベース）
- [ ] getAtRiskMilestones - 遅延リスク検出

**Files**:
- `src/services/milestone-service.ts`

---

### TSK-PM-019: MemberService実装
**Priority**: P0  
**Estimate**: 1h  
**Requirements**: REQ-PM-MEM-001~004  
**Design**: DES-PM-001 Section 3.2.3

**Description**:
メンバー管理のビジネスロジックを実装する。

**Acceptance Criteria**:
- [ ] addMember - メンバー招待
- [ ] findByProject - プロジェクトメンバー一覧
- [ ] changeRole - 役割変更（権限チェック）
- [ ] removeMember - メンバー削除
- [ ] 唯一のowner削除防止

**Files**:
- `src/services/member-service.ts`

---

### TSK-PM-020: ReportService実装
**Priority**: P1  
**Estimate**: 1.5h  
**Requirements**: REQ-PM-REP-001~003  
**Design**: DES-PM-001 Section 3.2.3

**Description**:
レポート生成のビジネスロジックを実装する。

**Acceptance Criteria**:
- [ ] generateProjectSummary - プロジェクトサマリー
- [ ] getBurndownData - バーンダウンデータ
- [ ] getMemberTaskReport - メンバー別レポート
- [ ] CSV/JSONエクスポート

**Files**:
- `src/services/report-service.ts`

---

### TSK-PM-021: AuthService実装
**Priority**: P0  
**Estimate**: 1h  
**Requirements**: REQ-PM-AUTH-001~003  
**Design**: DES-PM-001 Section 3.2.3

**Description**:
認証・認可のビジネスロジックを実装する。

**Acceptance Criteria**:
- [ ] authenticate - ログイン認証
- [ ] checkProjectAccess - プロジェクトアクセス権確認
- [ ] checkPermission - 操作権限確認
- [ ] セッションタイムアウト（1時間）

**Files**:
- `src/services/auth-service.ts`

---

## Phase 4: CLI Layer

### TSK-PM-022: CLI基盤実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: All  
**Design**: DES-PM-001 Section 2.1

**Description**:
CLI基盤（Commander.js）をセットアップする。

**Acceptance Criteria**:
- [ ] コマンドパーサー設定
- [ ] ヘルプ・バージョン表示
- [ ] グローバルオプション（--project, --format）

**Files**:
- `src/cli/index.ts`
- `src/cli/base.ts`

---

### TSK-PM-023: project コマンド実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-PM-PRJ-001~006  

**Subcommands**:
- `project create` - プロジェクト作成
- `project list` - 一覧表示
- `project show <id>` - 詳細表示
- `project status <id> <status>` - ステータス変更
- `project archive <id>` - アーカイブ
- `project restore <id>` - 復元

**Files**:
- `src/cli/commands/project.ts`

---

### TSK-PM-024: task コマンド実装
**Priority**: P0  
**Estimate**: 45min  
**Requirements**: REQ-PM-TSK-001~007  

**Subcommands**:
- `task create` - タスク作成
- `task list [--project <id>]` - 一覧表示
- `task show <id>` - 詳細表示
- `task move <id> <status>` - カンバン移動
- `task assign <id> <userId>` - 担当者割り当て
- `task overdue [--project <id>]` - 期限超過一覧

**Files**:
- `src/cli/commands/task.ts`

---

### TSK-PM-025: subtask コマンド実装
**Priority**: P2  
**Estimate**: 20min  
**Requirements**: REQ-PM-TSK-005  

**Subcommands**:
- `subtask add <taskId>` - サブタスク追加
- `subtask complete <id>` - 完了マーク
- `subtask list <taskId>` - 一覧表示

**Files**:
- `src/cli/commands/subtask.ts`

---

### TSK-PM-026: milestone コマンド実装
**Priority**: P1  
**Estimate**: 30min  
**Requirements**: REQ-PM-MIL-001~004  

**Subcommands**:
- `milestone create` - マイルストーン作成
- `milestone list [--project <id>]` - 一覧表示
- `milestone show <id>` - 詳細（進捗表示）
- `milestone at-risk [--project <id>]` - 遅延リスク一覧

**Files**:
- `src/cli/commands/milestone.ts`

---

### TSK-PM-027: member コマンド実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-PM-MEM-001~004  

**Subcommands**:
- `member add <projectId> <userId> <role>` - メンバー追加
- `member list <projectId>` - 一覧表示
- `member role <memberId> <role>` - 役割変更
- `member remove <memberId>` - メンバー削除

**Files**:
- `src/cli/commands/member.ts`

---

### TSK-PM-028: report コマンド実装
**Priority**: P1  
**Estimate**: 30min  
**Requirements**: REQ-PM-REP-001~003  

**Subcommands**:
- `report summary <projectId>` - プロジェクトサマリー
- `report burndown <projectId> [--from <date>] [--to <date>]` - バーンダウン
- `report members <projectId>` - メンバー別レポート

**Files**:
- `src/cli/commands/report.ts`

---

### TSK-PM-029: auth コマンド実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-PM-AUTH-001~003  

**Subcommands**:
- `auth login` - ログイン
- `auth logout` - ログアウト
- `auth whoami` - 現在ユーザー表示

**Files**:
- `src/cli/commands/auth.ts`

---

### TSK-PM-030: user コマンド実装
**Priority**: P1  
**Estimate**: 30min  
**Requirements**: REQ-PM-AUTH-001  

**Subcommands**:
- `user add` - ユーザー追加（Admin only）
- `user list` - ユーザー一覧
- `user lock <userId>` - アカウントロック
- `user unlock <userId>` - ロック解除

**Files**:
- `src/cli/commands/user.ts`

---

### TSK-PM-031: 出力フォーマッター実装
**Priority**: P1  
**Estimate**: 30min  
**Requirements**: REQ-PM-REP-*  

**Description**:
テーブル表示、JSON出力、カンバンビュー、進捗バーのフォーマッターを実装する。

**Files**:
- `src/cli/formatters/table.ts`
- `src/cli/formatters/kanban.ts`
- `src/cli/formatters/progress-bar.ts`

---

## Phase 5: Testing

### TSK-PM-032: Value Object & Entity テスト
**Priority**: P0  
**Estimate**: 45min  
**Requirements**: BP-TEST-001, BP-TEST-002  

**Test Cases**:
- ステータス遷移バリデーション
- Entity作成・更新
- 楽観的ロック動作

**Files**:
- `tests/unit/domain/value-objects.test.ts`
- `tests/unit/domain/entities.test.ts`

---

### TSK-PM-033: Service テスト
**Priority**: P0  
**Estimate**: 1.5h  
**Requirements**: BP-TEST-001, BP-TEST-002  

**Test Cases**:
- ProjectService: CRUD、ステータス遷移、アーカイブ
- TaskService: CRUD、カンバン移動、楽観的ロック競合
- MemberService: 招待、役割変更、削除制限

**Files**:
- `tests/unit/services/*.test.ts`

---

### TSK-PM-034: 権限テスト
**Priority**: P0  
**Estimate**: 45min  
**Requirements**: REQ-PM-AUTH-002, AUTH-003  

**Test Cases**:
- 役割別アクセス権限
- 非メンバーのアクセス拒否
- owner権限の保護

**Files**:
- `tests/unit/services/auth-service.test.ts`
- `tests/unit/services/member-service.test.ts`

---

### TSK-PM-035: 統合テスト
**Priority**: P1  
**Estimate**: 1h  

**Test Cases**:
- プロジェクト作成→メンバー招待→タスク作成フロー
- カンバンワークフロー
- マイルストーン進捗計算

**Files**:
- `tests/integration/*.test.ts`

---

### TSK-PM-036: E2Eテスト
**Priority**: P2  
**Estimate**: 1h  

**Test Cases**:
- CLIコマンドの実行
- 完全なプロジェクトライフサイクル

**Files**:
- `tests/e2e/*.test.ts`

---

## 依存関係グラフ

```
TSK-001 (Value Objects)
    ↓
TSK-002~007 (Entities) ← TSK-008 (Errors)
    ↓
TSK-009 (Repository Interfaces)
    ↓
TSK-010~014 (Repositories)
    ↓
TSK-015~021 (Services)
    ↓
TSK-022~031 (CLI)
    ↓
TSK-032~036 (Tests)
```

---

## サマリー

| 優先度 | タスク数 | 見積時間 |
|--------|---------|---------|
| P0 | 22 | 17.5h |
| P1 | 10 | 7h |
| P2 | 4 | 2.5h |
| **Total** | **36** | **27h** |
