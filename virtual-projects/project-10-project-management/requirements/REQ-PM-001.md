# プロジェクト管理ツール要件定義書

## Document Information
- **Document ID**: REQ-PM-001
- **Version**: 1.0.0
- **Status**: Draft
- **Created**: 2026-01-04
- **Author**: MUSUBIX SDD Workflow

## 1. プロジェクト概要

### 1.1 目的
小規模チーム向けのプロジェクト管理ツールを構築し、タスク管理、進捗追跡、チームコラボレーションを支援する。

### 1.2 スコープ
- プロジェクト作成・管理
- タスク管理（カンバンボード）
- メンバー管理
- 進捗レポート
- マイルストーン管理

### 1.3 対象外
- リアルタイムチャット
- ファイル共有
- 時間追跡（タイムシート）

---

## 2. 機能要件 (EARS形式)

### 2.1 プロジェクト管理 (Project Management)

#### REQ-PM-PRJ-001: プロジェクト作成
**Ubiquitous**
> THE system SHALL allow users to create new projects with a name, description, start date, and optional end date.

**Acceptance Criteria**:
- プロジェクト名は必須（1-100文字）
- 開始日は必須
- プロジェクトIDは自動生成（PRJ-YYYYMMDD-NNN）

#### REQ-PM-PRJ-002: プロジェクト一覧表示
**Event-driven**
> WHEN a user requests the project list, THE system SHALL display all accessible projects with their status, progress percentage, and member count.

**Acceptance Criteria**:
- アクセス可能なプロジェクトのみ表示
- ステータス・日付でソート可能
- ページネーション対応

#### REQ-PM-PRJ-003: プロジェクトステータス更新
**Event-driven**
> WHEN a user changes the project status, THE system SHALL validate the transition and update the status with an audit log entry.

**Acceptance Criteria**:
- 有効なステータス遷移のみ許可
- ステータス: planning, active, on-hold, completed, cancelled

#### REQ-PM-PRJ-004: プロジェクトアーカイブ
**Optional**
> IF a project has been completed or cancelled for more than 90 days, THEN THE system SHALL allow archiving the project to reduce clutter.

**Acceptance Criteria**:
- アーカイブされたプロジェクトは一覧から非表示
- 復元可能

#### REQ-PM-PRJ-006: アーカイブ復元
**Event-driven**
> WHEN a user restores an archived project, THE system SHALL return the project to the 'on-hold' status and make it visible in the project list.

**Acceptance Criteria**:
- 復元後のステータスは on-hold
- 関連タスク・マイルストーンも復元

#### REQ-PM-PRJ-005: 完了プロジェクトの変更防止
**Unwanted**
> THE system SHALL NOT allow modifications to projects with status 'completed' or 'cancelled' except for archiving.

**Acceptance Criteria**:
- 完了/キャンセル済みプロジェクトは読み取り専用
- アーカイブのみ可能

---

### 2.2 タスク管理 (Task Management)

#### REQ-PM-TSK-001: タスク作成
**Ubiquitous**
> THE system SHALL allow users to create tasks within a project with title, description, assignee, priority, and due date.

**Acceptance Criteria**:
- タイトルは必須（1-200文字）
- 優先度: high, medium, low
- 担当者はオプション

#### REQ-PM-TSK-002: タスクステータス更新
**Event-driven**
> WHEN a user moves a task between columns on the kanban board, THE system SHALL update the task status and record the transition time.

**Acceptance Criteria**:
- カンバンカラム: backlog, todo, in-progress, review, done
- ドラッグ&ドロップ対応（CLI版は move コマンド）

#### REQ-PM-TSK-003: タスク割り当て
**Event-driven**
> WHEN a user assigns a task to a team member, THE system SHALL update the assignee and log the assignment for future notification integration.

**Acceptance Criteria**:
- プロジェクトメンバーのみ割り当て可能
- 割り当て履歴をAuditログに記録
- 通知機能は将来拡張として設計時に考慮

#### REQ-PM-TSK-004: タスク検索・フィルタ
**Event-driven**
> WHEN a user applies filters to the task list, THE system SHALL display tasks matching the criteria within 300ms.

**Acceptance Criteria**:
- フィルタ: ステータス、優先度、担当者、期限
- キーワード検索対応

#### REQ-PM-TSK-005: サブタスク管理
**Optional**
> IF a task requires breakdown, THEN THE system SHALL allow creating subtasks linked to the parent task.

**Acceptance Criteria**:
- サブタスクは1階層のみ
- 親タスクの進捗はサブタスク完了率で計算

#### REQ-PM-TSK-006: 期限超過タスク表示
**State-driven**
> WHILE a task's due date has passed and the task is not in 'done' status, THE system SHALL highlight the task as overdue in all views.

**Acceptance Criteria**:
- 視覚的なハイライト（CLI版は [OVERDUE] ラベル）
- 期限超過タスク一覧を提供

#### REQ-PM-TSK-007: 同時編集防止
**Unwanted**
> THE system SHALL NOT allow concurrent updates to the same task that would result in data loss.

**Acceptance Criteria**:
- 楽観的ロック実装
- 競合時はエラーメッセージと最新データを提示

---

### 2.3 メンバー管理 (Member Management)

#### REQ-PM-MEM-001: メンバー招待
**Event-driven**
> WHEN a project owner invites a user to the project, THE system SHALL add them as a member with the specified role.

**Acceptance Criteria**:
- 役割: owner, admin, member, viewer
- 招待はプロジェクト単位

#### REQ-PM-MEM-002: 役割変更
**Event-driven**
> WHEN a project owner or admin changes a member's role, THE system SHALL update permissions immediately.

**Acceptance Criteria**:
- owner は変更不可（譲渡のみ）
- admin は admin 以下の役割を変更可能

#### REQ-PM-MEM-003: メンバー削除
**Event-driven**
> WHEN a project owner or admin removes a member, THE system SHALL revoke their access and reassign their tasks to unassigned status.

**Acceptance Criteria**:
- 削除前に確認プロンプト
- 担当タスクは自動的に未割り当てに変更

#### REQ-PM-MEM-004: 自己削除防止
**Unwanted**
> THE system SHALL NOT allow the sole project owner to remove themselves from the project.

**Acceptance Criteria**:
- 唯一の owner は削除不可
- owner 権限の譲渡後は削除可能

---

### 2.4 マイルストーン管理 (Milestone Management)

#### REQ-PM-MIL-001: マイルストーン作成
**Ubiquitous**
> THE system SHALL allow users to create milestones with a name, description, and target date.

**Acceptance Criteria**:
- 名前は必須（1-100文字）
- 目標日は必須

#### REQ-PM-MIL-002: タスクとマイルストーンの関連付け
**Event-driven**
> WHEN a user associates a task with a milestone, THE system SHALL include the task in milestone progress calculations.

**Acceptance Criteria**:
- 1タスク = 1マイルストーン（多対1）
- マイルストーン進捗 = 完了タスク数 / 全タスク数

#### REQ-PM-MIL-003: マイルストーン進捗表示
**State-driven**
> WHILE a milestone has associated tasks, THE system SHALL display the milestone progress as a percentage based on completed tasks.

**Acceptance Criteria**:
- リアルタイム進捗更新
- 進捗バー表示

#### REQ-PM-MIL-004: 遅延マイルストーン警告
**State-driven**
> WHILE a milestone's target date is within 7 days and progress is below 80%, THE system SHALL display a warning indicator.

**Acceptance Criteria**:
- 警告は自動表示
- 警告閾値は設定可能（将来拡張）

---

### 2.5 レポート機能 (Reporting)

#### REQ-PM-REP-001: プロジェクトサマリーレポート
**Event-driven**
> WHEN a user requests a project summary report, THE system SHALL generate a report showing task statistics, milestone progress, and team activity.

**Acceptance Criteria**:
- タスク統計: ステータス別、優先度別
- マイルストーン進捗一覧
- CSV/JSON形式でエクスポート

#### REQ-PM-REP-002: バーンダウンチャートデータ
**Event-driven**
> WHEN a user requests burndown data, THE system SHALL provide daily completed task counts for the specified date range.

**Acceptance Criteria**:
- 日次データポイント
- 理想線と実績線のデータ

#### REQ-PM-REP-003: メンバー別タスクレポート
**Event-driven**
> WHEN a user requests a member task report, THE system SHALL display task counts and completion rates per team member.

**Acceptance Criteria**:
- 完了率計算
- 期限超過タスク数を含む

---

### 2.6 認証・認可 (Authentication & Authorization)

#### REQ-PM-AUTH-001: ユーザー認証
**Ubiquitous**
> THE system SHALL require users to authenticate before accessing any project management functions.

**Acceptance Criteria**:
- ユーザー名/パスワード認証
- セッションタイムアウト（1時間）

#### REQ-PM-AUTH-002: プロジェクト単位の権限管理
**State-driven**
> WHILE a user accesses a project, THE system SHALL enforce permissions based on their project role.

**Acceptance Criteria**:
| 役割 | プロジェクト設定 | タスク作成 | タスク更新 | メンバー管理 |
|-----|----------------|----------|----------|-------------|
| owner | ✓ | ✓ | ✓ | ✓ |
| admin | - | ✓ | ✓ | ✓ |
| member | - | ✓ | 自分のみ | - |
| viewer | - | - | - | - |

#### REQ-PM-AUTH-003: 不正アクセス防止
**Unwanted**
> THE system SHALL NOT allow users to access projects they are not members of.

**Acceptance Criteria**:
- 非メンバーは403エラー
- プロジェクト存在の漏洩を防止（404ではなく403）

---

## 3. 非機能要件

### 3.1 パフォーマンス (NFR-PM-PERF)

#### NFR-PM-PERF-001: 応答時間
> THE system SHALL respond to user queries within 300ms for 95% of requests.

#### NFR-PM-PERF-002: データ量
> THE system SHALL support projects with up to 1000 tasks without performance degradation.

### 3.2 データ整合性 (NFR-PM-DATA)

#### NFR-PM-DATA-001: トランザクション整合性
> THE system SHALL ensure atomic operations for all task state changes.

#### NFR-PM-DATA-002: 監査ログ
> THE system SHALL maintain an audit log of all project and task modifications for at least 1 year.

### 3.3 可用性 (NFR-PM-AVAIL)

#### NFR-PM-AVAIL-001: データ復旧
> THE system SHALL support data backup and recovery with a recovery point objective (RPO) of 24 hours.

---

## 4. ドメインモデル

### 4.1 エンティティ

| エンティティ | 説明 | 主要属性 |
|-------------|------|----------|
| Project | プロジェクト | id, name, description, startDate, endDate, status, ownerId |
| Task | タスク | id, projectId, title, description, status, priority, assigneeId, dueDate, milestoneId |
| Subtask | サブタスク | id, parentTaskId, title, status |
| Milestone | マイルストーン | id, projectId, name, description, targetDate |
| Member | メンバー | id, projectId, userId, role, joinedAt |
| User | ユーザー | id, username, email, passwordHash |

### 4.2 Value Objects

| Value Object | 説明 | 構成 |
|-------------|------|------|
| ProjectStatus | プロジェクトステータス | planning, active, on-hold, completed, cancelled |
| TaskStatus | タスクステータス | backlog, todo, in-progress, review, done |
| Priority | 優先度 | high, medium, low |
| ProjectRole | プロジェクト役割 | owner, admin, member, viewer |

### 4.3 ステータス遷移

```
Project Status (BP-DESIGN-001):
  planning → active
  active → on-hold, completed, cancelled
  on-hold → active, cancelled
  completed → (terminal, archivable)
  cancelled → (terminal, archivable)

Task Status:
  backlog → todo
  todo → in-progress, backlog
  in-progress → review, todo
  review → done, in-progress
  done → in-progress (reopen)
```

---

## 5. トレーサビリティ

| 要件ID | 優先度 | 設計参照 |
|--------|--------|----------|
| REQ-PM-PRJ-001 | P0 | DES-PM-001 |
| REQ-PM-PRJ-002 | P0 | DES-PM-001 |
| REQ-PM-PRJ-003 | P1 | DES-PM-001 |
| REQ-PM-PRJ-004 | P2 | DES-PM-001 |
| REQ-PM-PRJ-005 | P0 | DES-PM-001 |
| REQ-PM-TSK-001 | P0 | DES-PM-002 |
| REQ-PM-TSK-002 | P0 | DES-PM-002 |
| REQ-PM-TSK-003 | P1 | DES-PM-002 |
| REQ-PM-TSK-004 | P1 | DES-PM-002 |
| REQ-PM-TSK-005 | P2 | DES-PM-002 |
| REQ-PM-TSK-006 | P1 | DES-PM-002 |
| REQ-PM-TSK-007 | P0 | DES-PM-002 |
| REQ-PM-MEM-001 | P0 | DES-PM-003 |
| REQ-PM-MEM-002 | P1 | DES-PM-003 |
| REQ-PM-MEM-003 | P1 | DES-PM-003 |
| REQ-PM-MEM-004 | P0 | DES-PM-003 |
| REQ-PM-MIL-001 | P1 | DES-PM-004 |
| REQ-PM-MIL-002 | P1 | DES-PM-004 |
| REQ-PM-MIL-003 | P1 | DES-PM-004 |
| REQ-PM-MIL-004 | P2 | DES-PM-004 |
| REQ-PM-REP-001 | P1 | DES-PM-005 |
| REQ-PM-REP-002 | P2 | DES-PM-005 |
| REQ-PM-REP-003 | P2 | DES-PM-005 |
| REQ-PM-AUTH-001 | P0 | DES-PM-006 |
| REQ-PM-AUTH-002 | P0 | DES-PM-006 |
| REQ-PM-AUTH-003 | P0 | DES-PM-006 |

---

## 6. 用語集

| 用語 | 定義 |
|-----|------|
| カンバン | タスクをステータスごとに列で表示するボード形式 |
| バックログ | 未着手のタスクプール |
| マイルストーン | プロジェクトの重要な中間目標 |
| バーンダウン | 残タスク量の時系列推移 |
| 楽観的ロック | 更新時にバージョン確認で競合検出 |

---

## Appendix A: EARS パターン使用状況

| パターン | 使用数 | 要件ID |
|---------|--------|--------|
| Ubiquitous | 4 | REQ-PM-PRJ-001, TSK-001, MIL-001, AUTH-001 |
| Event-driven | 13 | REQ-PM-PRJ-002~003, TSK-002~004, MEM-001~003, MIL-002, REP-001~003 |
| State-driven | 4 | REQ-PM-TSK-006, MIL-003~004, AUTH-002 |
| Unwanted | 4 | REQ-PM-PRJ-005, TSK-007, MEM-004, AUTH-003 |
| Optional | 2 | REQ-PM-PRJ-004, TSK-005 |

**Total**: 26 機能要件 + 5 非機能要件 = 31 要件
