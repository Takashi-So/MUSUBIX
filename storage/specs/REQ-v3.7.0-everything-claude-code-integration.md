# MUSUBIX v3.7.0 要件定義書
## Everything Claude Code 分析からの知見統合（Agent Skills実装）

**文書ID**: REQ-v3.7.0-001  
**作成日**: 2026-01-25  
**ステータス**: Draft  
**優先度**: P0-P4 (機能ごとに定義)  
**実装方式**: GitHub Copilot Agent Skills  
**準拠仕様**: [Agent Skills Open Standard](https://github.com/agentskills/agentskills)

---

## 1. エグゼクティブサマリー

`affaan-m/everything-claude-code` リポジトリの分析から、MUSUBIXに不足している以下の主要機能領域を特定しました。  
**これらをGitHub Copilot Agent Skills形式で実装します。**

| カテゴリ | 不足機能 | 優先度 | 対応スキル名 |
|----------|----------|--------|--------------|
| **セッション管理** | Memory Persistence（セッション永続化） | P0 | `session-manager` |
| **タスク追跡** | TodoWrite統合（マルチステップ進捗管理） | P0 | `session-manager` |
| **コンテキスト最適化** | Strategic Compact（戦略的圧縮提案） | P1 | `context-optimizer` |
| **PostToolUse Hooks** | 編集後自動チェック（format/type） | P1 | `context-optimizer` |
| **PreToolUse Hooks** | ツール実行前検証（tmux/git確認） | P2 | `context-optimizer` |
| **継続学習** | Continuous Learning Hooks（自動パターン抽出） | P1 | `learning-hooks` |
| **評価フレームワーク** | Eval Harness（pass@k評価システム） | P1 | `eval-harness` |
| **検証ループ** | Verification Loop（継続的検証） | P2 | `verification-loop` |
| **チェックポイント** | Checkpoint System（状態保存・復元） | P2 | `checkpoint` |
| **動的コンテキスト** | Mode Injection（contexts/*.md） | P2 | `context-optimizer` |
| **コードマップ** | Codemap Generation（アーキテクチャ可視化） | P3 | `codemap` |
| **Dead Code検出** | Refactor Cleaner Agent | P3 | `refactor-cleaner` |
| **ビルドエラー解決** | Build Error Resolver | P2 | `build-fix` |
| **E2Eテスト** | E2E Test Runner（Playwright） | P3 | `e2e-runner` |

### スキル配置構造

```
# プロジェクトスキル（MUSUBIX専用）
# GitHub Copilot: .github/skills/
# Claude Code: .claude/skills/
.github/skills/
├── session-manager/
│   └── SKILL.md
├── context-optimizer/
│   └── SKILL.md
├── learning-hooks/
│   └── SKILL.md
├── eval-harness/
│   └── SKILL.md
├── verification-loop/
│   └── SKILL.md
├── checkpoint/
│   └── SKILL.md
├── codemap/
│   └── SKILL.md
├── refactor-cleaner/
│   └── SKILL.md
├── build-fix/
│   └── SKILL.md
└── e2e-runner/
    └── SKILL.md

# 個人スキル（全プロジェクト共有）
~/.copilot/skills/
└── musubix-common/
    └── SKILL.md
```

---

## 2. MUSUBIXとeverything-claude-codeの機能比較

### 2.1 既にMUSUBIXに存在する機能

| everything-claude-code | MUSUBIX相当機能 | パッケージ |
|------------------------|-----------------|-----------|
| planner agent | sdd_create_requirements + sdd_create_design | mcp-server |
| architect agent | C4 Design Generation | core |
| tdd-guide agent | テスト生成（musubix test generate） | core |
| code-reviewer agent | security analyzer + pattern-mcp | security, pattern-mcp |
| security-reviewer agent | セキュリティ分析 | security |
| orchestrate command | Agent Orchestrator | agent-orchestrator |
| skill management | Skill Manager | skill-manager |
| workflow phases | Workflow Engine (5フェーズ) | workflow-engine |
| P0-P5 triage | ExtendedQualityGate (v3.6.0) | workflow-engine |
| Non-Negotiables | NonNegotiablesEngine (v3.6.0) | policy |

### 2.2 MUSUBIXに不足している機能

以下の機能はeverything-claude-codeに存在するがMUSUBIXには未実装：

| カテゴリ | 機能 | everything-claude-code | MUSUBIX現状 |
|---------|------|----------------------|-------------|
| **セッション管理** | Memory Persistence | session-start.js, session-end.js | ❌ 未実装 |
| **コンテキスト最適化** | Strategic Compact | suggest-compact.sh | ❌ 未実装 |
| **コンテキスト最適化** | PreToolUse Hooks | rules/hooks.md | ❌ 未実装 |
| **コンテキスト最適化** | Doc Blocker | rules/hooks.md | ❌ 未実装 |
| **継続学習** | Auto Pattern Extraction | evaluate-session.js | ⚠️ 部分的（手動のみ） |
| **評価フレームワーク** | pass@k Metrics | eval-harness skill | ❌ 未実装 |
| **検証ループ** | 6-Phase Verification | verification-loop skill | ⚠️ 部分的（品質ゲートのみ） |
| **検証ループ** | Stop Hook監査（log/debugger等） | rules/hooks.md | ❌ 未実装 |
| **チェックポイント** | State Snapshot | /checkpoint command | ❌ 未実装 |
| **ビルドエラー解決** | Build Error Resolver | build-error-resolver agent | ❌ 未実装 |
| **コードマップ** | Architecture Visualization | doc-updater agent | ⚠️ 部分的（codegraph） |
| **Dead Code検出** | Automated Cleanup | refactor-cleaner agent | ❌ 未実装 |
| **E2Eテスト** | E2E Runner（Playwright） | e2e-runner agent | ❌ 未実装 |
| **動的コンテキスト** | Mode Injection | contexts/*.md | ❌ 未実装 |
| **PostToolUse Hooks** | 編集後自動チェック | prettier, tsc hooks | ❌ 未実装 |
| **タスク追跡** | TodoWrite統合 | rules/hooks.md | ❌ 未実装 |

---

## 3. 要件定義（EARS形式）

### 要件IDサマリー

| スキル | 要件ID | 要件数 | 優先度 |
|--------|--------|--------|--------|
| session-manager | REQ-SM-001〜004 | 4 | P0 |
| context-optimizer | REQ-CO-001〜006 | 6 | P1-P2 |
| learning-hooks | REQ-LH-001〜003 | 3 | P1 |
| eval-harness | REQ-EH-001〜005 | 5 | P1 |
| verification-loop | REQ-VL-001〜005 | 5 | P2 |
| checkpoint | REQ-CP-001〜005 | 5 | P2 |
| build-fix | REQ-BF-001〜003 | 3 | P2 |
| codemap | REQ-CM-001〜004 | 4 | P3 |
| refactor-cleaner | REQ-RC-001〜004 | 4 | P3 |
| e2e-runner | REQ-E2E-001〜003 | 3 | P3 |
| **合計** | | **42** | |

### 3.1 Session Manager スキル (P0)

**スキルパス**: `.github/skills/session-manager/SKILL.md`

#### SKILL.md Frontmatter
```yaml
---
name: session-manager
description: |
  MUSUBIXセッション管理スキル。セッション開始時に過去のコンテキストを復元し、
  終了時に状態を永続化する。セッション間の継続性を提供する。
license: MIT
---
```

#### REQ-SM-001: SessionStart Hook
**WHEN** 新しいCopilotセッションが開始される、  
**THE** session-manager **SHALL** 過去7日間のセッションファイルを検索し、利用可能なコンテキストをユーザーに通知する。

**根拠**: everything-claude-codeの`session-start.js`フックは、セッション間の継続性を提供する。

**SKILL.md指示例**:
```markdown
セッション開始時、以下を実行してください：
1. `~/.musubix/sessions/`から過去7日間のセッションファイルを検索
2. 直近のセッションの「Notes for Next Session」を読み込み
3. ユーザーに継続可能なコンテキストを通知
```

#### REQ-SM-002: SessionEnd Hook
**WHEN** Copilotセッションが終了する、  
**THE** session-manager **SHALL** セッションの状態（完了タスク、進行中タスク、次回向けメモ）をMarkdown形式で保存する。

**保存形式**:
```markdown
# Session: 2026-01-25
**Date:** 2026-01-25
**Started:** 14:30
**Last Updated:** 17:45

---

## Current State

### Completed
- [x] Task 1
- [x] Task 2

### In Progress
- [ ] Task 3

### Notes for Next Session
- Important context to remember

### Context to Load
\```
relevant/files/to/load
\```
```

#### REQ-SM-003: Pre-Compact State Saving
**WHEN** コンテキスト圧縮（compaction）がトリガーされる、  
**THE** session-manager **SHALL** 圧縮前の重要な状態をセッションファイルに記録する。

**根拠**: 自動圧縮により重要なコンテキストが失われることを防ぐ。

#### REQ-SM-004: TodoWrite統合
**WHILE** マルチステップタスクを実行中、
**THE** session-manager **SHALL** TodoWriteツールを使用してタスク進捗を追跡し、以下を可視化する：

- 実行順序の妥当性
- 欠落ステップの検出
- 粒度の適切性
- 誤解された要件の早期発見

**根拠**: everything-claude-codeの`rules/hooks.md`に記載されたTodoWrite Best Practicesに準拠。

**SKILL.md指示例**:
```markdown
マルチステップタスクを開始する際は、必ずTodoWriteツールを使用してください：
1. タスクリストを作成し、各ステップを明示
2. 完了したステップをチェック
3. 順序の誤りや欠落があれば修正を提案
4. セッション終了時に未完了タスクをNotes for Next Sessionに記録
```

---

### 3.2 Context Optimizer スキル (P1)

**スキルパス**: `.github/skills/context-optimizer/SKILL.md`

#### SKILL.md Frontmatter
```yaml
---
name: context-optimizer
description: |
  コンテキストウィンドウ最適化スキル。ツール呼び出し回数を追跡し、
  戦略的なタイミングでコンテキスト圧縮を提案する。モードベースの
  コンテキスト注入もサポートする。
license: MIT
---
```

#### REQ-CO-001: Strategic Compact Suggestion
**WHEN** ツール呼び出し回数が設定閾値（デフォルト50回）に達する、  
**THE** context-optimizer **SHALL** 論理的なフェーズ遷移点での手動圧縮を提案する。

**提案タイミング**:
- 計画フェーズ完了後
- デバッグ完了後
- マイルストーン達成後

#### REQ-CO-002: Tool Call Counter
**WHILE** セッションが実行中、  
**THE** context-optimizer **SHALL** ツール呼び出し回数を追跡し、閾値超過後は25回ごとにリマインダーを表示する。

#### REQ-CO-003: Context Mode Injection
**IF** ユーザーがコンテキストモード（dev/review/research）を指定する、  
**THEN THE** context-optimizer **SHALL** 対応するコンテキストをシステムプロンプトに注入する。

**モード定義**:
| モード | フォーカス | 推奨ツール |
|--------|----------|----------|
| dev | 実装・コーディング | Edit, Write, Bash |
| review | コードレビュー | Read, Grep, Glob |
| research | 調査・探索 | Read, Grep, semantic_search |

#### REQ-CO-004: PostToolUse Hooks
**WHEN** ファイル編集ツール（Edit, Write）が実行された後、
**THE** context-optimizer **SHALL** 以下のチェックを提案する：

| ファイル種別 | 自動チェック | ツール |
|-------------|-------------|--------|
| `.ts`, `.tsx` | 型チェック | `npx tsc --noEmit` |
| `.js`, `.ts`, `.tsx` | フォーマット | Prettier |
| `.ts`, `.tsx` | console.log検出 | grep警告 |

**根拠**: everything-claude-codeのPostToolUse Hooksに準拠。

**SKILL.md指示例**:
```markdown
TypeScript/JavaScriptファイルを編集した後は、以下を確認してください：
1. 型エラーがないか（npx tsc --noEmit）
2. フォーマットが整っているか（prettier --check）
3. console.logが残っていないか

問題がある場合はユーザーに報告し、修正を提案してください。
```

#### REQ-CO-005: PreToolUse Hooks
**WHEN** 長時間実行コマンド（npm, pnpm, yarn, cargo等）がBashツールで実行されようとしている、
**THE** context-optimizer **SHALL** tmuxまたはバックグラウンド実行を提案する。

**WHEN** `git push`が実行されようとしている、
**THE** context-optimizer **SHALL** 変更内容の最終確認を促す。

**対象コマンド**:
| コマンドパターン | 提案内容 |
|-----------------|----------|
| `npm install`, `pnpm install` | tmux使用を提案 |
| `npm run build`, `cargo build` | バックグラウンド実行を提案 |
| `git push` | diff確認を促す |
| `rm -rf`, `git reset --hard` | 破壊的操作の警告 |

**根拠**: everything-claude-codeの`rules/hooks.md`に記載されたPreToolUse Hooksに準拠。

**SKILL.md指示例**:
```markdown
以下のコマンドを実行する前に確認してください：
- 長時間コマンド（npm install等）→ tmux内での実行を提案
- git push → 変更差分を再確認
- 破壊的操作（rm -rf等）→ 実行前に警告
```

#### REQ-CO-006: Doc Blocker
**WHEN** 不要なMarkdownファイル（README以外の.md、.txtファイル）が作成されようとしている、
**THE** context-optimizer **SHALL** 本当に必要かユーザーに確認する。

**除外対象**（ブロックしない）:
- README.md
- CHANGELOG.md
- LICENSE
- docs/配下のファイル
- .github/配下のファイル

**根拠**: everything-claude-codeの「doc blocker」PreToolUse Hook。

---

### 3.3 Learning Hooks スキル (P1)

**スキルパス**: `.github/skills/learning-hooks/SKILL.md`

#### SKILL.md Frontmatter
```yaml
---
name: learning-hooks
description: |
  継続的学習スキル。セッション終了時に再利用可能なパターンを自動抽出し、
  学習済みスキルとして保存する。エラー解決・デバッグ・回避策などを学習する。
license: MIT
---
```

#### REQ-LH-001: Continuous Learning Evaluation
**WHEN** セッションが終了し、ユーザーメッセージが10件以上存在する、  
**THE** learning-hooks **SHALL** セッションを分析し、再利用可能なパターンを抽出する。

**抽出対象パターン**:
- `error_resolution`: エラー解決パターン
- `user_corrections`: ユーザー修正パターン
- `workarounds`: フレームワーク回避策
- `debugging_techniques`: デバッグ技法
- `project_specific`: プロジェクト固有パターン

#### REQ-LH-002: Learned Skills Storage
**THE** learning-hooks **SHALL** 抽出したパターンを`~/.musubix/skills/learned/`に保存する。

**スキルファイル形式**:
```markdown
# [Descriptive Pattern Name]

**Extracted:** [Date]
**Context:** [When this applies]

## Problem
[What problem this solves]

## Solution
[The pattern/technique/workaround]

## Example
[Code example if applicable]

## When to Use
[Trigger conditions]
```

#### REQ-LH-003: Pattern Ignore List
**THE** learning-hooks **SHALL NOT** 以下のパターンを抽出対象としない：
- 単純なタイポ修正
- 一時的な問題の修正
- 外部API障害への対応

---

### 3.4 Eval Harness スキル (P1)

**スキルパス**: `.github/skills/eval-harness/SKILL.md`

#### SKILL.md Frontmatter
```yaml
---
name: eval-harness
description: |
  評価ハーネススキル。pass@kメトリクスでAIコード生成の品質を評価する。
  機能評価（Capability）と回帰評価（Regression）の両方をサポートする。
license: MIT
---
```

#### REQ-EH-001: Capability Eval Definition
**THE** eval-harness **SHALL** 機能評価（Capability Eval）を以下の形式で定義する機能を提供する：

```markdown
[CAPABILITY EVAL: feature-name]
Task: Description of what should be accomplished
Success Criteria:
  - [ ] Criterion 1
  - [ ] Criterion 2
  - [ ] Criterion 3
Expected Output: Description of expected result
```

#### REQ-EH-002: Regression Eval Definition
**THE** eval-harness **SHALL** 回帰評価（Regression Eval）を以下の形式で定義する機能を提供する：

```markdown
[REGRESSION EVAL: feature-name]
Baseline: SHA or checkpoint name
Tests:
  - existing-test-1: PASS/FAIL
  - existing-test-2: PASS/FAIL
Result: X/Y passed (previously Y/Y)
```

#### REQ-EH-003: pass@k Metrics
**THE** eval-harness **SHALL** 以下のメトリクスを計算し報告する：

| メトリクス | 説明 | 用途 |
|-----------|------|------|
| pass@1 | 初回試行成功率 | 基本信頼度 |
| pass@3 | 3回以内成功率（少なくとも1回成功） | 一般的ターゲット |
| consecutive@3 | 3回連続成功率（全試行成功） | クリティカルパス |

#### REQ-EH-004: Grader Types
**THE** eval-harness **SHALL** 以下の評価器タイプをサポートする：

1. **Code-Based Grader**: コマンド実行による決定的評価
2. **Model-Based Grader**: LLMによる自由形式評価

#### REQ-EH-005: Human Grader Support
**IF** 自動評価（Code-Based / Model-Based）だけでは判定が困難である、
**THEN THE** eval-harness **SHALL** 人手評価（Human Grader）用のチェックリストテンプレートを生成し、評価結果を記録できるようにする。

**テンプレート例**:
```markdown
[HUMAN GRADE: feature-name]
Reviewer: @username
Checklist:
  - [ ] 仕様を満たしている
  - [ ] エッジケースが考慮されている
  - [ ] 既存API互換性が維持されている
  - [ ] セキュリティ上の懸念がない
Notes:
  - ...
Verdict: PASS/FAIL
```

---

### 3.5 Verification Loop スキル (P2)

**スキルパス**: `.github/skills/verification-loop/SKILL.md`

#### SKILL.md Frontmatter
```yaml
---
name: verification-loop
description: |
  6フェーズ検証ループスキル。Build→Type→Lint→Test→Security→Diffの
  総合的な検証を実行し、PRレディネスを判定する。
license: MIT
---
```

#### REQ-VL-001: Multi-Phase Verification
**WHEN** `/verify`コマンドが実行される、  
**THE** verification-loop **SHALL** 以下のフェーズを順次実行する：

| フェーズ | 検証内容 | 失敗時アクション |
|---------|---------|----------------|
| 1. Build | ビルド成功 | 即座に停止・修正 |
| 2. Type Check | 型エラーなし | 重大エラーは修正 |
| 3. Lint | リント警告 | 報告 |
| 4. Tests | テスト合格・カバレッジ | 報告 |
| 5. Security | セキュリティ問題 | 報告 |
| 6. Diff Review | 変更差分確認 | レビュー |

#### REQ-VL-002: Verification Report
**WHEN** 検証が完了する、  
**THE** verification-loop **SHALL** 以下の形式でレポートを生成する：

```
VERIFICATION REPORT
==================

Build:     [PASS/FAIL]
Types:     [PASS/FAIL] (X errors)
Lint:      [PASS/FAIL] (X warnings)
Tests:     [PASS/FAIL] (X/Y passed, Z% coverage)
Security:  [PASS/FAIL] (X issues)
Diff:      [X files changed]

Overall:   [READY/NOT READY] for PR

Issues to Fix:
1. ...
2. ...
```

#### REQ-VL-003: Continuous Verification
**WHILE** 長時間セッションが実行中、  
**THE** verification-loop **SHALL** 15分ごとまたは大きな変更後に自動検証を提案する。

#### REQ-VL-004: Verification Modes (quick/full)
**WHEN** `/verify quick` が実行される、
**THE** verification-loop **SHALL** 実行時間を優先し、以下の最小セットを実行する：
- Type Check（可能なら）
- Tests（差分に関連する最小範囲、または `test:unit`）
- Diff Review（変更ファイル数と主要差分の要約）

**WHEN** `/verify`（full）が実行される、
**THE** verification-loop **SHALL** REQ-VL-001に定義する全フェーズを実行する。

#### REQ-VL-005: Stop Hook監査
**WHEN** セッションが終了する、
**THE** verification-loop **SHALL** セッション中に編集されたすべてのファイルに対して以下の監査を実行する：

| チェック項目 | 対象ファイル | アクション |
|-------------|-------------|------------|
| console.log残存 | `.ts`, `.tsx`, `.js`, `.jsx` | 警告を表示 |
| debugger残存 | `.ts`, `.tsx`, `.js`, `.jsx` | 警告を表示 |
| TODO/FIXME | 全ファイル | 未完了項目をリスト化 |
| 未コミット変更 | Git管理ファイル | コミット提案 |

**根拠**: everything-claude-codeのStop Hookで実装されている`console.log audit`に準拠。

**SKILL.md指示例**:
```markdown
セッション終了時、以下を確認してください：
1. 編集したファイルにconsole.log/debuggerが残っていないか
2. TODO/FIXMEコメントの未完了項目
3. 未コミットの変更があれば報告
```

---

### 3.6 Checkpoint スキル (P2)

**スキルパス**: `.github/skills/checkpoint/SKILL.md`

#### SKILL.md Frontmatter
```yaml
---
name: checkpoint
description: |
  チェックポイント管理スキル。セーフポイントの作成・復元・
  比較を行う。Gitと統合して状態を追跡する。
license: MIT
---
```

#### REQ-CP-001: Checkpoint Creation
**WHEN** `/checkpoint create <name>`が実行される、  
**THE** checkpoint **SHALL** 以下を実行する：
1. 現在状態の検証（`/verify quick`）
2. Git stash/commitの作成
3. チェックポイントログへの記録

**ログ形式**: `YYYY-MM-DD-HH:MM | checkpoint_name | git_short_sha`

#### REQ-CP-002: Checkpoint Verification
**WHEN** `/checkpoint verify <name>`が実行される、  
**THE** checkpoint **SHALL** 以下を比較・報告する：
- チェックポイント以降の変更ファイル数
- テスト合格率の変化
- カバレッジの変化
- ビルド状態

#### REQ-CP-003: Checkpoint Listing
**WHEN** `/checkpoint list`が実行される、  
**THE** checkpoint **SHALL** 全チェックポイントを以下の形式で表示する：
- 名前
- タイムスタンプ
- Git SHA
- ステータス（current/behind/ahead）

#### REQ-CP-004: Checkpoint Restore
**WHEN** `/checkpoint restore <name>` が実行される、
**THE** checkpoint **SHALL** 指定チェックポイントの状態へ安全に復元する。

**復元前の安全策**:
- 現在の未コミット変更がある場合は、ユーザーに確認してstash/commitを促す
- 復元後に `/verify quick` を提案する

#### REQ-CP-005: Checkpoint Retention & Location
**WHEN** チェックポイントが作成される、
**THE** checkpoint **SHALL** チェックポイントのメタデータを `~/.musubix/checkpoints/checkpoints.log` に追記し、保持数が上限（デフォルト10件）を超える場合は古いものから整理する。

---

### 3.7 Codemap スキル (P3)

**スキルパス**: `.github/skills/codemap/SKILL.md`

#### SKILL.md Frontmatter
```yaml
---
name: codemap
description: |
  コードマップ生成スキル。リポジトリ構造を分析し、アーキテクチャドキュメントを
  自動生成する。新規参加者のオンボーディングを加速する。
license: MIT
---
```

#### REQ-CM-001: Repository Structure Analysis
**THE** codemap **SHALL** リポジトリ構造を分析し、以下を識別する：
- ワークスペース/パッケージ
- ディレクトリ構造
- エントリーポイント
- フレームワークパターン

#### REQ-CM-002: Module Analysis
**THE** codemap **SHALL** 各モジュールについて以下を抽出する：
- エクスポート（公開API）
- インポート（依存関係）
- ルート（APIルート、ページ）
- データベースモデル
- バックグラウンドワーカー

#### REQ-CM-003: Codemap Generation
**THE** codemap **SHALL** 以下の構造でコードマップを生成する：

```
docs/CODEMAPS/
├── INDEX.md              # 全体概要
├── frontend.md           # フロントエンド構造
├── backend.md            # バックエンド/API構造
├── database.md           # データベーススキーマ
├── integrations.md       # 外部サービス
└── workers.md            # バックグラウンドジョブ
```

#### REQ-CM-004: Codemap Diff Threshold & Report
**WHEN** 既存のコードマップが存在する状態でコードマップを更新する、
**THE** codemap **SHALL** 変更差分率（diff%）を算出し、閾値（デフォルト30%）を超える場合はユーザー承認を求める。

**THE** codemap **SHALL** 更新結果のサマリーとdiff%を `.reports/codemap-diff.txt` に出力する。

---

### 3.8 Refactor Cleaner スキル (P3)

**スキルパス**: `.github/skills/refactor-cleaner/SKILL.md`

#### SKILL.md Frontmatter
```yaml
---
name: refactor-cleaner
description: |
  リファクタリング・クリーナースキル。デッドコード検出・安全な削除を実行する。
  knip, depcheck, ts-pruneと連携してコードベースをクリーンに保つ。
license: MIT
---
```

#### REQ-RC-001: Dead Code Detection
**THE** refactor-cleaner **SHALL** 以下のツールを使用してデッドコードを検出する：
- knip: 未使用ファイル、エクスポート、依存関係
- depcheck: 未使用npm依存関係
- ts-prune: 未使用TypeScriptエクスポート

#### REQ-RC-002: Safe Deletion
**BEFORE** コード削除を実行する、  
**THE** refactor-cleaner **SHALL** 以下を検証する：
- 動的インポートによる参照がないこと
- テストでの参照がないこと
- ドキュメントでの参照がないこと

#### REQ-RC-003: Deletion Log
**WHEN** コードを削除する、  
**THE** refactor-cleaner **SHALL** `docs/DELETION_LOG.md`に以下を記録する：
- 削除日時
- 削除ファイル/コード
- 削除理由
- 復元方法（Git SHA）

#### REQ-RC-004: Risk Classification & Report
**WHEN** デッドコード検出結果を報告する、
**THE** refactor-cleaner **SHALL** 変更候補を以下の3段階で分類し、`.reports/dead-code-analysis.md` にレポートを出力する：

1. **SAFE**: 静的解析上も参照がなく、削除しても影響が限定的
2. **CAUTION**: 動的参照の可能性があり、追加確認が必要
3. **DANGER**: 公開API/エントリーポイント等に影響し得るため自動削除しない

---

### 3.9 Build Fix スキル (P2)

**スキルパス**: `.github/skills/build-fix/SKILL.md`

#### SKILL.md Frontmatter
```yaml
---
name: build-fix
description: |
  ビルドエラー解決スキル。ビルドエラーを分析し、段階的に修正する。
  TypeScript、ESLint、Webpack/Vite等のエラーに対応。
license: MIT
---
```

#### REQ-BF-001: Build Error Analysis
**WHEN** ビルドエラーが発生する、
**THE** build-fix **SHALL** エラーを以下のカテゴリに分類する：

| カテゴリ | 例 | 優先度 |
|---------|-----|--------|
| Type Error | TS2322, TS2339 | 高 |
| Import Error | Module not found | 高 |
| Syntax Error | Unexpected token | 高 |
| Lint Error | ESLint warnings | 中 |
| Config Error | tsconfig, webpack | 中 |
| Dependency Error | Version mismatch | 低 |

#### REQ-BF-002: Iterative Fix Strategy
**WHILE** ビルドエラーが存在する、
**THE** build-fix **SHALL** 以下のループを実行する：

1. エラーリストを取得
2. 最も影響範囲の大きいエラーを特定
3. 修正を適用
4. ビルドを再実行
5. 新たなエラーがあれば1に戻る

**最大反復回数**: 10回（超過時はユーザーに報告）

#### REQ-BF-003: Fix Report
**WHEN** ビルドエラーの修正が完了する、
**THE** build-fix **SHALL** 以下を報告する：
- 修正したエラー数
- 変更したファイル一覧
- 残存する警告（あれば）

**根拠**: everything-claude-codeの`build-error-resolver` agentに相当。

---

### 3.10 E2E Runner スキル (P3)

**スキルパス**: `.github/skills/e2e-runner/SKILL.md`

#### SKILL.md Frontmatter
```yaml
---
name: e2e-runner
description: |
  E2Eテスト実行スキル。Playwrightを使用してエンドツーエンドテストを
  生成・実行する。クリティカルユーザーフローの検証に使用。
license: MIT
---
```

#### REQ-E2E-001: E2E Test Generation
**WHEN** `/e2e generate <flow>`コマンドが実行される、
**THE** e2e-runner **SHALL** 指定されたユーザーフローのE2Eテストを生成する。

**生成されるファイル**:
```
tests/e2e/
├── <flow-name>.spec.ts
└── fixtures/
    └── <flow-name>.json
```

**テストテンプレート**:
```typescript
import { test, expect } from '@playwright/test';

test.describe('<Flow Name>', () => {
  test('should complete the flow', async ({ page }) => {
    // Generated test steps
  });
});
```

#### REQ-E2E-002: E2E Test Execution
**WHEN** `/e2e run [flow]`コマンドが実行される、
**THE** e2e-runner **SHALL** Playwrightでテストを実行し、結果を報告する。

**実行オプション**:
| オプション | 説明 |
|-----------|------|
| `--headed` | ブラウザを表示して実行 |
| `--debug` | デバッグモードで実行 |
| `--trace` | トレースを記録 |

#### REQ-E2E-003: E2E Report
**WHEN** E2Eテストが完了する、
**THE** e2e-runner **SHALL** 以下の形式でレポートを生成する：

```
E2E TEST REPORT
===============

Total:    X tests
Passed:   Y tests
Failed:   Z tests
Skipped:  W tests

Duration: XX.XXs

Failed Tests:
1. test-name: Error message
   Screenshot: playwright-report/...
```

**根拠**: everything-claude-codeの`e2e-runner` agentに相当。

---

## 4. 実装優先順位

### Phase 1: Core Session Management (v3.7.0)
1. **session-manager** スキル（REQ-SM-001〜004）
2. **context-optimizer** スキル（REQ-CO-001〜004）
3. **learning-hooks** スキル（REQ-LH-001〜003）

### Phase 2: Evaluation Framework (v3.7.1)
4. **context-optimizer** スキル（REQ-CO-005〜006）
5. **eval-harness** スキル（REQ-EH-001〜005）
6. **verification-loop** スキル（REQ-VL-001〜005）
7. **checkpoint** スキル（REQ-CP-001〜005）
8. **build-fix** スキル（REQ-BF-001〜003）

### Phase 3: Code Intelligence (v3.7.2)
9. **codemap** スキル（REQ-CM-001〜004）
10. **refactor-cleaner** スキル（REQ-RC-001〜004）
11. **e2e-runner** スキル（REQ-E2E-001〜003）

---

## 5. 設計原則

### 5.1 Agent Skills標準準拠
[Agent Skills Open Standard](https://github.com/agentskills/agentskills)に準拠した実装：

| 要素 | 説明 | 必須 |
|------|------|------|
| `SKILL.md` | スキル定義ファイル | ✅ |
| YAML frontmatter | name, description, license | ✅ |
| Markdown本文 | 指示・例・ガイドライン | ✅ |
| スクリプト | ヘルパースクリプト（任意） | ○ |
| リソース | テンプレート・例（任意） | ○ |

### 5.2 スキル配置構造

```
# プロジェクトスキル（MUSUBIXリポジトリ内）
.github/skills/
├── session-manager/
│   ├── SKILL.md
│   └── scripts/
│       ├── session-start.sh
│       └── session-end.sh
├── context-optimizer/
│   ├── SKILL.md
│   └── contexts/
│       ├── dev.md
│       ├── review.md
│       └── research.md
├── learning-hooks/
│   ├── SKILL.md
│   └── templates/
│       └── learned-skill-template.md
├── eval-harness/
│   ├── SKILL.md
│   └── examples/
│       ├── capability-eval.md
│       └── regression-eval.md
├── verification-loop/
│   ├── SKILL.md
│   └── scripts/
│       └── verify.sh
├── checkpoint/
│   └── SKILL.md
├── codemap/
│   ├── SKILL.md
│   └── templates/
│       └── codemap-index.md
├── refactor-cleaner/
│   └── SKILL.md
├── build-fix/
│   └── SKILL.md
└── e2e-runner/
  └── SKILL.md

# 個人スキル（全プロジェクト共有）
~/.copilot/skills/
├── musubix-common/
│   └── SKILL.md           # MUSUBIX共通ルール
└── learned/               # 学習済みスキル（自動生成）
    ├── error-resolution-xxx/
    └── workaround-yyy/
```

### 5.3 MCPツールとの連携
スキルかMUSUBIX MCPツールを呼び出す方法：

```markdown
## MCPツール統合

このスキルはMUSUBIX MCPサーバーの以下のツールと連携します：

- `sdd_validate_requirements`: 要件検証
- `workflow_get_status`: ワークフロー状態取得
- `knowledge_query`: 知識グラフ検索

MCPツールが利用可能な場合は、それらを優先的に使用してください。
```

### 5.4 Hook統合
everything-claude-codeのHook種別をAgent Skillsで実現：

| Hook Type | Agent Skills実装方法 |
|-----------|-----------------------|
| PreToolUse | SKILL.mdで「ツール実行前に...」指示 |
| PostToolUse | SKILL.mdで「ツール実行後に...」指示 |
| SessionStart | descriptionで「セッション開始時に使用」指定 |
| Stop | SKILL.mdで「セッション終了時に...」指示 |
| PreCompact | session-managerスキルで実装 |

### 5.5 スキル依存関係

```
session-manager (基盤)
    ↓
context-optimizer ──→ session-manager
    ↓
learning-hooks ────→ session-manager, pattern-mcp (MCPツール)
    ↓
eval-harness ──────→ verification-loop
    ↓
verification-loop ─→ workflow-engine (MCPツール)
    ↓
checkpoint ────────→ verification-loop
    ↓
build-fix ─────────→ verification-loop
    ↓
codemap ───────────→ codegraph (MCPツール)
    ↓
refactor-cleaner ──→ codemap
    ↓
e2e-runner ────────→ verification-loop, codemap
```

---

## 6. 非機能要件

### NFR-001: パフォーマンス
| 項目 | 要件 |
|------|------|
| Hook実行時間 | 各Hook 100ms以下 |
| セッション保存 | 500ms以下 |
| パターン抽出 | 5秒以下/セッション |
| 検証ループ全体 | 60秒以下 |

### NFR-002: ストレージ
| 項目 | 要件 |
|------|------|
| セッションファイル最大サイズ | 1MB/ファイル |
| セッション保持期間 | 30日（自動削除） |
| チェックポイント保持数 | 最新10件 |
| 学習パターン最大数 | 500パターン |

### NFR-003: 互換性
| 項目 | 要件 |
|------|------|
| GitHub Copilot | ✅ フルサポート（Agent Skills） |
| Claude Code | ✅ `.claude/skills/`でサポート |
| GitHub Copilot CLI | ✅ `~/.copilot/skills/`でサポート |
| VS Code Insiders | ✅ Agent Modeでサポート |
| MUSUBIX MCP | ✅ MCPツールと連携可能 |

### NFR-004: セキュリティ
| 項目 | 要件 |
|------|------|
| 学習データ | ローカル保存のみ（外部送信禁止） |
| 機密情報フィルタ | APIキー、パスワード自動除外 |
| セッションデータ | ユーザー明示的な同意なしに共有禁止 |

---

## 7. 成功基準

| メトリクス | 目標値 | 計測方法 |
|-----------|--------|---------|
| セッション継続性 | 90%以上のコンテキスト保持 | ユーザーテスト |
| パターン抽出率 | セッション当たり1-3パターン | 自動計測 |
| 検証実行率 | 変更の80%以上で検証実行 | ログ分析 |
| consecutive@3達成率 | 機能評価90%以上 | 評価結果 |
| デッドコード削減 | 未使用コード5%以下 | 静的解析 |

---

## 8. リスクと軽減策

| リスク | 影響度 | 軽減策 |
|--------|--------|--------|
| コンテキストウィンドウ消費 | 高 | Strategic Compactによる最適化 |
| Hook実行オーバーヘッド | 中 | 軽量実装、非同期処理 |
| パターン誤抽出 | 低 | 信頼度閾値、ユーザー確認 |
| チェックポイント肥大化 | 低 | 自動クリーンアップ（最新5件保持） |


---

## 9. 参考資料

### Agent Skills
- [GitHub Docs: Agent Skills](https://docs.github.com/ja/copilot/concepts/agents/about-agent-skills)
- [Agent Skills Open Standard](https://github.com/agentskills/agentskills)
- [anthropics/skills](https://github.com/anthropics/skills)
- [github/awesome-copilot](https://github.com/github/awesome-copilot)

### everything-claude-code
- [affaan-m/everything-claude-code](https://github.com/affaan-m/everything-claude-code)
- [The Shorthand Guide to Everything Claude Code](https://x.com/affaanmustafa/status/2012378465664745795)
- [The Longform Guide to Everything Claude Code](https://x.com/affaanmustafa/status/2014040193557471352)

### MUSUBIX
- [MUSUBIX v3.6.0 FastRender Insights](docs/qiita/musubix-v3.6.0-fastrender-insights.md)

---

**Author**: MUSUBIX Team  
**Version**: 3.7.0-draft  
**Date**: 2026-01-25
