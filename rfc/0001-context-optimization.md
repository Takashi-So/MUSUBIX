# MUSUBIX コンテキスト管理改善: 調査結果と実装計画

> **作成日**: 2026-02-23
> **ステータス**: 調査完了・実装承認待ち
> **関連プロジェクト**: [cc-sdd](https://github.com/gotalab/cc-sdd)

---

## 1. 解決したい課題

> **対象**: MUSUBIXを利用するユーザーのプロジェクト。MUSUBIX自体の開発は対象外。

| # | 課題 | 現状 | 影響 |
|---|------|------|------|
| 1 | **ワークフローのコンテキスト枯渇** | SDDワークフローは5フェーズあり、全フェーズをメインコンテキストで実行するとトークンが枯渇する | 長い開発セッションでコンテキスト上限に到達 |
| 2 | **並列実行** | 独立した作業（例: テスト生成とドキュメント更新）が順次実行されている | 作業時間の増大 |

### コンテキスト消費の内訳（ユーザープロジェクト）

`npx musubix init`で生成されるCLAUDE.mdは約50行/2KBと軽量。
ユーザープロジェクトのコンテキスト消費はCLAUDE.mdよりも**スキル呼び出しとsteering/参照**が支配的。

| カテゴリ | ロードタイミング | サイズ目安 |
|---------|----------------|----------|
| プロジェクト CLAUDE.md (`npx musubix init`生成) | 毎ターン自動 | ~2 KB（軽量） |
| ユーザーのグローバル ~/.claude/ | 毎ターン自動 | ユーザーによる |
| steering/ | CLAUDE.mdが参照指示、SDDワークフロー開始時 | ~50 KB（プロジェクト規模による） |
| skills (10個、init時にインストール) | スキル呼び出し時 | 1スキルあたり3-9 KB |
| **SDDワークフロー全体実行時** | **5フェーズ分の蓄積** | **大（枯渇リスク）** |

**最大の問題**: SDDワークフローを実行すると、各フェーズでsteering/を読み込み、
スキルのガイダンスがメインコンテキストに蓄積し、さらに各フェーズの成果物（要件書、設計書等）の
詳細がメインに残り続ける。**5フェーズ全体をメインコンテキストで実行するのが根本原因**。

**明確にすること**: 手段（サブエージェント等）は目的ではなく、上記2つの課題を解決する最適な方法を選ぶ。

---

## 2. Claude Code のコンテキスト管理機構（2026年2月時点）

### 2.1 Agent tool（旧 Task tool）

> **注意**: Task toolはClaude Code v2.1.63で**Agent tool**にリネームされた。
> `subagent_type`は`agent_type`に変更。旧名`Task()`もエイリアスとして引き続き動作する。

Agent toolはサブエージェントを起動するためのネイティブ機能。主要パラメータ：

| パラメータ | 必須 | 説明 |
|-----------|------|------|
| `agent_type` | はい | エージェント名（組み込み or カスタム、**自由文字列**） |
| `description` | はい | 3-5語のタスク概要 |
| `prompt` | はい | 詳細な指示 |
| `run_in_background` | いいえ | `true`で**バックグラウンド並列実行** |
| `model` | いいえ | モデル上書き: sonnet, opus, haiku |
| `resume` | いいえ | 前回のエージェントIDを指定して再開 |

**組み込みエージェントタイプ**:

| agent_type | モデル | ツール | 用途 |
|------------|--------|--------|------|
| `Explore` | Haiku（高速） | 読み取り専用 | ファイル探索、コード検索 |
| `Plan` | 継承 | 読み取り専用 | 実装計画の策定 |
| `general-purpose` | 継承 | 全ツール | 複雑なマルチステップタスク |
| `Bash` | 継承 | ターミナルのみ | コマンド実行 |

### 2.2 カスタムエージェント（`.claude/agents/`）

`.claude/agents/`にMarkdownファイルを配置すると、**カスタムエージェントタイプ**として認識される。
`agent_type`に自由文字列としてカスタムエージェント名を指定できる。

**エージェント定義の優先順位**:

| 優先度 | 配置場所 | スコープ |
|--------|---------|---------|
| 1（最高） | `--agents` CLIフラグ | セッションのみ |
| 2 | `.claude/agents/` | プロジェクト（VCSにコミット可能） |
| 3 | `~/.claude/agents/` | 全プロジェクト（個人） |
| 4（最低） | プラグインの `agents/` | プラグイン有効範囲 |

**フロントマター仕様**:

```yaml
---
name: my-agent              # 必須: 一意識別子（小文字+ハイフン）
description: ...             # 必須: Claudeがいつこのエージェントに委譲すべきか
tools: Read, Write, Glob     # 許可ツールリスト（省略時は全ツール継承）
disallowedTools: Bash        # 拒否ツールリスト
model: inherit               # sonnet/opus/haiku/inherit（デフォルト: inherit）
skills: skill-a, skill-b     # プリロードするスキル名（既存スキルを再利用!）
maxTurns: 30                 # 最大ターン数
background: false            # trueでバックグラウンド実行
isolation: worktree          # worktreeでGit worktree分離
---

Markdown本文がエージェントのシステムプロンプトになる。
```

**`skills`フィールドの重要性**: 既存のスキルをエージェントにプリロードできる。
知識を複製する必要がなく、スキルを更新すればエージェントも自動的に最新化される。

### 2.3 Skills と `context: fork`

#### Commands と Skills の関係

Claude Codeでは**CommandsはSkillsに統合済み**。新たに`.claude/commands/`を作成する必要はない。

#### `context: fork` の動作

スキルのフロントマターに`context: fork`を追加すると、サブエージェントとして実行される。
`agent`フィールドでカスタムエージェントを指定可能：

```yaml
---
name: my-research-skill
description: ...
context: fork
agent: my-custom-agent    # カスタムエージェントを実行環境として指定（省略時: general-purpose）
---
```

| 項目 | `context: fork` なし | `context: fork` あり |
|------|---------------------|---------------------|
| 実行場所 | メインコンテキスト内 | 独立した新規コンテキスト |
| 会話履歴 | 全履歴にアクセス可能 | **アクセス不可** |
| トークン消費 | メインに蓄積 | サブエージェント側で消費 |
| 戻り値 | なし（メインに直接反映） | サマリーがメインに返却 |
| 他のAgent()呼び出し | 可能 | **不可**（ネスト禁止） |

### 2.4 フォアグラウンド vs バックグラウンド実行

| モード | 動作 | 並列 | 権限 |
|--------|------|------|------|
| **フォアグラウンド**（デフォルト） | メイン会話をブロック | 不可（1つずつ） | ユーザーに権限確認 |
| **バックグラウンド** | 並列に実行 | **可能** | 事前承認が必要 |

**並列実行にはバックグラウンドモードが必須**。Agent tool呼び出し時に`run_in_background: true`を指定するか、
エージェント定義に`background: true`を設定する。

### 2.5 サブエージェントの制約（ハード制約）

```
サブエージェントは他のサブエージェントを起動できない。
マルチレベルの委譲が必要な場合は、メイン会話からAgent()をチェインすること。
```

これはClaude Codeのアーキテクチャ上の制約であり、回避不可能。

---

## 3. cc-sddの実装分析

### 3.1 cc-sddのアーキテクチャ

cc-sddは `.claude/commands/` + `.claude/agents/` の二層構造：

```
.claude-code-agent/
├── commands/kiro/           ← ユーザー向けコマンド（12個）
│   ├── spec-quick.md        ← オーケストレーター（全フェーズ一括）
│   ├── spec-requirements.md ← Task()でサブエージェントを呼び出し
│   ├── spec-design.md
│   ├── spec-tasks.md
│   ├── spec-impl.md
│   └── ...
└── agents/kiro/             ← サブエージェント定義（9個）
    ├── spec-requirements.md ← EARS要件生成ロジック
    ├── spec-design.md       ← 設計生成ロジック
    ├── spec-tasks.md        ← タスク分解ロジック
    ├── spec-impl.md         ← TDD実装ロジック
    └── ...
```

### 3.2 cc-sddの設計パターン

1. **コマンド（薄い層）**: 引数パースと前提条件チェックのみ → `Task()`（現`Agent()`）で委譲
2. **エージェント（厚い層）**: Step 0〜4のプロトコルで自律的に実行
3. **ファイルパターン委譲**: コマンドはglobパターン（文字列）を渡し、サブエージェントが展開
4. **ツール制限**: エージェントごとに最小限のツールを許可
5. **オーケストレーション**: `spec-quick`が4つのサブエージェントを順次呼び出し

### 3.3 cc-sddの評価

| 良い点 | 改善余地 |
|--------|---------|
| コンテキスト分離が明確 | commandsはスキルに統合済みで、やや旧式 |
| ツール制限で安全性確保 | コマンド+エージェントの二重管理が冗長 |
| オーケストレーターパターンが便利 | cc-sddはskillsを使っていない |
| Step 0のファイルパターン展開が効率的 | — |

---

## 4. MUSUBIXの現状分析

### 4.1 現在の`.claude/`構造

```
.claude/
├── skills/              (13スキル)
│   ├── musubix-sdd-workflow/SKILL.md       ← SDDワークフロー全体ガイド
│   ├── musubix-ears-validation/SKILL.md    ← EARS検証ガイド
│   ├── musubix-code-generation/SKILL.md    ← コード生成ガイド
│   ├── musubix-c4-design/SKILL.md          ← C4設計ガイド
│   ├── musubix-test-generation/SKILL.md    ← テスト生成ガイド
│   ├── musubix-traceability/SKILL.md       ← トレーサビリティガイド
│   ├── musubix-adr-generation/SKILL.md     ← ADR生成ガイド
│   ├── musubix-best-practices/SKILL.md     ← ベストプラクティスガイド
│   ├── musubix-technical-writing/SKILL.md  ← テクニカルライティングガイド
│   ├── musubix-domain-inference/SKILL.md   ← ドメイン推論ガイド
│   ├── musubix-decision-records/SKILL.md   ← 意思決定記録ガイド
│   ├── musubix-knowledge-graph/SKILL.md    ← 知識グラフガイド
│   └── musubix-policy-engine/SKILL.md      ← ポリシーエンジンガイド
├── prompts/             (12プロンプト ← SDDフェーズごとの詳細指示)
│   ├── sdd-requirements.prompt.md   ← 要件定義の詳細プロンプト
│   ├── sdd-design.prompt.md         ← 設計の詳細プロンプト
│   ├── sdd-tasks.prompt.md          ← タスク分解の詳細プロンプト
│   ├── sdd-implement.prompt.md      ← 実装の詳細プロンプト
│   ├── sdd-test.prompt.md           ← テストの詳細プロンプト
│   ├── sdd-validate.prompt.md       ← 検証の詳細プロンプト
│   ├── sdd-review.prompt.md         ← レビューの詳細プロンプト
│   ├── sdd-security.prompt.md       ← セキュリティの詳細プロンプト
│   ├── sdd-steering.prompt.md       ← steering参照の詳細プロンプト
│   ├── sdd-change-init.prompt.md    ← 変更開始の詳細プロンプト
│   ├── sdd-change-apply.prompt.md   ← 変更適用の詳細プロンプト
│   └── sdd-change-archive.prompt.md ← 変更アーカイブの詳細プロンプト
├── agents/              ← 存在しない（今回新規作成）
└── settings.json        ← 存在しない
```

### 4.2 現在のスキルの特性

| スキル | 種類 | `context: fork` | コンテキスト消費 |
|--------|------|-----------------|----------------|
| musubix-sdd-workflow | ガイド | なし | **大**（全フェーズのガイダンスを含む） |
| musubix-ears-validation | ガイド | なし | 中 |
| musubix-code-generation | ガイド | なし | 中 |
| musubix-c4-design | ガイド | なし | 中 |
| musubix-test-generation | ガイド | なし | 中 |
| musubix-traceability | ガイド | なし | 小 |
| その他7スキル | ガイド | なし | 小〜中 |

**問題**: すべてのスキルがメインコンテキスト内で実行される。特に`musubix-sdd-workflow`は211行のガイダンスを含み、呼び出すたびにコンテキストを消費する。

### 4.3 関連TypeScriptパッケージ

| パッケージ | 状態 | 今回の改善との関係 |
|-----------|------|-------------------|
| `packages/agent-orchestrator/` | 設計のみ（SubagentAdapterはプレースホルダー） | **変更不要**。Claude Codeのネイティブ機能で代替 |
| `packages/expert-delegation/` | 動作する（VS Code LM API統合） | **変更不要**。サブエージェント内から利用可能 |
| `packages/workflow-engine/` | 動作する（5フェーズ制御） | **変更不要**。参考にするがClaude Code機能で代替 |

---

## 5. 推奨するアプローチ

### 5.1 方針: Skills + `.claude/agents/`

**cc-sddのcommands/agents二層構造を踏まえつつ、Claude Codeの最新機能を活用する**：

1. **既存スキル（13個）はそのまま維持** — ガイダンスとしての役割を継続
2. **SDDフェーズごとのサブエージェントを`.claude/agents/`に定義** — コンテキスト分離用
3. **オーケストレーター用スキルを新規追加** — `context: fork`なし（Agent()呼び出しのため）
4. **不要なcommandsは作成しない** — スキルで統一

### 5.2 なぜこのアプローチが最適か

| 比較軸 | cc-sdd方式（commands+agents） | 推奨方式（skills+agents） |
|--------|---------------------------|------------------------|
| 二重管理 | コマンドとエージェントの2ファイル | エージェント1ファイル（+必要ならスキル） |
| 将来性 | commandsはレガシー | skillsが公式推奨 |
| 既存資産 | MUSUBIXにcommands/なし | MUSUBIXに13スキル既存 |
| 自動呼び出し | なし | Claudeが文脈に応じて自動呼び出し可能 |
| コンテキスト分離 | 同等（Agent()経由） | 同等（Agent()経由） |
| 並列実行 | 同等 | 同等 |

### 5.3 想定する利用パターン

本システムは以下の3つの利用パターンすべてに対応する必要がある：

| パターン | 説明 | 例 |
|---------|------|-----|
| **A: 全工程一括** | 新機能を要件定義から実装まで通して行う | 「認証機能を実装して」 |
| **B: 特定フェーズ単独** | 特定のフェーズだけを実行する（別日の継続含む） | 「昨日の要件をもとに設計を作って」 |
| **C: 修正・部分作業** | リリース済みプロダクトの修正、テスト追加、リファクタリング等 | 「このバグを修正して」「テストを追加して」 |

**パターンごとの呼び出し方式**:

```
パターンA（全工程一括）:
  ユーザー → オーケストレーター・スキル → Agent(requirements-agent) → Agent(design-agent) → ...

パターンB（特定フェーズ単独）:
  ユーザー → メイン会話でClaudeがAgent()を直接呼び出し → Agent(design-agent)
  ※ エージェントはspec.jsonから現在の状態を自動検出し、前提条件を検証

パターンC（修正・部分作業）:
  ユーザー → メイン会話で直接実行（サブエージェント不要な場合も多い）
  ※ 変更が大きい場合のみ、必要なエージェントをAgent()で呼び出し
```

### 5.4 コンテキスト保証の原則

サブエージェントが正しく動作するために、以下の原則を設ける：

#### 原則1: 各エージェントは自己完結する

各エージェントは**オーケストレーター経由でもAgent()による単独呼び出しでも**正しく動作しなければならない。
そのため、各エージェントに**必須コンテキスト読み込みステップ**を定義する：

```
Step 0: コンテキスト読み込み（全エージェント共通）
  ├─ 1. steering/*.md を Glob → Read（プロジェクト方針の把握）
  ├─ 2. storage/specs/<feature>/spec.json を Read（現在の状態把握）
  ├─ 3. 自フェーズの前提となるファイルを Read（例: design-agentならrequirements.md）
  └─ 4. ファイルが存在しない場合はエラーメッセージを返して停止
```

#### 原則2: spec.jsonによる状態管理

spec.jsonが**唯一の状態管理ファイル**として機能する。
各エージェントはspec.jsonを読んで以下を判断する：

- 現在どのフェーズまで完了しているか
- 前フェーズが承認済みか
- どのIDが採番済みか

```json
{
  "feature": "user-authentication",
  "phase": "design-approved",
  "approvals": {
    "requirements": { "generated": true, "approved": true },
    "design": { "generated": true, "approved": true },
    "tasks": { "generated": false, "approved": false }
  }
}
```

→ この状態でtasks-agentを呼ぶと、requirements.mdとdesign.mdを読み込んでタスク分解を開始。
→ この状態でrequirements-agentを呼ぶと、既存の要件を読み込んで「修正モード」で動作。

#### 原則3: 前提条件の検証と適応

各エージェントは前提条件が満たされない場合、2つの動作モードを持つ：

| 状況 | 動作 |
|------|------|
| 前フェーズの成果物が存在しない | **エラーで停止** + 必要な手順を案内（例: 「先にrequirements-agentを実行してください」） |
| 前フェーズの成果物が存在するが未承認 | **警告付きで続行** + サマリーに警告を含める |
| 前フェーズの成果物が存在し承認済み | **通常実行** |
| spec.jsonが存在しない（パターンCの修正作業） | **spec.jsonなしモードで動作**（既存コードベースから直接作業） |

#### 原則4: 修正作業への対応

パターンC（修正・部分作業）では、フルSDDワークフローが不要な場合がある。
この場合は以下のように対応する：

- **バグ修正**: メインコンテキストで直接実行。コンテキストが膨らむ場合のみimplement-agentに委譲
- **テスト追加**: メインコンテキストで直接実行。大量のテスト追加の場合のみimplement-agentに委譲
- **リファクタリング**: implement-agentに委譲（既存テストの通過確認が必要なため）
- **新機能追加（小規模）**: メインコンテキストで直接実行、または必要なフェーズのみエージェントに委譲

**判断基準**: サブエージェントに委譲するかどうかは、作業量とコンテキスト消費量で判断する。
小規模な変更をわざわざサブエージェントに委譲すると、Step 0のコンテキスト読み込みオーバーヘッドの方が大きくなるため、メインコンテキストで直接実行した方が効率的。

### 5.5 情報漏れ防止の仕組み

サブエージェントはメインの会話履歴を引き継がないため、以下の3種類の情報が漏れるリスクがある。
それぞれに対する防止策を設計に組み込む。

#### 漏れリスク1: 横断的なユーザー指示

**問題**: ユーザーが会話中に伝えた横断的指示（「セキュリティを重視して」「DBはPostgreSQLで」等）は、
特定フェーズの成果物（requirements.md等）に書く場所がなく、次フェーズのサブエージェントに伝わらない。

**対策: ユーザーディレクティブファイル**

```
storage/specs/<feature>/directives.md
```

オーケストレーターがユーザーの横断的指示を検出した時点で、このファイルに即座に書き出す。
各サブエージェントはStep 0でこのファイルを読み込み、全フェーズを通じて一貫した方針を適用する。

```markdown
# ユーザーディレクティブ

## 技術制約
- DBはPostgreSQLを使用（MySQLは使わない）
- ORMはPrismaを使用
- デプロイ先はAWS（ECS + RDS）

## 品質方針
- セキュリティを特に重視すること
- テストカバレッジは90%以上を目指す

## コーディング規約
- エラーハンドリングはResult型で統一
- 変数名はキャメルケース
```

**タイミング**: オーケストレーターは各フェーズ間のユーザー確認やりとりで
横断的指示を検出するたびに directives.md を追記更新する。
パターンBやCの場合も、メインの会話でClaudeが横断的指示を検出したら書き出す。

#### 漏れリスク2: フェーズ間の意思決定コンテキスト

**問題**: Phase 1で3回レビューを往復した経緯、レビューで「既存要件と重複の可能性あり」と警告が出た事実、
ユーザーが「REQ-001をP2→P0に変更した理由」など、意思決定コンテキストが次フェーズに伝わらない。

**対策: フェーズサマリファイル**

```
storage/specs/<feature>/phase-1-summary.md
storage/specs/<feature>/phase-2-summary.md
storage/specs/<feature>/phase-3-summary.md
```

各フェーズ完了時にオーケストレーターが自動生成する。次フェーズのサブエージェントはStep 0でこれを読む。

```markdown
# Phase 1（要件定義）サマリ

## 生成結果
- 要件数: 5件（REQ-AUTH-001〜005）
- P0: 2件, P1: 2件, P2: 1件

## 修正履歴
- REQ-AUTH-001: P2→P0に変更（法規制対応のため必須化）
- REQ-AUTH-003: ユーザーの指示で「パスワードリセットは24時間有効」を追加

## レビュー警告
- ⚠️ REQ-AUTH-002と既存REQ-USER-003の機能重複の可能性あり。設計時に統合を検討すること

## 次フェーズへの申し送り
- ユーザーの主要関心: パスワードリセットフローの使いやすさ
- 認証方式はJWTを前提として設計すること（ユーザー確認済み）
```

**タイミング**: オーケストレーターがAgent()のサマリー返却を受け取った後、
ユーザー承認を得た時点で自動生成する。サマリーの内容 + レビュー結果 + ユーザーのやりとりを統合する。

#### 漏れリスク3: 並列タスク間の型・命名の分裂

**問題**: 並列実行されるimplement-agent同士は完全に独立しているため、
共有インターフェースの命名・型定義で分裂が発生する。
例: TSK-001が `getUserInfo()` と命名し、TSK-002が `fetchUserData()` と命名する。

**対策: 共有インターフェース事前定義**

```
storage/specs/<feature>/shared-interfaces.ts
```

Phase 3（タスク分解）で並列実行可能なタスクが特定された場合、tasks-agentが
共有インターフェースの型定義を事前に生成する。各implement-agentはこの定義に準拠して実装する。

```typescript
// storage/specs/user-authentication/shared-interfaces.ts
// このファイルは tasks-agent が自動生成。implement-agent は必ず準拠すること。

/** TSK-AUTH-001, TSK-AUTH-002 で共有するユーザー型 */
export interface User {
  id: string;
  email: string;
  passwordHash: string;
  createdAt: Date;
}

/** TSK-AUTH-001（認証サービス）が実装するインターフェース */
export interface AuthService {
  login(email: string, password: string): Promise<Result<AuthToken, AuthError>>;
  logout(token: string): Promise<Result<void, AuthError>>;
}

/** TSK-AUTH-002（パスワードリセット）が実装するインターフェース */
export interface PasswordResetService {
  requestReset(email: string): Promise<Result<void, ResetError>>;
  confirmReset(token: string, newPassword: string): Promise<Result<void, ResetError>>;
}
```

**タイミング**: tasks-agentがタスク分解の際に並列実行可能タスク（`(P)` マーカー付き）を
特定した時点で生成する。依存関係のないタスクが同じ型を扱う場合のみ生成する。

#### 情報漏れ防止の全体像

```
メイン会話（オーケストレーター）
│
├─ ユーザーの横断的指示を検出 → directives.md に書き出し
│
├─ Phase 1: Agent(requirements-agent)
│   ├─ Step 0: steering/ + spec.json + directives.md を読み込み
│   └─ → requirements.md を出力
│
├─ Phase 1 完了 → phase-1-summary.md を自動生成
│
├─ Phase 2: Agent(design-agent)
│   ├─ Step 0: steering/ + spec.json + directives.md + phase-1-summary.md + requirements.md を読み込み
│   └─ → design.md を出力
│
├─ Phase 2 完了 → phase-2-summary.md を自動生成
│
├─ Phase 3: Agent(tasks-agent)
│   ├─ Step 0: steering/ + spec.json + directives.md + phase-1,2-summary.md + requirements.md + design.md を読み込み
│   ├─ → tasks.md を出力
│   └─ → 並列タスクがある場合: shared-interfaces.ts を出力
│
├─ Phase 3 完了 → phase-3-summary.md を自動生成
│
├─ Phase 4: Agent(implement-agent) × N（並列）
│   ├─ Step 0: steering/ + spec.json + directives.md + phase-*-summary.md + tasks.md + design.md を読み込み
│   ├─ Step 0: shared-interfaces.ts があれば読み込み（準拠必須）
│   └─ → ソースコード + テストコード を出力
│
└─ Phase 5: Agent(validate-agent)
    ├─ Step 0: 全ファイルを読み込み
    └─ → 検証レポート を出力
```

---

## 6. 実装計画

### 6.1 作成するファイル一覧

```
.claude/
├── agents/musubix/                ← 新規作成（5ファイル）
│   ├── requirements-agent.md      ← EARS要件生成サブエージェント
│   ├── design-agent.md            ← C4設計生成サブエージェント
│   ├── tasks-agent.md             ← タスク分解サブエージェント（shared-interfaces.ts生成含む）
│   ├── implement-agent.md         ← TDD実装サブエージェント
│   └── validate-agent.md          ← 検証サブエージェント
├── skills/
│   └── musubix-sdd-orchestrator/  ← 新規追加（1ファイル）
│       └── SKILL.md               ← オーケストレーター（directives.md記録 + phase-*-summary.md生成）
├── skills/                        ← 既存維持（変更なし）
│   ├── musubix-sdd-workflow/      ← 既存のまま（ガイダンス用途）
│   └── ...
└── prompts/                       ← 既存維持（変更なし）

実行時に生成されるファイル（storage/specs/<feature>/以下）:
├── spec.json                      ← 状態管理（filesフィールドに各ファイルパスを記録）
├── directives.md                  ← ユーザーの横断的指示（オーケストレーターが記録）
├── phase-1-summary.md             ← Phase 1完了時のサマリ（オーケストレーターが生成）
├── phase-2-summary.md             ← Phase 2完了時のサマリ
├── phase-3-summary.md             ← Phase 3完了時のサマリ
├── shared-interfaces.ts           ← 並列タスク用の共有型定義（tasks-agentが生成、該当時のみ）
├── requirements.md                ← 要件書（requirements-agentが出力）
├── design.md                      ← 設計書（design-agentが出力）
└── tasks.md                       ← タスク分解書（tasks-agentが出力）
```

**合計**: エージェント5ファイル + スキル1ファイル = **6ファイル新規作成**

### 6.2 各エージェントの設計

全エージェントに共通する **Step 0（コンテキスト保証ステップ）** を定義する。
これにより、オーケストレーター経由でも単独呼び出しでも、必要なコンテキストが確実に読み込まれる。

#### 6.2.0 全エージェント共通: Step 0（コンテキスト保証）

```markdown
### Step 0: コンテキスト読み込み

以下のファイルを必ず読み込むこと。このステップは省略不可。

1. **プロジェクト方針**（必須）:
   - Glob(`steering/*.md`) → 全ファイルをRead
   - steering/rules/constitution.md は特に重要（9憲法条項）

2. **状態ファイル**（存在する場合）:
   - Read(`storage/specs/<feature>/spec.json`)
   - spec.jsonが存在しない場合: 新規作成モードとして動作
   - spec.jsonが存在する場合: phase と approvals を確認

3. **ユーザーディレクティブ**（存在する場合）:
   - Read(`storage/specs/<feature>/directives.md`)
   - ユーザーが会話中に伝えた横断的指示（セキュリティ重視、技術選定等）が記録されている
   - 存在しない場合はスキップ（省略可）

4. **前フェーズサマリ**（存在する場合）:
   - Glob(`storage/specs/<feature>/phase-*-summary.md`) → 全ファイルをRead
   - 前フェーズのレビュー結果、修正経緯、注意事項が記録されている
   - 存在しない場合はスキップ（省略可）

5. **前提成果物**（エージェントごとに異なる）:
   - 各エージェントの「必須入力ファイル」を参照
   - ファイルが存在しない場合の動作は「前提条件検証」に従う

6. **共有インターフェース定義**（implement-agentの並列実行時のみ）:
   - Read(`storage/specs/<feature>/shared-interfaces.ts`)
   - 並列タスク間で共有する型定義。存在する場合は必ず準拠すること
   - 存在しない場合はスキップ（省略可）

### 前提条件検証

| 状況 | 動作 |
|------|------|
| 前フェーズの成果物が存在しない | エラーで停止 + 必要な手順を案内 |
| 前フェーズの成果物が存在するが未承認 | 警告付きで続行 |
| 前フェーズの成果物が存在し承認済み | 通常実行 |
| spec.jsonが存在しない | 新規作成モードまたはspec.jsonなしモードで動作 |
```

#### 6.2.1 `agents/musubix/requirements-agent.md`

```yaml
---
name: requirements-agent
description: EARS形式で要件ドキュメントを生成・修正する。要件定義、要件書作成、EARS形式変換を依頼された時に使用。
tools: Read, Write, Edit, Glob, Grep
model: inherit
skills: musubix-ears-validation
---
```

**`skills: musubix-ears-validation`** により、既存のEARS検証スキルの全知識がプリロードされる。
エージェント本文にEARS形式のルールを再記述する必要がない。

**必須入力ファイル**: steering/*.md
**任意入力ファイル**: storage/specs/\<feature\>/requirements.md（存在時は修正モード）
**出力ファイル**: storage/specs/\<feature\>/requirements.md, spec.json

**動作モード**:
| モード | 条件 | 動作 |
|--------|------|------|
| **新規生成** | requirements.mdが存在しない | 要件を新規作成 |
| **修正・追加** | requirements.mdが既に存在する | 既存要件を読み込み、指示に基づいて修正・追加 |

**処理ステップ**:
1. **Step 0**: コンテキスト保証（上記共通ステップ）
2. **EARS要件生成/修正**: 5パターン（Ubiquitous, Event-driven, State-driven, Unwanted, Optional）
3. **セルフレビュー**: EARS形式準拠、完全性、テスト可能性をチェック
4. **ファイル出力**: requirements.md 書き込み + spec.json 更新
5. **サマリー返却**: 生成/修正した要件数、レビュー結果、次ステップを150-300語で返す

**MUSUBIX固有の要素**:
- 要件IDは `REQ-<PREFIX>-NNN` 形式
- 優先度（P0/P1/P2）を付与
- 第IV条（EARS Format）準拠チェック

#### 6.2.2 `agents/musubix/design-agent.md`

```yaml
---
name: design-agent
description: C4モデルで設計ドキュメントを生成・修正する。設計、アーキテクチャ、C4ダイアグラム作成を依頼された時に使用。
tools: Read, Write, Edit, Glob, Grep, WebSearch, WebFetch
model: inherit
skills: musubix-c4-design
---
```

**`skills: musubix-c4-design`** により、C4モデルの知識がプリロードされる。

**必須入力ファイル**: steering/*.md, storage/specs/\<feature\>/requirements.md
**任意入力ファイル**: storage/specs/\<feature\>/design.md（存在時は修正モード）
**出力ファイル**: storage/specs/\<feature\>/design.md, spec.json

**前提条件**: requirements.mdが存在すること。存在しない場合はエラーで停止し
「先にrequirements-agentを実行するか、要件ドキュメントを作成してください」と案内する。

**動作モード**:
| モード | 条件 | 動作 |
|--------|------|------|
| **新規生成** | design.mdが存在しない | 設計を新規作成 |
| **修正・更新** | design.mdが既に存在する | 既存設計を読み込み、指示に基づいて修正 |

**処理ステップ**:
1. **Step 0**: コンテキスト保証 + requirements.md必須チェック
2. **設計生成/修正**: C4モデル（Context → Container → Component → Code）で構造化
3. **セルフレビュー**: 要件カバレッジ、SOLID原則、設計パターン適用をチェック
4. **ファイル出力**: design.md 書き込み + spec.json 更新
5. **サマリー返却**: 設計概要、適用パターン、トレーサビリティを返す

**MUSUBIX固有の要素**:
- 設計IDは `DES-<PREFIX>-NNN` 形式
- REQ-* → DES-* のトレーサビリティ明記
- 設計パターン検出（Repository, Service, Factory等）

#### 6.2.3 `agents/musubix/tasks-agent.md`

```yaml
---
name: tasks-agent
description: 設計から実装タスクを分解する。タスク分解、実装計画、作業分割を依頼された時に使用。
tools: Read, Write, Edit, Glob, Grep
model: inherit
skills: musubix-traceability
---
```

**`skills: musubix-traceability`** により、トレーサビリティの知識がプリロードされる。

**必須入力ファイル**: steering/*.md, requirements.md, design.md
**任意入力ファイル**: tasks.md（存在時はマージモード）
**出力ファイル**: storage/specs/\<feature\>/tasks.md, spec.json

**前提条件**: requirements.mdとdesign.mdが存在すること。

**動作モード**:
| モード | 条件 | 動作 |
|--------|------|------|
| **新規生成** | tasks.mdが存在しない | タスクを新規作成 |
| **マージ** | tasks.mdが既に存在する | 既存タスクを読み込み、不足分を追加・既存を改善 |

**処理ステップ**:
1. **Step 0**: コンテキスト保証 + requirements.md/design.md必須チェック
2. **タスク分解/マージ**: 設計の各コンポーネントを実装タスクに分解
3. **依存関係分析**: タスク間の依存関係を特定し、並列実行可能なタスクに `(P)` マーカーを付与
4. **共有インターフェース生成**: 並列タスクが同じ型を扱う場合、`shared-interfaces.ts` を生成
5. **セルフレビュー**: 粒度（4時間以内）、受入基準、依存関係をチェック
6. **ファイル出力**: tasks.md + shared-interfaces.ts（該当時） + spec.json 更新
7. **サマリー返却**: タスク数、依存関係図、並列実行可能なタスク、共有インターフェースの有無を返す

**MUSUBIX固有の要素**:
- タスクIDは `TSK-<PREFIX>-NNN` 形式
- DES-* → TSK-* のトレーサビリティ明記
- 並列実行可能なタスクに `(P)` マーカー
- `(P)` タスクが共通の型を扱う場合、`shared-interfaces.ts` を自動生成

#### 6.2.4 `agents/musubix/implement-agent.md`

```yaml
---
name: implement-agent
description: TDDでコードを実装する。コード実装、バグ修正、リファクタリング、テスト追加を依頼された時に使用。
tools: Read, Write, Edit, Bash, Glob, Grep, WebSearch, WebFetch
model: inherit
skills: musubix-code-generation, musubix-test-generation, musubix-best-practices
---
```

**`skills`** により、コード生成・テスト生成・ベストプラクティスの知識がプリロードされる。
3つのスキルの知見をエージェント本文に複製する必要がない。

**必須入力ファイル**: steering/*.md
**条件付き入力ファイル**: tasks.md, design.md（SDDワークフロー内の場合）
**任意入力ファイル**: 既存ソースコード、テストファイル
**出力ファイル**: ソースコード、テストコード、tasks.md（タスク完了マーク）

**前提条件**: 柔軟。以下の2つのモードで動作する：

**動作モード**:
| モード | 条件 | 動作 |
|--------|------|------|
| **SDDモード** | tasks.mdが存在する | 指定されたタスクをTDDで実装。design.mdも参照 |
| **ダイレクトモード** | tasks.mdが存在しない | プロンプトの指示内容に基づいて直接実装。バグ修正やリファクタリング等 |

**処理ステップ**:
1. **Step 0**: コンテキスト保証。SDDモードならtasks.md/design.md読み込み、ダイレクトモードなら既存コード読み込み
2. **TDDサイクル**:
   - Red: テスト作成
   - Green: 最小限の実装
   - Blue: リファクタリング
3. **テスト実行**: `npm test` で通過確認
4. **メタデータ更新**: SDDモードならtasks.mdのチェックマーク更新
5. **サマリー返却**: 実装ファイル、テスト結果、残タスク（SDDモード）を返す

#### 6.2.5 `agents/musubix/validate-agent.md`

```yaml
---
name: validate-agent
description: トレーサビリティとポリシーを検証する。検証、品質チェック、整合性確認を依頼された時に使用。
tools: Read, Bash, Glob, Grep
model: inherit
skills: musubix-traceability
---
```

**必須入力ファイル**: steering/*.md
**条件付き入力ファイル**: requirements.md, design.md, tasks.md（存在するもののみ）
**出力**: 検証レポート（サマリーとして返却）

**動作モード**:
| モード | 条件 | 動作 |
|--------|------|------|
| **フル検証** | 全仕様ファイル（REQ/DES/TSK）が存在 | 完全なトレーサビリティチェーン検証 |
| **部分検証** | 一部のファイルのみ存在 | 存在するファイル間のトレーサビリティを検証 |
| **コードのみ検証** | 仕様ファイルなし | テスト実行と9憲法条項チェックのみ |

**処理ステップ**:
1. **Step 0**: コンテキスト保証。存在する仕様ファイルを列挙して読み込み
2. **トレーサビリティ検証**: 存在するファイル間の REQ-* → DES-* → TSK-* → コード → テスト
3. **テスト実行**: `npm test` で全テスト通過確認
4. **9憲法条項チェック**: 各条項への準拠状態
5. **サマリー返却**: 合格/不合格、カバレッジ、未対応項目を返す

### 6.3 オーケストレーター・スキル

#### `skills/musubix-sdd-orchestrator/SKILL.md`

```yaml
---
name: musubix-sdd-orchestrator
description: SDDワークフロー全体をサブエージェントで一括実行するオーケストレーター。
  コンテキスト分離により効率的にフェーズを進行する。
  新機能を要件定義から実装まで通して行う場合に使用。
---
```

**重要**: `context: fork` は**指定しない**。オーケストレーターはメインコンテキストで実行し、
各フェーズでAgent()を呼び出してサブエージェントに委譲する。
（`context: fork`を指定すると、サブエージェントからAgent()を呼べなくなるため）

**処理フロー**:
```
ユーザー: 「認証機能を実装して。セキュリティは重視してほしい」
  ↓
Claudeが musubix-sdd-orchestrator を自動呼び出し（または /musubix-sdd-orchestrator で手動呼び出し）
  ↓
Phase 0: 初期化（直接実行）
  ├─ feature名をケバブケースに変換
  ├─ storage/specs/<feature>/ ディレクトリ作成
  ├─ spec.json テンプレート生成
  └─ ユーザーの横断的指示を検出 → directives.md に書き出し
  ↓
Phase 1: Agent(requirements-agent) → サマリー返却
  ↓
ユーザー確認（承認 or 修正指示）
  ├─ 横断的指示があれば directives.md に追記
  └─ phase-1-summary.md を自動生成（レビュー結果、修正経緯、注意事項）
  ↓
Phase 2: Agent(design-agent) → サマリー返却
  ↓
ユーザー確認（承認 or 修正指示）
  ├─ 横断的指示があれば directives.md に追記
  └─ phase-2-summary.md を自動生成
  ↓
Phase 3: Agent(tasks-agent) → サマリー返却
  ↓
ユーザー確認（承認 or 修正指示）
  ├─ phase-3-summary.md を自動生成
  └─ 並列タスクがある場合: shared-interfaces.ts を確認（tasks-agentが生成済み）
  ↓
Phase 4: Agent(implement-agent) → サマリー返却
  ↓
Phase 5: Agent(validate-agent) → サマリー返却
```

**並列実行の活用**:
- Phase 1〜3は順次実行（前フェーズの出力が次フェーズの入力）
- Phase 4では、タスク間に依存関係がない場合に**複数のimplement-agentをバックグラウンドで並列起動**可能
- Phase 5はPhase 4完了後に実行

### 6.4 利用パターン別の動作詳細

#### パターンA: 全工程一括（新機能開発）

```
ユーザー: 「ユーザー認証機能を実装して」
  ↓
Claude: musubix-sdd-orchestrator を呼び出し
  ↓ Phase 0〜5 を順次実行（上記フロー参照）

メインコンテキストの消費:
  ├─ オーケストレーターの指示テキスト
  ├─ 各フェーズのサマリー × 5（150-300語 × 5 = 750-1500語）
  └─ ユーザーとの確認やりとり
  → 合計: 非常に軽量。各フェーズの詳細はサブエージェント内で消費
```

#### パターンB: 特定フェーズ単独実行

```
ユーザー: 「昨日作った要件をもとに設計を作って」
  ↓
Claude: ユーザーの意図を理解し、Agent()でdesign-agentを直接呼び出し
  ↓
design-agent:
  ├─ Step 0: steering/*.md 読み込み
  ├─ Step 0: spec.json 読み込み → phase: "requirements-approved" を確認
  ├─ Step 0: requirements.md 読み込み（前提条件OK）
  ├─ 設計生成
  └─ サマリー返却

メインコンテキストの消費:
  ├─ ユーザーの指示
  ├─ design-agentのサマリー（150-300語）
  └─ フォローアップの会話
  → 合計: 非常に軽量
```

**重要**: パターンBでは**オーケストレーター・スキルは不要**。
Claudeがユーザーの意図を理解し、適切なエージェントをAgent()で直接呼び出す。
これは`.claude/agents/`に定義されたエージェントがClaude Codeにとって
「利用可能なサブエージェントタイプ」として認識されるため可能になる。

```
パターンBの他の例:

ユーザー: 「この要件書をEARS形式に直して」
  → Agent(requirements-agent) を修正モードで呼び出し

ユーザー: 「タスクの分解をお願い」
  → Agent(tasks-agent) を呼び出し

ユーザー: 「テストと実装の整合性を確認して」
  → Agent(validate-agent) を呼び出し
```

#### パターンC: 修正・部分作業

```
ユーザー: 「このバグを修正して」
  ↓
Claude: 変更規模を判断
  ├─ 小規模（数ファイル、明確な修正）→ メインコンテキストで直接修正
  └─ 大規模（多ファイル、テスト追加必要）→ Agent(implement-agent) をダイレクトモードで呼び出し

implement-agent（ダイレクトモード）:
  ├─ Step 0: steering/*.md 読み込み
  ├─ Step 0: spec.jsonが存在しない → ダイレクトモードで動作
  ├─ 既存コードとテストを読み込み
  ├─ TDDでバグ修正
  └─ サマリー返却
```

**パターンCの判断基準**:

| 作業内容 | 規模 | 推奨方式 |
|---------|------|---------|
| タイポ修正、1-2行の変更 | 極小 | メインコンテキストで直接 |
| バグ修正（原因特定済み） | 小 | メインコンテキストで直接 |
| バグ修正（調査必要） | 中 | Agent(implement-agent) ダイレクトモード |
| テスト追加（1-2ファイル） | 小 | メインコンテキストで直接 |
| テスト追加（多数ファイル） | 大 | Agent(implement-agent) ダイレクトモード |
| リファクタリング | 中〜大 | Agent(implement-agent) ダイレクトモード |
| 新機能追加（小規模） | 小 | メインコンテキストで直接、または必要なフェーズのみ |
| 新機能追加（中〜大規模） | 大 | オーケストレーター（パターンA） |

**サブエージェント委譲のオーバーヘッド**: 各エージェントはStep 0でsteering/を読み込むため、
約5-10秒のオーバーヘッドがある。小規模な変更ではこのオーバーヘッドの方が大きくなるため、
メインコンテキストで直接実行した方が効率的。

### 6.5 spec.jsonの形式

各機能のメタデータ管理ファイル：

```json
{
  "feature": "user-authentication",
  "description": "ユーザー認証機能の追加",
  "created_at": "2026-02-23T10:00:00Z",
  "updated_at": "2026-02-23T12:00:00Z",
  "phase": "requirements-generated",
  "approvals": {
    "requirements": { "generated": true, "approved": false },
    "design": { "generated": false, "approved": false },
    "tasks": { "generated": false, "approved": false }
  },
  "ids": {
    "requirements": ["REQ-AUTH-001", "REQ-AUTH-002"],
    "designs": ["DES-AUTH-001"],
    "tasks": ["TSK-AUTH-001", "TSK-AUTH-002"]
  },
  "files": {
    "directives": "directives.md",
    "phaseSummaries": ["phase-1-summary.md"],
    "sharedInterfaces": null
  }
}
```

**`files`フィールド**: 各サブエージェントがStep 0でどのファイルを読むべきか判断するためのメタデータ。
- `directives`: ユーザーディレクティブファイルのパス。存在しない場合は `null`
- `phaseSummaries`: 完了済みフェーズのサマリファイル一覧
- `sharedInterfaces`: 並列タスク用の共有インターフェースファイル。Phase 3完了後に設定される

### 6.6 既存スキルとの関係

| 既存スキル | 変更 | 導入後の役割 |
|-----------|------|-------------|
| musubix-sdd-workflow | **変更なし** | ガイダンス参照用として維持 |
| musubix-ears-validation | **変更なし** | EARS形式の確認用。requirements-agentが内部的に同じ知見を使用 |
| musubix-code-generation | **変更なし** | コード生成の参照用。implement-agentが内部的に同じ知見を使用 |
| musubix-c4-design | **変更なし** | C4設計の参照用。design-agentが内部的に同じ知見を使用 |
| musubix-test-generation | **変更なし** | テスト生成の参照用。implement-agentが内部的に同じ知見を使用 |
| その他8スキル | **変更なし** | そのまま維持 |

### 6.7 prompts/との関係

既存の12個のプロンプトファイル（`.claude/prompts/*.prompt.md`）は、SDDの各フェーズで
Claudeに詳細な指示を与えるためのものであり、**メインコンテキストで展開される**。

| prompts/ | 対応するエージェント | 関係 |
|---------|---------------------|------|
| `sdd-requirements.prompt.md` | `requirements-agent` | エージェント本文に統合可能（将来） |
| `sdd-design.prompt.md` | `design-agent` | エージェント本文に統合可能（将来） |
| `sdd-tasks.prompt.md` | `tasks-agent` | エージェント本文に統合可能（将来） |
| `sdd-implement.prompt.md` | `implement-agent` | エージェント本文に統合可能（将来） |
| `sdd-test.prompt.md` | `implement-agent` | テスト生成はimplement-agentが担当 |
| `sdd-validate.prompt.md` | `validate-agent` | エージェント本文に統合可能（将来） |
| `sdd-review.prompt.md` | 各エージェントのセルフレビュー | エージェント内のレビューステップで代替 |
| `sdd-security.prompt.md` | `validate-agent` | セキュリティチェックはvalidate-agentに含める |
| `sdd-steering.prompt.md` | 全エージェントのStep 0 | 各エージェントが自律的にsteering/を読み込む |
| `sdd-change-*.prompt.md`（3個） | 変更管理用（エージェント対象外） | 維持 |

**方針**: 今回の初期実装では**prompts/は変更しない**（既存のまま維持）。
エージェント導入後、prompts/の内容はエージェント本文に段階的に統合し、
将来的にprompts/を整理・削除することを検討する。
ただし`sdd-change-*.prompt.md`（変更管理）はエージェントの対象外であり、引き続き単独で使用する。

**使い分けガイド**:

| ユースケース | 使うもの | 理由 |
|-------------|---------|------|
| 新機能を要件→実装まで通して開発 | `/musubix-sdd-orchestrator` | オーケストレーターで全フェーズ一括。コンテキスト分離 |
| 特定フェーズだけ実行（設計だけ、等） | メイン会話からAgent()で直接エージェント呼び出し | エージェントがStep 0で自動的に必要なコンテキストを読み込む |
| バグ修正、小規模な変更 | メインコンテキストで直接（必要ならimplement-agent委譲） | オーバーヘッドを避ける |
| EARS形式の書き方を確認 | `musubix-ears-validation` スキル | ガイダンスとして参照 |
| C4モデルの作り方を確認 | `musubix-c4-design` スキル | ガイダンスとして参照 |
| ベストプラクティスを確認 | `musubix-best-practices` スキル | 学習済みパターンの参照 |

---

## 7. コンテキスト効率の改善効果

### 7.1 改善前（現状）

```
メインコンテキスト:
├─ CLAUDE.md（約50行/2KB）
├─ steering/*.md（プロジェクト規模による）
├─ musubix-sdd-workflow スキル（211行）
├─ Phase 1: 要件定義の全詳細（steering/再読み込み含む）
├─ Phase 2: 設計の全詳細（steering/再読み込み含む）
├─ Phase 3: タスク分解の全詳細
├─ Phase 4: 実装の全詳細
├─ Phase 5: 検証の全詳細
└─ → 各フェーズの成果物とsteering/が重複蓄積し、トークン上限に到達するリスク大
```

### 7.2 改善後（サブエージェント導入）

```
メインコンテキスト:
├─ CLAUDE.md（約50行/2KB）
├─ オーケストレーターの指示
├─ Phase 1 サマリー（150-300語）
├─ ユーザー確認
├─ Phase 2 サマリー（150-300語）
├─ ユーザー確認
├─ Phase 3 サマリー（150-300語）
├─ ユーザー確認
├─ Phase 4 サマリー（150-300語）
├─ Phase 5 サマリー（150-300語）
└─ → 各フェーズの詳細はサブエージェント内で消費済み

サブエージェント（Phase 1 - 独立コンテキスト）:
├─ steering/*.md
├─ EARS検証ルール
├─ 要件生成の詳細
└─ → 完了後に破棄

サブエージェント（Phase 2 - 独立コンテキスト）:
├─ steering/*.md
├─ requirements.md
├─ C4設計ルール
└─ → 完了後に破棄

... 以下同様
```

**概算トークン削減効果**:
- 各フェーズのsteering/読み込み: サブエージェント側で消費（メインに蓄積しない）
- 各フェーズの出力詳細: サブエージェント側で消費（メインには150-300語のみ）
- 推定: メインコンテキストのトークン消費を **60-70%削減**

### 7.3 並列実行の活用

Phase 4（実装）で、依存関係のないタスクをバックグラウンドモードで並列実行する：

```
オーケストレーター（メインコンテキスト）:
│
├─ 依存関係を分析: TSK-AUTH-001, TSK-AUTH-002 は独立、TSK-AUTH-003 は TSK-001 に依存
│
├─ 並列実行（バックグラウンドモード）:
│   ├─ Agent(implement-agent, run_in_background=true)  ← TSK-AUTH-001
│   └─ Agent(implement-agent, run_in_background=true)  ← TSK-AUTH-002
│   → 2つのサブエージェントが同時に独立コンテキストで実行
│
├─ 結果収集: 両方の完了を待ち、サマリーを取得
│
├─ 順次実行（フォアグラウンドモード）:
│   └─ Agent(implement-agent)  ← TSK-AUTH-003（TSK-001の出力に依存）
│
└─ 全タスクのサマリーをまとめてユーザーに返却
```

**並列実行の前提条件**:
- タスク間にファイル競合がないこと（同一ファイルへの同時書き込みを回避）
- tasks-agentが依存関係を分析し、並列実行可能なタスクに `(P)` マーカーを付与済みであること
- 並列タスクが共通の型を扱う場合、`shared-interfaces.ts` が生成済みであること（型・命名の分裂防止）
- バックグラウンドモードでは事前の権限承認が必要（ユーザーに確認ダイアログが表示される）

---

## 8. 実装手順

### Phase 1: エージェント定義作成

| # | 作業 | ファイル |
|---|------|---------|
| 1 | agents/ディレクトリ作成 | `.claude/agents/musubix/` |
| 2 | requirements-agent作成 | `.claude/agents/musubix/requirements-agent.md` |
| 3 | design-agent作成 | `.claude/agents/musubix/design-agent.md` |
| 4 | tasks-agent作成 | `.claude/agents/musubix/tasks-agent.md` |
| 5 | implement-agent作成 | `.claude/agents/musubix/implement-agent.md` |
| 6 | validate-agent作成 | `.claude/agents/musubix/validate-agent.md` |

### Phase 2: オーケストレーター作成

| # | 作業 | ファイル |
|---|------|---------|
| 7 | オーケストレーター・スキル作成 | `.claude/skills/musubix-sdd-orchestrator/SKILL.md` |

### Phase 3: 動作検証

| # | 作業 |
|---|------|
| 8 | requirements-agentの単体テスト（テスト用featureで要件生成を確認） |
| 9 | design-agentの単体テスト |
| 10 | tasks-agentの単体テスト |
| 11 | implement-agentの単体テスト |
| 12 | validate-agentの単体テスト |
| 13 | オーケストレーター全体テスト |

### Phase 4: ドキュメント更新

| # | 作業 | ファイル |
|---|------|---------|
| 14 | CLAUDE.mdにオーケストレーターの説明を追記 | `CLAUDE.md` |

---

## 9. リスクと対策

| リスク | 影響 | 対策 |
|--------|------|------|
| サブエージェントがsteering/を正しく読めない | 不整合な出力 | エージェント定義にStep 0（ファイルパターン展開）を必須化 |
| サブエージェントのサマリーが不十分 | メインコンテキストで判断できない | サマリーのフォーマットを厳密に定義（生成物、レビュー結果、次ステップ） |
| 既存スキルとの混乱 | ユーザーがどちらを使うか迷う | CLAUDE.mdに使い分けを明記。オーケストレーター=自動実行、スキル=ガイダンス |
| 並列実装でファイル競合 | 同一ファイルへの同時書き込み | 依存関係分析でファイル競合がないタスクのみ並列化 |
| 並列タスク間の型・命名分裂 | 同じインターフェースに異なる命名・型定義 | tasks-agentが`shared-interfaces.ts`を事前生成し、implement-agentに準拠を指示 |
| ユーザーの横断的指示がサブエージェントに伝わらない | 意図しない技術選定・方針の不整合 | `directives.md`にリアルタイム記録、Step 0で読み込み |
| フェーズ間の意思決定コンテキストが消失 | レビュー警告の無視、修正理由の喪失 | `phase-*-summary.md`をフェーズ完了時に自動生成、Step 0で読み込み |
| `context: fork`の挙動変更 | Claude Codeのアップデートで挙動が変わる可能性 | エージェント定義は`.claude/agents/`に配置（公式サポートされる形式） |

---

## 10. 成功基準

### コンテキスト管理
- [ ] 各フェーズのサブエージェントが独立したコンテキストで実行される
- [ ] メインコンテキストにはサマリー（150-300語）のみが返却される
- [ ] 長いSDDワークフロー（全5フェーズ）でもコンテキストが枯渇しない

### コンテキスト保証（漏れのない読み込み）
- [ ] 各エージェントがStep 0でsteering/*.mdを確実に読み込む
- [ ] 各エージェントがspec.jsonから現在の状態を正しく検出する
- [ ] 各エージェントがdirectives.md（存在する場合）を読み込み、横断的指示を反映する
- [ ] 各エージェントがphase-*-summary.md（存在する場合）を読み込み、前フェーズの注意事項を把握する
- [ ] 前フェーズの成果物が存在しない場合、エラーメッセージで適切に案内する
- [ ] 前フェーズの成果物が未承認の場合、警告付きで続行する

### 情報漏れ防止
- [ ] オーケストレーターがユーザーの横断的指示をdirectives.mdに記録する
- [ ] 各フェーズ完了時にphase-*-summary.mdが自動生成される
- [ ] 並列タスクがある場合、tasks-agentがshared-interfaces.tsを生成する
- [ ] implement-agentがshared-interfaces.tsに準拠して実装する

### 利用パターン対応
- [ ] パターンA（全工程一括）: オーケストレーターが正しく全フェーズを実行する
- [ ] パターンB（特定フェーズ単独）: 各エージェントが単独でも正しく動作する
- [ ] パターンC（修正・部分作業）: implement-agentがダイレクトモードで動作する
- [ ] 翌日に別セッションで続行しても、spec.jsonから状態を復元して正しく動作する

### 並列実行
- [ ] 依存関係のないタスクが同時に処理される
- [ ] ファイル競合が発生しない

### 既存資産との共存
- [ ] 既存の13スキルが引き続き動作する
- [ ] 既存の12プロンプトが引き続き動作する

---

## 付録A: cc-sddとの実装方式の比較

| 要素 | cc-sdd | MUSUBIX（推奨案） |
|------|--------|------------------|
| コマンド定義場所 | `.claude/commands/kiro/` | **不要**（skillsで代替） |
| エージェント定義場所 | `.claude/agents/kiro/` | `.claude/agents/musubix/` |
| オーケストレーター | コマンド（spec-quick.md） | **スキル**（musubix-sdd-orchestrator） |
| ガイダンス | なし | 既存13スキル（維持） |
| プロンプト | なし | 既存12プロンプト（維持） |
| 仕様ストレージ | `{{KIRO_DIR}}/specs/` | `storage/specs/`（既存活用） |
| プロジェクトメモリ | `steering/` | `steering/`（同じ） |
| 知識グラフ | なし | `@musubix/knowledge`（MUSUBIX固有の強み） |
| ポリシー検証 | なし | `@musubix/policy`（MUSUBIX固有の強み） |
| MCP統合 | なし | 107ツール（サブエージェント内から呼び出し可能） |

## 付録B: 用語整理

| 用語 | 意味 |
|------|------|
| **スキル（Skill）** | `.claude/skills/*/SKILL.md` で定義。スラッシュコマンドを作成する。ガイダンスまたは自動実行 |
| **プロンプト（Prompt）** | `.claude/prompts/*.prompt.md` で定義。AI向けの詳細な指示 |
| **エージェント（Agent）** | `.claude/agents/*/` で定義。サブエージェントとして独立コンテキストで実行 |
| **オーケストレーター** | 複数のサブエージェントを順次/並列に呼び出すスキル。自身は`context: fork`を使わない |
| **`context: fork`** | スキルのフロントマターオプション。指定するとそのスキルがサブエージェントとして実行される |
| **Agent()** | Claude CodeのAgent tool（旧Task tool、v2.1.63でリネーム）。サブエージェントを起動するためのネイティブ機能 |
