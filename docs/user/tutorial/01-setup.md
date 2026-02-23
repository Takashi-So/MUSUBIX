# チュートリアル Part 1: セットアップ

> 所要時間: 約5分

---

## 1. プロジェクトの作成

<details>
<summary>npmを使っている場合</summary>

```bash
mkdir equipment-management && cd equipment-management
npx musubix init . --name equipment-management
```

</details>

<details>
<summary>pnpmを使っている場合</summary>

```bash
mkdir equipment-management && cd equipment-management
pnpm dlx musubix init . --name equipment-management
```

</details>

### 出力結果

```json
{
  "success": true,
  "projectPath": "/path/to/equipment-management",
  "message": "MUSUBIX project 'equipment-management' initialized successfully!"
}
```

## 2. 生成されたファイルの確認

以下のファイル・ディレクトリが自動生成されます：

```
equipment-management/
├── musubix.config.json                # プロジェクト設定
├── AGENTS.md                          # GitHub Copilot向けAI指示ファイル
├── CLAUDE.md                          # Claude Code向けAI指示ファイル
│
├── steering/                          # プロジェクトメモリ
│   ├── rules/
│   │   └── constitution.md            # 9つの憲法条項
│   ├── product.md                     # プロダクトコンテキスト
│   ├── tech.md                        # 技術スタック定義
│   └── structure.md                   # プロジェクト構造定義
│
├── storage/                           # 成果物ストレージ
│   ├── specs/                         # 要件(REQ-*)・設計(DES-*)・タスク(TSK-*)
│   ├── archive/
│   │   └── .gitkeep
│   └── changes/
│       └── .gitkeep
│
├── .github/                           # GitHub Copilot向け
│   ├── copilot-instructions.md        # Copilot固有の追加指示
│   ├── prompts/                       # 12個のSDDプロンプトテンプレート
│   │   ├── sdd-requirements.prompt.md
│   │   ├── sdd-design.prompt.md
│   │   ├── sdd-tasks.prompt.md
│   │   ├── sdd-implement.prompt.md
│   │   ├── sdd-test.prompt.md
│   │   ├── sdd-review.prompt.md
│   │   ├── sdd-validate.prompt.md
│   │   ├── sdd-security.prompt.md
│   │   ├── sdd-steering.prompt.md
│   │   ├── sdd-change-init.prompt.md
│   │   ├── sdd-change-apply.prompt.md
│   │   └── sdd-change-archive.prompt.md
│   └── skills/                        # 20個のスキル定義
│       ├── musubix-sdd-workflow/
│       ├── musubix-ears-validation/
│       ├── musubix-c4-design/
│       ├── musubix-code-generation/
│       ├── musubix-test-generation/
│       ├── musubix-adr-generation/
│       ├── musubix-traceability/
│       ├── musubix-best-practices/
│       ├── musubix-domain-inference/
│       ├── musubix-technical-writing/
│       ├── checkpoint/
│       ├── build-fix/
│       ├── verification-loop/
│       ├── session-manager/
│       ├── learning-hooks/
│       ├── context-optimizer/
│       ├── codemap/
│       ├── e2e-runner/
│       ├── eval-harness/
│       └── refactor-cleaner/
│
└── .claude/                           # Claude Code向け
    ├── CLAUDE.md                      # Claude固有の追加指示
    ├── settings.json                  # Claude Code設定
    ├── prompts/                       # 12個のSDDプロンプトテンプレート（.github/と同内容）
    └── skills/                        # 20個のスキル定義（.github/と同内容）
```

### 各ディレクトリの役割

**`steering/`** — AIエージェントが開発判断をする際に参照する「プロジェクトメモリ」です。
- `constitution.md`: 品質ルール（9つの憲法条項）
- `product.md`: このプロジェクトが何を作るか（テンプレート）
- `tech.md`: 使用する技術スタック（テンプレート）
- `structure.md`: プロジェクトのディレクトリ構造（テンプレート）

**`storage/specs/`** — これからの作業で生成される要件(REQ-*)、設計(DES-*)、タスク(TSK-*)がここに保存されます。

**`.github/prompts/` `.claude/prompts/`** — SDDワークフローの各フェーズで使用されるプロンプトテンプレートです。AIエージェントが自動的に使用するので、手動で編集する必要はありません。

**`.github/skills/` `.claude/skills/`** — SDDスキル（要件検証、C4設計、コード生成等）と開発補助スキル（チェックポイント、ビルド修正、検証ループ等）の定義です。AIエージェントが自動的に使用します。

> `.github/` と `.claude/` は同じ内容が両方のAIエージェント用にコピーされています。使用するAIエージェントに応じて、対応するディレクトリが参照されます。

## 3. AIエージェントの準備

お使いのAIエージェントを起動してください。

**Claude Code の場合:**
```bash
# プロジェクトディレクトリでClaude Codeを起動
claude
```

**GitHub Copilot の場合:**
VS Code または Cursor でプロジェクトディレクトリを開いてください。

## 準備完了

これでセットアップは完了です。次のパートで要件定義を始めます。

---

**次へ**: [Part 2: 要件定義](02-requirements.md)
