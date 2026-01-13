# MUSUBIX v3.2.0 要件定義書
# Expert Delegation System - MUSUBIXの強みを活かしたマルチAI統合

**文書ID**: REQ-MUSUBIX-v3.2.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-13  
**ステータス**: Draft  
**準拠規格**: EARS（Easy Approach to Requirements Syntax）  
**参照文書**: claude-delegator比較分析, REQ-MUSUBIX-v3.1.0.md

---

## 1. 文書概要

### 1.1 目的

本文書は、MUSUBIX v3.2.0の機能要件をEARS形式で正式に定義する。claude-delegatorとの比較分析に基づき、MUSUBIXの強み（形式的手法、オントロジー推論、トレーサビリティ）を活かしながら、マルチAI委任機能を統合する。

### 1.2 背景

**claude-delegatorの強み**:
- 5つの専門エキスパート（Architect, Plan Reviewer, Scope Analyst, Code Reviewer, Security Analyst）
- Advisory/Implementation デュアルモード
- セマンティックトリガーによる自動ルーティング
- 7セクション委任フォーマット

**MUSUBIXの強み（活用対象）**:
- EARS形式要件定義（5パターン）
- 10憲法条項による開発規律
- オントロジー推論エンジン
- 形式検証（Z3/Lean4統合）
- トレーサビリティ（REQ→DES→TSK→Code）
- Git-native知識グラフ
- パターン学習（Wake-Sleep）

### 1.3 EARS パターン定義

| パターン | キーワード | 用途 | 構文 |
|----------|-----------|------|------|
| **Ubiquitous** | SHALL | システムが常に満たすべき要件 | THE \<system\> SHALL \<requirement\> |
| **Event-Driven** | WHEN...SHALL | イベント発生時の要件 | WHEN \<trigger\>, THE \<system\> SHALL \<response\> |
| **State-Driven** | WHILE...SHALL | 特定状態における要件 | WHILE \<state\>, THE \<system\> SHALL \<response\> |
| **Unwanted** | SHALL NOT | 禁止事項 | THE \<system\> SHALL NOT \<behavior\> |
| **Optional** | IF...THEN SHALL | 条件付き要件 | IF \<condition\>, THEN THE \<system\> SHALL \<response\> |

### 1.4 優先度定義

| 優先度 | 説明 | 対象バージョン |
|--------|------|---------------|
| **P0** | 必須 - リリースブロッカー | v3.2.0 |
| **P1** | 重要 - 可能な限り実装 | v3.2.0 |
| **P2** | 任意 - 時間があれば | v3.3.0+ |

### 1.5 要件ID体系

```
REQ-<カテゴリ>-<連番>
```

| カテゴリ | 説明 |
|---------|------|
| EXP | Expert Delegation（エキスパート委任） |
| TRG | Trigger Detection（トリガー検出） |
| PRV | Provider Integration（プロバイダー統合） |
| FMT | Delegation Format（委任フォーマット） |
| MCP | MCPツール統合 |
| NFR | 非機能要件 |

---

## 2. アーキテクチャ概要

### 2.1 新規パッケージ構成

```
packages/
└── expert-delegation/          # @nahisaho/musubix-expert-delegation (NEW!)
    ├── src/
    │   ├── experts/            # 専門家プロンプト定義
    │   │   ├── architect.ts
    │   │   ├── security-analyst.ts
    │   │   ├── code-reviewer.ts
    │   │   ├── ears-analyst.ts      # MUSUBIX独自
    │   │   ├── formal-verifier.ts   # MUSUBIX独自
    │   │   ├── ontology-reasoner.ts # MUSUBIX独自
    │   │   └── traceability-auditor.ts # MUSUBIX独自
    │   ├── triggers/           # セマンティックトリガー
    │   │   ├── semantic-router.ts
    │   │   └── intent-classifier.ts
    │   ├── formats/            # 委任フォーマット
    │   │   ├── delegation-template.ts
    │   │   └── ears-extended-format.ts
    │   ├── providers/          # AIプロバイダー
    │   │   ├── provider-interface.ts
    │   │   └── vscode-lm-provider.ts  # VS Code Language Model API
    │   ├── modes/              # 実行モード
    │   │   ├── advisory-mode.ts
    │   │   └── implementation-mode.ts
    │   └── retry/              # リトライ機構
    │       └── retry-handler.ts
    └── tests/
```

### 2.2 Expert一覧（7専門家）

| Expert | 役割 | 由来 | MUSUBIXオントロジーマッピング |
|--------|------|------|------------------------------|
| **Architect** | システム設計、アーキテクチャ決定 | claude-delegator | `sdd:DesignPhase` |
| **Security Analyst** | セキュリティ脆弱性分析 | claude-delegator | `sec:VulnerabilityAnalysis` |
| **Code Reviewer** | コード品質、バグ検出 | claude-delegator | `qa:CodeReview` |
| **Plan Reviewer** | 計画検証 | claude-delegator | `sdd:TaskPhase` |
| **EARS Analyst** | EARS形式要件分析 | MUSUBIX独自 | `ears:RequirementPattern` |
| **Formal Verifier** | 形式検証、Z3/Lean4 | MUSUBIX独自 | `formal:Verification` |
| **Ontology Reasoner** | オントロジー推論 | MUSUBIX独自 | `ont:InferenceEngine` |

---

## 3. 機能要件

---

### 3.1 Expert Delegation 基盤要件

---

#### REQ-EXP-001: エキスパート委任フレームワーク

| 属性 | 値 |
|------|-----|
| **ID** | REQ-EXP-001 |
| **名称** | エキスパート委任フレームワーク |
| **種別** | Ubiquitous |
| **優先度** | P0（必須） |
| **由来** | claude-delegator比較分析 |

**EARS要件**:

> THE Expert Delegation System SHALL 7つの専門エキスパート（Architect, Security Analyst, Code Reviewer, Plan Reviewer, EARS Analyst, Formal Verifier, Ontology Reasoner）を定義し,  
> AND THE System SHALL 各エキスパートの専門プロンプトを管理し,  
> AND THE System SHALL 委任タスクを適切なエキスパートにルーティングする。

**根拠**: claude-delegatorは5専門家だが、MUSUBIXは形式的手法の強みを活かして7専門家（+EARS Analyst, +Formal Verifier, +Ontology Reasoner）を提供する。

**受入基準**:
- [ ] AC-EXP-001-1: 7専門家の定義とプロンプトが存在する
- [ ] AC-EXP-001-2: `createExpert(type)` で専門家インスタンスを生成できる
- [ ] AC-EXP-001-3: 各専門家がオントロジークラスにマッピングされている
- [ ] AC-EXP-001-4: 専門家のメタデータ（得意分野、制約）が定義されている

**トレーサビリティ**: DES-EXP-001, TSK-EXP-001

---

#### REQ-EXP-002: Advisory/Implementation デュアルモード

| 属性 | 値 |
|------|-----|
| **ID** | REQ-EXP-002 |
| **名称** | Advisory/Implementation デュアルモード |
| **種別** | Event-Driven |
| **優先度** | P0（必須） |
| **由来** | claude-delegator: Dual mode |

**EARS要件**:

> WHEN ユーザーがエキスパートにタスクを委任した際,  
> THE System SHALL タスク種別を分析し,  
> AND IF タスクが分析・レビュー・推奨である場合 THEN THE System SHALL Advisoryモード（read-only）で実行し,  
> AND IF タスクが変更・修正・実装である場合 THEN THE System SHALL Implementationモード（workspace-write）で実行する。

**根拠**: claude-delegatorのデュアルモードは安全性と実用性のバランスに優れている。MUSUBIXでも採用する。

**受入基準**:
- [ ] AC-EXP-002-1: `Advisory` モードで read-only 操作のみ許可される
- [ ] AC-EXP-002-2: `Implementation` モードで書き込み操作が許可される
- [ ] AC-EXP-002-3: タスク種別に応じてモードが自動選択される
- [ ] AC-EXP-002-4: モードの明示的な指定が可能

**トレーサビリティ**: DES-EXP-002, TSK-EXP-002

---

#### REQ-EXP-003: MUSUBIX独自エキスパート - EARS Analyst

| 属性 | 値 |
|------|-----|
| **ID** | REQ-EXP-003 |
| **名称** | EARS Analyst エキスパート |
| **種別** | Ubiquitous |
| **優先度** | P0（必須） |
| **由来** | MUSUBIXの強み活用 |

**EARS要件**:

> THE EARS Analyst Expert SHALL 自然言語の要件記述をEARS形式に変換し,  
> AND THE Expert SHALL 5つのEARSパターン（Ubiquitous, Event-Driven, State-Driven, Unwanted, Optional）を識別し,  
> AND THE Expert SHALL 要件の曖昧性・不完全性を検出し,  
> AND THE Expert SHALL 既存要件との整合性を検証する。

**根拠**: MUSUBIXはEARS形式に強みを持つ。この知識を専門エキスパートとして委任可能にする。

**受入基準**:
- [ ] AC-EXP-003-1: 自然言語 → EARS変換の精度が90%以上
- [ ] AC-EXP-003-2: 5つのEARSパターンを正確に識別できる
- [ ] AC-EXP-003-3: 曖昧な要件に対して改善提案を生成できる
- [ ] AC-EXP-003-4: 既存REQ-*との重複・矛盾を検出できる

**トレーサビリティ**: DES-EXP-003, TSK-EXP-003

---

#### REQ-EXP-004: MUSUBIX独自エキスパート - Formal Verifier

| 属性 | 値 |
|------|-----|
| **ID** | REQ-EXP-004 |
| **名称** | Formal Verifier エキスパート |
| **種別** | Ubiquitous |
| **優先度** | P1（重要） |
| **由来** | MUSUBIXの強み活用 |

**EARS要件**:

> THE Formal Verifier Expert SHALL 形式仕様を解析し,  
> AND THE Expert SHALL Z3 SMTソルバーを用いて充足可能性を検証し,  
> AND THE Expert SHALL Lean 4定理証明器と連携し,  
> AND THE Expert SHALL EARS要件をSMT-LIB形式に変換する。

**根拠**: MUSUBIXはformal-verifyパッケージでZ3/Lean4統合を持つ。これを専門エキスパートとして委任可能にする。

**受入基準**:
- [ ] AC-EXP-004-1: EARS → SMT-LIB変換が正常に動作する
- [ ] AC-EXP-004-2: Z3による充足可能性検証が実行できる
- [ ] AC-EXP-004-3: Lean 4証明ファイルを生成できる
- [ ] AC-EXP-004-4: 検証結果を人間可読な形式で説明できる

**トレーサビリティ**: DES-EXP-004, TSK-EXP-004

---

#### REQ-EXP-005: MUSUBIX独自エキスパート - Ontology Reasoner

| 属性 | 値 |
|------|-----|
| **ID** | REQ-EXP-005 |
| **名称** | Ontology Reasoner エキスパート |
| **種別** | Ubiquitous |
| **優先度** | P1（重要） |
| **由来** | MUSUBIXの強み活用 |

**EARS要件**:

> THE Ontology Reasoner Expert SHALL 知識グラフに対してシンボリック推論を実行し,  
> AND THE Expert SHALL RDF/OWLベースのオントロジークエリを処理し,  
> AND THE Expert SHALL 推論結果に基づいて設計提案を生成し,  
> AND THE Expert SHALL 知識グラフの整合性を検証する。

**根拠**: MUSUBIXはontology-mcpパッケージでN3Store推論エンジンを持つ。これを専門エキスパートとして委任可能にする。

**受入基準**:
- [ ] AC-EXP-005-1: オントロジークエリが正常に実行できる
- [ ] AC-EXP-005-2: 推論ルールに基づく暗黙知識の導出ができる
- [ ] AC-EXP-005-3: 循環依存・矛盾を検出できる
- [ ] AC-EXP-005-4: 推論パスを説明可能な形式で出力できる

**トレーサビリティ**: DES-EXP-005, TSK-EXP-005

---

### 3.2 Trigger Detection 要件

---

#### REQ-TRG-001: セマンティックトリガー検出

| 属性 | 値 |
|------|-----|
| **ID** | REQ-TRG-001 |
| **名称** | セマンティックトリガー検出 |
| **種別** | Event-Driven |
| **優先度** | P0（必須） |
| **由来** | claude-delegator: Semantic Triggers |

**EARS要件**:

> WHEN ユーザーがメッセージを入力した際,  
> THE System SHALL メッセージの意図を分析し,  
> AND THE System SHALL 以下のトリガーパターンを検出する:  
> - "Is this secure?" → Security Analyst  
> - "How should I structure?" → Architect  
> - "Review this code" → Code Reviewer  
> - "要件を定義して" → EARS Analyst  
> - "形式検証して" → Formal Verifier  
> - "推論して" → Ontology Reasoner  
> AND THE System SHALL 適切なエキスパートを自動選択する。

**根拠**: claude-delegatorのセマンティックトリガーは優れたUXを提供する。MUSUBIXでも採用し、独自エキスパート用トリガーを追加する。

**受入基準**:
- [ ] AC-TRG-001-1: 7専門家それぞれに対応するトリガーパターンが定義されている
- [ ] AC-TRG-001-2: 日本語・英語両方のトリガーをサポートする
- [ ] AC-TRG-001-3: 曖昧な入力に対して確認プロンプトを表示する
- [ ] AC-TRG-001-4: 明示的なエキスパート指定が優先される

**トレーサビリティ**: DES-TRG-001, TSK-TRG-001

---

#### REQ-TRG-002: プロアクティブ委任判定

| 属性 | 値 |
|------|-----|
| **ID** | REQ-TRG-002 |
| **名称** | プロアクティブ委任判定 |
| **種別** | Event-Driven |
| **優先度** | P1（重要） |
| **由来** | claude-delegator: Proactive Delegation |

**EARS要件**:

> WHEN 同一問題に対して2回以上の修正試行が失敗した際,  
> THE System SHALL 自動的にArchitectエキスパートへのエスカレーションを提案し,  
> AND WHEN セキュリティ関連コードを検出した際,  
> THE System SHALL Security Analystによるレビューを推奨し,  
> AND WHEN EARS形式でない要件を検出した際,  
> THE System SHALL EARS Analystによる変換を推奨する。

**根拠**: claude-delegatorの「2回失敗後のエスカレーション」は実践的。MUSUBIXではEARS検出も追加する。

**受入基準**:
- [ ] AC-TRG-002-1: 修正試行回数が追跡され、2回失敗後にエスカレーション提案される
- [ ] AC-TRG-002-2: セキュリティパターン（auth, password, token等）検出時に推奨される
- [ ] AC-TRG-002-3: 非EARS形式の要件記述検出時に変換推奨される
- [ ] AC-TRG-002-4: 推奨を無視するオプションが提供される

**トレーサビリティ**: DES-TRG-002, TSK-TRG-002

---

### 3.3 Provider Integration 要件

---

#### REQ-PRV-001: VS Code Language Model API 統合

| 属性 | 値 |
|------|-----|
| **ID** | REQ-PRV-001 |
| **名称** | VS Code Language Model API 統合 |
| **種別** | Ubiquitous |
| **優先度** | P0（必須） |
| **由来** | VS Code/GitHub Copilot統合 |

**EARS要件**:

> THE System SHALL VS Code Language Model API（vscode.lm）を使用してLLMにアクセスし,  
> AND THE System SHALL GitHub Copilotの認証を再利用し,  
> AND THE System SHALL ユーザーに追加のAPIキー設定を要求しない,  
> AND THE System SHALL 利用可能なモデル一覧を動的に取得する。

**根拠**: VS Code LM APIを使用することで、GitHub Copilotユーザーは追加設定なしでExpert Delegationを利用可能。APIキー管理の複雑さを排除。

**技術詳細**:
```typescript
// VS Code Language Model API
import * as vscode from 'vscode';

// 利用可能なモデル取得
const models = await vscode.lm.selectChatModels({ family: 'gpt-4' });

// メッセージ送信
const messages = [vscode.LanguageModelChatMessage.User(prompt)];
const response = await model.sendRequest(messages, {}, token);
```

**受入基準**:
- [ ] AC-PRV-001-1: `vscode.lm` APIを使用したプロバイダーが実装されている
- [ ] AC-PRV-001-2: GitHub Copilot認証が自動的に使用される
- [ ] AC-PRV-001-3: 追加のAPIキー設定が不要
- [ ] AC-PRV-001-4: 利用可能なモデル一覧が取得できる
- [ ] AC-PRV-001-5: モデル選択UIが提供される

**トレーサビリティ**: DES-PRV-001, TSK-PRV-001

---

#### REQ-PRV-002: モデル選択・フォールバック

| 属性 | 値 |
|------|-----|
| **ID** | REQ-PRV-002 |
| **名称** | モデル選択・フォールバック |
| **種別** | Event-Driven |
| **優先度** | P1（重要） |
| **由来** | MUSUBIXオリジナル |

**EARS要件**:

> WHEN ユーザーが特定のモデルを指定した場合,  
> THE System SHALL 指定されたモデルを優先使用し,  
> AND WHEN 指定モデルが利用不可の場合,  
> THE System SHALL 利用可能な代替モデルに自動フォールバックし,  
> AND THE System SHALL モデルごとの利用統計を記録する。

**根拠**: VS Code LM APIでは複数のモデルが利用可能な場合がある。最適なモデル選択とフォールバックを提供。

**受入基準**:
- [ ] AC-PRV-002-1: モデル選択UIが提供される
- [ ] AC-PRV-002-2: 指定モデル利用不可時に自動フォールバックが動作する
- [ ] AC-PRV-002-3: モデルごとの成功率・レイテンシが記録される
- [ ] AC-PRV-002-4: フォールバック順序が設定可能

**トレーサビリティ**: DES-PRV-002, TSK-PRV-002

---

### 3.4 Delegation Format 要件

---

#### REQ-FMT-001: 7セクション委任フォーマット

| 属性 | 値 |
|------|-----|
| **ID** | REQ-FMT-001 |
| **名称** | 7セクション委任フォーマット |
| **種別** | Ubiquitous |
| **優先度** | P0（必須） |
| **由来** | claude-delegator: 7-Section Format |

**EARS要件**:

> THE System SHALL 以下の7セクション形式で委任プロンプトを構成する:  
> 1. TASK: 単一の具体的なゴール  
> 2. EXPECTED OUTCOME: 成功の定義  
> 3. CONTEXT: 現状・関連コード・背景  
> 4. CONSTRAINTS: 技術的・パターン的制約  
> 5. MUST DO: 必須アクション  
> 6. MUST NOT DO: 禁止アクション  
> 7. OUTPUT FORMAT: 出力形式の指定  
> AND THE System SHALL 各セクションの検証を行う。

**根拠**: claude-delegatorの7セクションフォーマットは委任の品質を保証する。MUSUBIXでも採用する。

**受入基準**:
- [ ] AC-FMT-001-1: 7セクションテンプレートが定義されている
- [ ] AC-FMT-001-2: セクション欠落時にエラーまたは警告を表示する
- [ ] AC-FMT-001-3: テンプレートから委任プロンプトを自動生成できる
- [ ] AC-FMT-001-4: カスタムセクションの追加が可能

**トレーサビリティ**: DES-FMT-001, TSK-FMT-001

---

#### REQ-FMT-002: EARS拡張委任フォーマット

| 属性 | 値 |
|------|-----|
| **ID** | REQ-FMT-002 |
| **名称** | EARS拡張委任フォーマット |
| **種別** | Ubiquitous |
| **優先度** | P1（重要） |
| **由来** | MUSUBIXオリジナル |

**EARS要件**:

> THE System SHALL 7セクションフォーマットをEARS形式で拡張し,  
> AND THE System SHALL EARS REQUIREMENT セクションを追加し,  
> AND THE System SHALL TRACEABILITY セクションを追加し,  
> AND THE System SHALL CONSTITUTION CHECK セクションを追加する。

**根拠**: MUSUBIXはEARS・トレーサビリティ・憲法条項に強みを持つ。委任フォーマットに統合する。

**拡張セクション**:
```
8. EARS REQUIREMENT: 関連するEARS形式要件
9. TRACEABILITY: REQ-* → DES-* → TSK-* マッピング
10. CONSTITUTION CHECK: 違反する可能性のある憲法条項
```

**受入基準**:
- [ ] AC-FMT-002-1: 10セクション拡張テンプレートが定義されている
- [ ] AC-FMT-002-2: EARS REQUIREMENT セクションに自動的に関連要件が挿入される
- [ ] AC-FMT-002-3: TRACEABILITY セクションにトレースリンクが挿入される
- [ ] AC-FMT-002-4: CONSTITUTION CHECK セクションに潜在的違反が警告される

**トレーサビリティ**: DES-FMT-002, TSK-FMT-002

---

### 3.5 MCP統合要件

---

#### REQ-MCP-001: Expert Delegation MCPツール

| 属性 | 値 |
|------|-----|
| **ID** | REQ-MCP-001 |
| **名称** | Expert Delegation MCPツール |
| **種別** | Ubiquitous |
| **優先度** | P0（必須） |
| **由来** | claude-delegator比較分析 |

**EARS要件**:

> THE MCP Server SHALL 以下の10ツールを提供する:  
> 1. `expert_delegate` - 適切なエキスパートにタスクを委任  
> 2. `expert_architect` - アーキテクチャ設計を専門家に委任  
> 3. `expert_security` - セキュリティ分析を専門家に委任  
> 4. `expert_review` - コードレビューを専門家に委任  
> 5. `expert_ears` - EARS要件分析を専門家に委任  
> 6. `expert_formal` - 形式検証を専門家に委任  
> 7. `expert_ontology` - オントロジー推論を専門家に委任  
> 8. `trigger_detect` - ユーザー意図を検出してルーティング  
> 9. `delegation_retry` - 失敗時の自動リトライ  
> 10. `provider_select` - AIプロバイダー選択  

**根拠**: MCPツールとして提供することで、Claude Code等のAIアシスタントからシームレスに利用可能になる。

**受入基準**:
- [ ] AC-MCP-001-1: 10ツールがMCPサーバーに登録されている
- [ ] AC-MCP-001-2: 各ツールのJSONスキーマが定義されている
- [ ] AC-MCP-001-3: Claude Codeから各ツールが呼び出せる
- [ ] AC-MCP-001-4: ツール実行結果が構造化された形式で返される

**トレーサビリティ**: DES-MCP-001, TSK-MCP-001

---

#### REQ-MCP-002: リトライ・エスカレーション機構

| 属性 | 値 |
|------|-----|
| **ID** | REQ-MCP-002 |
| **名称** | リトライ・エスカレーション機構 |
| **種別** | Event-Driven |
| **優先度** | P1（重要） |
| **由来** | claude-delegator: Retry Flow |

**EARS要件**:

> WHEN エキスパートの回答が不十分または失敗した場合,  
> THE System SHALL 最大3回までリトライを実行し,  
> AND THE System SHALL 各リトライに前回の失敗コンテキストを含め,  
> AND WHEN 3回のリトライがすべて失敗した場合,  
> THE System SHALL ユーザーへのエスカレーションを行い,  
> AND THE System SHALL 代替エキスパートへの切替を提案する。

**根拠**: claude-delegatorの3回リトライ + エスカレーションは実用的。MUSUBIXでも採用する。

**受入基準**:
- [ ] AC-MCP-002-1: リトライ回数が設定可能（デフォルト3回）
- [ ] AC-MCP-002-2: リトライ時に前回の失敗理由が含まれる
- [ ] AC-MCP-002-3: 3回失敗後にユーザーへ通知される
- [ ] AC-MCP-002-4: 代替エキスパートへの切替が提案される

**トレーサビリティ**: DES-MCP-002, TSK-MCP-002

---

### 3.6 非機能要件

---

#### REQ-NFR-001: ステートレス設計

| 属性 | 値 |
|------|-----|
| **ID** | REQ-NFR-001 |
| **名称** | ステートレス設計 |
| **種別** | Ubiquitous |
| **優先度** | P0（必須） |
| **由来** | claude-delegator: Stateless Design |

**EARS要件**:

> THE Expert Delegation System SHALL 各委任呼び出しをステートレスに設計し,  
> AND THE System SHALL 各呼び出しに完全なコンテキストを含め,  
> AND THE System SHALL 以前の呼び出し結果に依存しない。

**根拠**: claude-delegatorのステートレス設計は信頼性を高める。MUSUBIXでも採用する。

**受入基準**:
- [ ] AC-NFR-001-1: 委任呼び出し間でセッション状態を保持しない
- [ ] AC-NFR-001-2: 各呼び出しに必要な全コンテキストが含まれる
- [ ] AC-NFR-001-3: リトライ時も完全なコンテキストが再送される

**トレーサビリティ**: DES-NFR-001, TSK-NFR-001

---

#### REQ-NFR-002: テストカバレッジ

| 属性 | 値 |
|------|-----|
| **ID** | REQ-NFR-002 |
| **名称** | テストカバレッジ |
| **種別** | Ubiquitous |
| **優先度** | P0（必須） |
| **由来** | MUSUBIX憲法条項 III |

**EARS要件**:

> THE expert-delegation Package SHALL 80%以上のステートメントカバレッジを達成し,  
> AND THE Package SHALL すべての公開APIに対するテストを含み,  
> AND THE Package SHALL エッジケース・エラーケースをカバーする。

**根拠**: MUSUBIX憲法条項 III（Test-First）に準拠。

**受入基準**:
- [ ] AC-NFR-002-1: ステートメントカバレッジ80%以上
- [ ] AC-NFR-002-2: ブランチカバレッジ70%以上
- [ ] AC-NFR-002-3: すべての公開関数にテストが存在
- [ ] AC-NFR-002-4: エラーハンドリングのテストが存在

**トレーサビリティ**: DES-NFR-002, TSK-NFR-002

---

#### REQ-NFR-003: ドキュメント

| 属性 | 値 |
|------|-----|
| **ID** | REQ-NFR-003 |
| **名称** | ドキュメント |
| **種別** | Ubiquitous |
| **優先度** | P1（重要） |
| **由来** | MUSUBIX憲法条項 V |

**EARS要件**:

> THE expert-delegation Package SHALL APIリファレンスドキュメントを提供し,  
> AND THE Package SHALL 使用例を含むチュートリアルを提供し,  
> AND THE Package SHALL AGENTS.md/CLAUDE.mdへの統合ガイドを提供する。

**根拠**: MUSUBIX憲法条項 V（Traceability）に準拠。ドキュメントもトレース対象。

**受入基準**:
- [ ] AC-NFR-003-1: README.mdが存在し、クイックスタートを含む
- [ ] AC-NFR-003-2: APIリファレンスがTSDocで生成される
- [ ] AC-NFR-003-3: 使用例が最低5つ提供される
- [ ] AC-NFR-003-4: AGENTS.md統合ガイドが提供される

**トレーサビリティ**: DES-NFR-003, TSK-NFR-003

---

## 4. 要件サマリー

### 4.1 優先度別サマリー

| 優先度 | 要件数 | 要件ID |
|--------|--------|--------|
| **P0** | 8 | REQ-EXP-001, REQ-EXP-002, REQ-EXP-003, REQ-TRG-001, REQ-PRV-001, REQ-FMT-001, REQ-MCP-001, REQ-NFR-001, REQ-NFR-002 |
| **P1** | 7 | REQ-EXP-004, REQ-EXP-005, REQ-TRG-002, REQ-PRV-002, REQ-FMT-002, REQ-MCP-002, REQ-NFR-003 |
| **P2** | 0 | - |

### 4.2 カテゴリ別サマリー

| カテゴリ | 要件数 | 説明 |
|---------|--------|------|
| EXP | 5 | Expert Delegation基盤 |
| TRG | 2 | Trigger Detection |
| PRV | 2 | Provider Integration |
| FMT | 2 | Delegation Format |
| MCP | 2 | MCP統合 |
| NFR | 3 | 非機能要件 |
| **合計** | **16** | - |

### 4.3 新規MCPツール（10ツール）

| ツール名 | 説明 | 優先度 |
|---------|------|--------|
| `expert_delegate` | 適切なエキスパートにタスクを委任 | P0 |
| `expert_architect` | アーキテクチャ設計を専門家に委任 | P0 |
| `expert_security` | セキュリティ分析を専門家に委任 | P0 |
| `expert_review` | コードレビューを専門家に委任 | P0 |
| `expert_ears` | EARS要件分析を専門家に委任 | P0 |
| `expert_formal` | 形式検証を専門家に委任 | P1 |
| `expert_ontology` | オントロジー推論を専門家に委任 | P1 |
| `trigger_detect` | ユーザー意図を検出してルーティング | P0 |
| `delegation_retry` | 失敗時の自動リトライ | P1 |
| `provider_select` | AIプロバイダー選択 | P0 |

---

## 5. 変更履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|----------|--------|
| 1.0 | 2026-01-13 | 初版作成 | AI Agent |

---

## 6. 承認

| 役割 | 名前 | 日付 | 署名 |
|------|------|------|------|
| 作成者 | AI Agent | 2026-01-13 | - |
| レビュアー | - | - | - |
| 承認者 | - | - | - |

---

**END OF DOCUMENT**
