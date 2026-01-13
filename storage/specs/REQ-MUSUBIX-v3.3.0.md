# MUSUBIX v3.3.0 要件定義書
# Scaffold Enhancement & Pattern Learning Integration

**文書ID**: REQ-MUSUBIX-v3.3.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.1  
**作成日**: 2026-01-14  
**更新日**: 2026-01-14  
**ステータス**: Reviewed  
**準拠規格**: EARS（Easy Approach to Requirements Syntax）  
**参照文書**: REQ-MUSUBIX-v3.2.0.md, v3.2.0実装テスト結果

---

## 1. 文書概要

### 1.1 目的

本文書は、MUSUBIX v3.3.0の機能要件をEARS形式で正式に定義する。v3.2.0の実装テスト（10仮想プロジェクト、360テスト）で発見された改善点に基づき、scaffold機能の強化とパターン学習の自動化を実現する。

### 1.2 背景

**v3.2.0実装テスト結果**:
- 10プロジェクト全てで正常動作（360テスト全合格）
- scaffold domain-model: 基本機能は正常動作
- -v/-sオプション: 動作不安定（無視される）
- パターン自動抽出: 生成コードからの学習が未実装
- expert-delegation: scaffold時の活用が未統合

**Neuro-Symbolic設計原則**:
- MUSUBIX: 構造化・検証・記録に集中
- Copilot/LLM: 理解・推論・創造に委譲
- 両者の強みを活かした協調動作

**実装方針サマリー**:
| 要件ID | 実装方式 | 備考 |
|---------|---------|------|
| REQ-PTN-005 | MUSUBIX + Copilot連携 | Copilotの言語理解を活用 |
| REQ-EXD-003 | Copilotプロンプト | MUSUBIXコード実装対象外 |
| REQ-SCF-004 | 設計時整理 | -eオプションとの構文競合回避 |

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
| **P0** | 必須 - リリースブロッカー | v3.3.0 |
| **P1** | 重要 - 可能な限り実装 | v3.3.0 |
| **P2** | 任意 - 時間があれば | v3.4.0+ |

### 1.5 要件ID体系

```
REQ-<カテゴリ>-<連番>
```

| カテゴリ | 説明 |
|---------|------|
| SCF | Scaffold Enhancement（スキャフォールド強化） |
| PTN | Pattern Learning（パターン学習） |
| EXD | Expert-Delegation Integration（エキスパート委譲統合） |
| NFR | 非機能要件 |

### 1.6 スコープサマリー

| カテゴリ | P0 | P1 | P2 | 合計 |
|---------|----|----|----|----- |
| SCF (Scaffold) | 3 | 2 | 1 | 6 |
| PTN (Pattern) | 2 | 3 | 1 | 6 |
| EXD (Expert) | 1 | 2 | 2 | 5 |
| NFR (非機能) | 1 | 2 | 0 | 3 |
| **合計** | **7** | **9** | **4** | **20** |

---

## 2. Scaffold Enhancement（SCF）

### 2.1 Value Object生成修正

#### REQ-SCF-001: Value Object生成オプション
**優先度**: P0  
**パターン**: Event-Driven

WHEN the user executes `scaffold domain-model <name> -v "ValueObject1,ValueObject2"`, THE system SHALL generate TypeScript files for each specified Value Object with:
- Immutable interface definition
- Factory function with validation
- Equality comparison function
- Type guard function

**受入基準**:
```typescript
// 生成例: src/value-objects/Price.ts
export interface Price {
  readonly amount: number;
  readonly currency: 'JPY' | 'USD';
}

export function createPrice(amount: number, currency: 'JPY' | 'USD'): Result<Price, ValidationError>;
export function priceEquals(a: Price, b: Price): boolean;
export function isPrice(value: unknown): value is Price;
```

**トレース**: DES-SCF-001

---

#### REQ-SCF-002: Value Objectバリデーションルール
**優先度**: P1  
**パターン**: Optional

IF the Value Object name contains a known pattern (Price, Email, Phone, URL, UUID), THEN THE system SHALL generate appropriate validation rules automatically.

**受入基準**:
| Pattern | Validation |
|---------|------------|
| Price | amount >= 0, currency in allowed list |
| Email | RFC 5322準拠の正規表現 |
| Phone | E.164フォーマット |
| URL | URL constructor validation |
| UUID | UUID v4フォーマット |

**トレース**: DES-SCF-001

---

### 2.2 Status Machine生成修正

#### REQ-SCF-003: Status Machine生成オプション
**優先度**: P0  
**パターン**: Event-Driven

WHEN the user executes `scaffold domain-model <name> -s "Entity1,Entity2"`, THE system SHALL generate status machine code for each specified entity with:
- Status type definition (union type)
- Valid transition map
- canTransitionTo function
- changeStatus function with validation

**受入基準**:
```typescript
// 生成例: src/entities/Order.ts に追加
export type OrderStatus = 'draft' | 'pending' | 'confirmed' | 'shipped' | 'delivered' | 'cancelled';

const validOrderStatusTransitions: Record<OrderStatus, OrderStatus[]> = {
  draft: ['pending', 'cancelled'],
  pending: ['confirmed', 'cancelled'],
  confirmed: ['shipped', 'cancelled'],
  shipped: ['delivered'],
  delivered: [],
  cancelled: [],
};

export function canOrderTransitionTo(current: OrderStatus, target: OrderStatus): boolean;
export function changeOrderStatus(entity: Order, newStatus: OrderStatus): Result<Order, ValidationError>;
```

**トレース**: DES-SCF-002

---

#### REQ-SCF-004: Status Machine初期状態指定
**優先度**: P1  
**パターン**: Optional  
**設計ノート**: 設計フェーズで-eオプションとの構文整合性を整理

IF the user specifies `-s "Entity:initial_status"` format, THEN THE system SHALL use the specified status as the initial state instead of the first status in the list.

**設計時検討事項**:
- `-e "Order,Task"` と `-s "Order:draft"` の構文競合回避
- 代替案1: `-s "Order=draft"` (イコール区切り)
- 代替案2: `-s Order --initial-status draft` (サブオプション)
- 代替案3: 設定ファイルでデフォルト指定

**受入基準**:
```bash
# 使用例
npx musubix scaffold domain-model order -e "Order" -s "Order:draft"
# Order entityのstatus初期値が 'draft' になる
```

**トレース**: DES-SCF-002

---

### 2.3 Scaffold出力強化

#### REQ-SCF-005: 生成ファイルサマリー
**優先度**: P0  
**パターン**: Event-Driven

WHEN the scaffold command completes successfully, THE system SHALL output a structured summary including:
- Total files created
- Entities generated (with test count)
- Value Objects generated
- Status Machines generated
- Next steps guidance

**受入基準**:
```
✅ Created SDD project scaffold at /path/to/project

📊 Generation Summary:
   Entities: 3 (Cart, CartItem, Product)
   Value Objects: 2 (Price, Quantity)
   Status Machines: 1 (Cart)
   Tests: 45 files
   
🚀 Next steps:
   cd project-name
   npm install
   npm run test
```

**トレース**: DES-SCF-003

---

#### REQ-SCF-006: Scaffold Dry-runモード
**優先度**: P2  
**パターン**: Optional

IF the user specifies `--dry-run` option, THEN THE system SHALL display what files would be created without actually creating them.

**受入基準**:
```bash
npx musubix scaffold domain-model order -e "Order" --dry-run
# 実際にファイルを作成せず、作成予定ファイル一覧を表示
```

**トレース**: DES-SCF-003

---

## 3. Pattern Learning（PTN）

### 3.1 自動パターン抽出

#### REQ-PTN-001: Scaffold後自動パターン登録
**優先度**: P0  
**パターン**: Event-Driven

WHEN the scaffold command generates code successfully, THE system SHALL automatically extract and register patterns from the generated code to the learning store with:
- Pattern category (code/design/test)
- Source context (entity name, project type)
- Initial confidence: 60%

**受入基準**:
```bash
npx musubix scaffold domain-model order -e "Order,OrderItem"
# 自動的に以下のパターンが登録される:
# - Entity-Input-DTO pattern
# - Status-Transition-Map pattern
# - Result-Type pattern
# - Test-Counter-Reset pattern
```

**トレース**: DES-PTN-001

---

#### REQ-PTN-002: コードからのパターン検出
**優先度**: P0  
**パターン**: Event-Driven

WHEN the user executes `npx musubix learn extract <path>`, THE system SHALL analyze TypeScript/JavaScript files and detect the following patterns:
- Entity patterns (Input DTO, Factory Function)
- Value Object patterns (Immutable, Validated)
- Status Machine patterns (Transition Map)
- Error Handling patterns (Result Type, Custom Error)
- Test patterns (Counter Reset, Table-Driven)

**受入基準**:
```bash
npx musubix learn extract src/
# Output:
# Detected patterns:
#   - Entity-Input-DTO (3 instances, confidence: 85%)
#   - Result-Type (5 instances, confidence: 92%)
#   - Status-Transition-Map (2 instances, confidence: 78%)
```

**トレース**: DES-PTN-002

---

### 3.2 パターン信頼度管理

#### REQ-PTN-003: 使用頻度による信頼度更新
**優先度**: P1  
**パターン**: Event-Driven

WHEN a registered pattern is detected in new code or applied by scaffold, THE system SHALL increase the pattern's confidence by 5% (max 95%).

**受入基準**:
- 初期信頼度: 60%
- 検出/適用ごとに+5%
- 上限: 95%
- `npx musubix learn status` で確認可能

**トレース**: DES-PTN-003

---

#### REQ-PTN-004: パターン減衰メカニズム
**優先度**: P1  
**パターン**: Event-Driven

WHEN `npx musubix learn decay` is executed, THE system SHALL reduce confidence of unused patterns by 10% and archive patterns with confidence below 30%.

**受入基準**:
```bash
npx musubix learn decay
# Output:
# Decayed patterns:
#   - Old-Pattern-1: 45% -> 35%
#   - Old-Pattern-2: 28% -> archived
```

**トレース**: DES-PTN-003

---

### 3.3 パターン推薦

#### REQ-PTN-005: コンテキストベース推薦
**優先度**: P1  
**パターン**: Event-Driven

WHEN the user executes `npx musubix learn recommend`, THE system SHALL analyze the current project context and recommend applicable patterns with confidence scores.

**実装方針**: MUSUBIX実装 + GitHub Copilot連携
- MUSUBIXがパターンライブラリとプロジェクト構造を解析
- コンテキスト情報をCopilotに提供し、推薦精度を向上
- Copilotの言語理解能力を活用した意味的マッチング

**受入基準**:
```bash
npx musubix learn recommend
# Output (based on project context):
# Recommended patterns for 'shopping-cart':
#   1. Cart-Pattern (confidence: 88%) - E-commerce cart management
#   2. Price-Value-Object (confidence: 85%) - Monetary value handling
#   3. Inventory-Check (confidence: 72%) - Stock validation
```

**トレース**: DES-PTN-004

---

#### REQ-PTN-006: パターンテンプレート生成
**優先度**: P2  
**パターン**: Optional

IF the user executes `npx musubix learn apply <pattern-id>`, THEN THE system SHALL generate code from the pattern template with project-specific customization.

**受入基準**:
```bash
npx musubix learn apply BP-CODE-001
# Generates Entity-Input-DTO code template
# with project-specific naming conventions
```

**トレース**: DES-PTN-004

---

## 4. Expert-Delegation Integration（EXD）

### 4.1 Scaffold時のExpert活用

#### REQ-EXD-001: Architect Expert統合
**優先度**: P0  
**パターン**: Optional

IF the user specifies `--expert` option with scaffold command, THEN THE system SHALL invoke the Architect expert to:
- Analyze entity relationships
- Suggest additional entities/value objects
- Recommend design patterns
- Generate C4 component diagram suggestions

**受入基準**:
```bash
npx musubix scaffold domain-model order -e "Order" --expert
# Output includes:
# 🏗️ Architect Analysis:
#   Suggested entities: OrderItem, Customer, Product
#   Suggested value objects: Money, Address
#   Recommended patterns: Repository, Factory
#   C4 suggestions: [diagram link]
```

**トレース**: DES-EXD-001

---

#### REQ-EXD-002: Security Expert統合
**優先度**: P1  
**パターン**: Optional

IF the user specifies `--security-check` option with scaffold command, THEN THE system SHALL invoke the Security Analyst expert to review the generated code for:
- Input validation completeness
- Sensitive data handling
- Authentication/Authorization patterns

**受入基準**:
```bash
npx musubix scaffold domain-model user -e "User,Session" --security-check
# Output includes:
# 🔒 Security Analysis:
#   ⚠️ User entity: Consider password hashing
#   ⚠️ Session entity: Add token expiration
#   ✅ Input validation: Complete
```

**トレース**: DES-EXD-002

---

### 4.2 対話的Scaffold

#### REQ-EXD-003: Expert対話モード
**優先度**: P1  
**パターン**: Optional  
**実装方式**: GitHub Copilotプロンプト（MUSUBIXコード実装対象外）

IF the user wants interactive scaffold guidance, THEN GitHub Copilot SHALL provide interactive dialogue using MUSUBIX expert prompts.

**実装方針**:
- MUSUBIXは`sdd_expert_scaffold`プロンプトを提供
- 対話ロジックはCopilotが処理
- MUSUBIXはコンテキスト情報（エンティティ、パターン、既存コード）を提供

**受入基準**:
```
# Copilotプロンプト使用例:
User: @musubix scaffold domain-model order を対話的に実行したい

Copilot (using sdd_expert_scaffold prompt):
> What is the primary domain? (e-commerce/logistics/...)
> Does Order have status transitions?
> Should OrderItem reference Product entity?
```

**トレース**: DES-EXD-003

---

### 4.3 Expert結果のパターン学習

#### REQ-EXD-004: Expert推薦のパターン化
**優先度**: P2  
**パターン**: Event-Driven

WHEN an expert recommendation is accepted by the user, THE system SHALL register the recommendation as a new pattern with initial confidence 70%.

**受入基準**:
- Expert推薦 → ユーザー承認 → パターン登録
- 承認されなかった推薦は登録しない
- `npx musubix learn feedback` と連携

**トレース**: DES-EXD-004

---

#### REQ-EXD-005: Expert学習データ蓄積
**優先度**: P2  
**パターン**: Ubiquitous

THE system SHALL log all expert invocations and user responses to enable pattern refinement and expert prompt optimization.

**受入基準**:
- storage/learning/expert-logs/ にログ保存
- プライバシーフィルタリング適用
- `npx musubix learn export --expert-logs` でエクスポート可能

**トレース**: DES-EXD-004

---

## 5. 非機能要件（NFR）

### 5.1 パフォーマンス

#### REQ-NFR-001: Scaffold実行時間
**優先度**: P0  
**パターン**: Ubiquitous

THE system SHALL complete scaffold command execution within 5 seconds for projects with up to 10 entities.

**受入基準**:
- 5エンティティ: < 2秒
- 10エンティティ: < 5秒
- Expert統合時: < 10秒（LLM応答時間含む）

**トレース**: DES-NFR-001

---

#### REQ-NFR-002: パターン検索性能
**優先度**: P1  
**パターン**: Ubiquitous

THE system SHALL return pattern search results within 100ms for pattern libraries containing up to 1000 patterns.

**受入基準**:
- 100パターン: < 20ms
- 500パターン: < 50ms
- 1000パターン: < 100ms

**トレース**: DES-NFR-001

---

### 5.2 互換性

#### REQ-NFR-003: 後方互換性
**優先度**: P1  
**パターン**: Ubiquitous

THE system SHALL maintain backward compatibility with v3.2.0 scaffold output and learning data formats.

**受入基準**:
- v3.2.0で生成されたプロジェクトがv3.3.0で正常動作
- v3.2.0のlearning-data.jsonがv3.3.0で読み込み可能
- 既存CLIコマンドの動作変更なし

**トレース**: DES-NFR-002

---

## 6. トレーサビリティマトリクス

| 要件ID | 設計ID | タスクID | テストID | 状態 |
|--------|--------|----------|----------|------|
| REQ-SCF-001 | DES-SCF-001 | TSK-SCF-001 | TST-SCF-001 | Draft |
| REQ-SCF-002 | DES-SCF-001 | TSK-SCF-002 | TST-SCF-002 | Draft |
| REQ-SCF-003 | DES-SCF-002 | TSK-SCF-003 | TST-SCF-003 | Draft |
| REQ-SCF-004 | DES-SCF-002 | TSK-SCF-004 | TST-SCF-004 | Draft |
| REQ-SCF-005 | DES-SCF-003 | TSK-SCF-005 | TST-SCF-005 | Draft |
| REQ-SCF-006 | DES-SCF-003 | TSK-SCF-006 | TST-SCF-006 | Draft |
| REQ-PTN-001 | DES-PTN-001 | TSK-PTN-001 | TST-PTN-001 | Draft |
| REQ-PTN-002 | DES-PTN-002 | TSK-PTN-002 | TST-PTN-002 | Draft |
| REQ-PTN-003 | DES-PTN-003 | TSK-PTN-003 | TST-PTN-003 | Draft |
| REQ-PTN-004 | DES-PTN-003 | TSK-PTN-004 | TST-PTN-004 | Draft |
| REQ-PTN-005 | DES-PTN-004 | TSK-PTN-005 | TST-PTN-005 | Draft |
| REQ-PTN-006 | DES-PTN-004 | TSK-PTN-006 | TST-PTN-006 | Draft |
| REQ-EXD-001 | DES-EXD-001 | TSK-EXD-001 | TST-EXD-001 | Draft |
| REQ-EXD-002 | DES-EXD-002 | TSK-EXD-002 | TST-EXD-002 | Draft |
| REQ-EXD-003 | DES-EXD-003 | TSK-EXD-003 | TST-EXD-003 | Draft |
| REQ-EXD-004 | DES-EXD-004 | TSK-EXD-004 | TST-EXD-004 | Draft |
| REQ-EXD-005 | DES-EXD-004 | TSK-EXD-005 | TST-EXD-005 | Draft |
| REQ-NFR-001 | DES-NFR-001 | TSK-NFR-001 | TST-NFR-001 | Draft |
| REQ-NFR-002 | DES-NFR-001 | TSK-NFR-002 | TST-NFR-002 | Draft |
| REQ-NFR-003 | DES-NFR-002 | TSK-NFR-003 | TST-NFR-003 | Draft |

---

## 7. 用語集

| 用語 | 定義 |
|------|------|
| Value Object | 値によって同一性が決まる不変オブジェクト |
| Status Machine | エンティティの状態遷移を管理するパターン |
| Pattern Confidence | パターンの信頼度（0-100%） |
| Expert Delegation | AIエキスパートへのタスク委譲 |
| Scaffold | プロジェクト構造の自動生成 |

---

## 8. 承認

| 役割 | 氏名 | 日付 | 署名 |
|------|------|------|------|
| 作成者 | AI Agent | 2026-01-14 | ✓ |
| レビュアー | | | |
| 承認者 | | | |

---

**文書終了**
