# MUSUBIX 形式検証パッケージ

**パッケージ名**: `@nahisaho/musubix-formal-verify`  
**バージョン**: 1.7.5  
**最終更新**: 2026-01-06

---

## 1. 概要

`@nahisaho/musubix-formal-verify` は、Z3 SMTソルバを使用した形式検証機能を提供するパッケージです。EARS形式の要件をSMT-LIB2形式に変換し、事前条件・事後条件の数学的検証を行います。

### 1.1 主要機能

| 機能 | 説明 |
|------|------|
| **Z3統合** | WebAssembly版とプロセス版の自動切り替え |
| **事前条件検証** | 関数の入力条件の充足可能性検証 |
| **事後条件検証** | Hoareトリプル {P} C {Q} の検証 |
| **EARS→SMT変換** | 5パターンのEARS要件をSMT-LIB2に変換 |
| **トレーサビリティDB** | 要件・設計・コード間のリンク管理 |
| **影響分析** | 変更による影響範囲の分析 |

### 1.2 モジュール構成

```
packages/formal-verify/src/
├── z3/                  # Z3 SMTソルバ統合
│   ├── Z3Adapter.ts         # メインアダプタ
│   ├── Z3WasmClient.ts      # WebAssembly版
│   ├── Z3ProcessFallback.ts # プロセス版フォールバック
│   └── types.ts             # 型定義
├── verifiers/           # 検証器
│   ├── PreconditionVerifier.ts   # 事前条件検証
│   ├── PostconditionVerifier.ts  # 事後条件検証
│   └── types.ts                  # 型定義
├── converters/          # 変換器
│   ├── EarsToSmtConverter.ts # EARS→SMT変換
│   └── types.ts              # 型定義
├── traceability/        # トレーサビリティ
│   ├── TraceabilityDB.ts    # データベース
│   ├── ImpactAnalyzer.ts    # 影響分析
│   └── types.ts             # 型定義
├── tools/               # MCPツール
│   └── formal-verify-tools.ts
└── index.ts             # エントリポイント
```

---

## 2. Z3 SMTソルバ統合

### 2.1 概要

Z3は、Microsoftが開発した高性能SMT（Satisfiability Modulo Theories）ソルバです。MUSUBIXでは、WebAssembly版を優先使用し、利用できない場合はプロセス版にフォールバックします。

### 2.2 Z3Adapter

メインのZ3アダプタクラス。

```typescript
import { Z3Adapter } from '@nahisaho/musubix-formal-verify';

const z3 = new Z3Adapter();

// 初期化（自動でWASM/プロセスを選択）
await z3.initialize();

// SMT-LIB2スクリプトを検証
const result = await z3.verify(`
  (declare-const x Int)
  (declare-const y Int)
  (assert (> x 0))
  (assert (> y 0))
  (assert (= (+ x y) 10))
  (check-sat)
`);

console.log(result.status); // 'sat' | 'unsat' | 'unknown'
console.log(result.model);  // 充足可能な場合のモデル
```

### 2.3 実行モード

| モード | 説明 | 優先度 |
|--------|------|--------|
| **WASM** | WebAssembly版（z3-solver） | 高 |
| **Process** | ローカルz3コマンド実行 | 低（フォールバック） |

### 2.4 型定義

```typescript
// Z3結果
interface Z3Result {
  status: 'sat' | 'unsat' | 'unknown' | 'error';
  model?: Record<string, unknown>;
  unsatCore?: string[];
  statistics?: Z3Statistics;
  duration: number;
  error?: string;
}

// Z3統計情報
interface Z3Statistics {
  numConflicts: number;
  numDecisions: number;
  memoryUsage: number;
  time: number;
}

// Z3オプション
interface Z3Options {
  timeout?: number;        // タイムアウト（ミリ秒）
  model?: boolean;         // モデル生成
  unsatCore?: boolean;     // UNSAT時のコア抽出
  proof?: boolean;         // 証明生成
}
```

---

## 3. 事前条件検証（Precondition Verifier）

### 3.1 概要

関数の入力条件（事前条件）が充足可能かどうかを検証します。

### 3.2 使用例

```typescript
import { PreconditionVerifier } from '@nahisaho/musubix-formal-verify';

const verifier = new PreconditionVerifier();

// 事前条件を検証
const result = await verifier.verify({
  condition: {
    expression: 'amount > 0 && amount <= balance',
    format: 'javascript',
  },
  variables: [
    { name: 'amount', type: 'Int' },
    { name: 'balance', type: 'Int' },
  ],
  options: {
    timeout: 5000,
    generateCounterexample: true,
  },
});

console.log(result.status);        // 'valid' | 'invalid' | 'unknown'
console.log(result.counterexample); // 反例（invalidの場合）
```

### 3.3 対応する変数型

| 型 | SMT型 | 説明 |
|----|-------|------|
| `Int` | `Int` | 整数 |
| `Real` | `Real` | 実数 |
| `Bool` | `Bool` | 真偽値 |
| `String` | `String` | 文字列 |
| `Array` | `Array` | 配列 |
| `BitVec` | `BitVec` | ビットベクトル |

### 3.4 対応する演算子

```typescript
// 比較演算子
'>' | '<' | '>=' | '<=' | '==' | '!='

// 論理演算子
'&&' | '||' | '!'

// 算術演算子
'+' | '-' | '*' | '/' | '%'
```

---

## 4. 事後条件検証（Postcondition Verifier）

### 4.1 概要

Hoareトリプル `{P} C {Q}`（事前条件P、コマンドC、事後条件Q）の検証を行います。

### 4.2 使用例

```typescript
import { PostconditionVerifier } from '@nahisaho/musubix-formal-verify';

const verifier = new PostconditionVerifier();

// Hoareトリプルを検証
const result = await verifier.verify({
  precondition: {
    expression: 'balance >= amount && amount > 0',
    format: 'javascript',
  },
  postcondition: {
    expression: 'balance_new == balance - amount',
    format: 'javascript',
  },
  preVariables: [
    { name: 'balance', type: 'Int' },
    { name: 'amount', type: 'Int' },
  ],
  postVariables: [
    { name: 'balance_new', type: 'Int' },
  ],
  transition: 'balance_new := balance - amount',
});

console.log(result.status);  // 'valid' | 'invalid' | 'unknown'
console.log(result.proof);   // 証明（validの場合）
```

### 4.3 検証フロー

```
┌─────────────────────────────────────────────────────────┐
│                  Hoare Triple {P} C {Q}                  │
│                                                          │
│  事前条件 P: balance >= amount && amount > 0             │
│  遷移 C:    balance_new := balance - amount              │
│  事後条件 Q: balance_new == balance - amount              │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│              SMT-LIB2 に変換                             │
│                                                          │
│  (declare-const balance Int)                             │
│  (declare-const amount Int)                              │
│  (declare-const balance_new Int)                         │
│  (assert (and (>= balance amount) (> amount 0)))   ; P  │
│  (assert (= balance_new (- balance amount)))       ; C  │
│  (assert (not (= balance_new (- balance amount)))) ; ¬Q │
│  (check-sat)                                             │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│              Z3 で検証                                   │
│                                                          │
│  結果: unsat → Hoareトリプルは valid                     │
│  結果: sat   → Hoareトリプルは invalid（反例あり）       │
└─────────────────────────────────────────────────────────┘
```

---

## 5. EARS→SMT変換

### 5.1 概要

EARS形式の要件をSMT-LIB2形式に変換します。5つのEARSパターンすべてに対応しています。

### 5.2 使用例

```typescript
import { EarsToSmtConverter } from '@nahisaho/musubix-formal-verify';

const converter = new EarsToSmtConverter();

// Event-driven パターン
const result = converter.convert(
  'WHEN a user submits login form, THE system SHALL validate credentials within 2 seconds.'
);

console.log(result.pattern);  // 'event-driven'
console.log(result.smtLib2);  // SMT-LIB2 コード
console.log(result.warnings); // 変換時の警告
```

### 5.3 パターン別変換

#### Ubiquitous（常時）

```
入力: THE system SHALL encrypt all user data.

出力:
(declare-const system_active Bool)
(declare-const data_encrypted Bool)
(assert (=> system_active data_encrypted))
(check-sat)
```

#### Event-driven（イベント駆動）

```
入力: WHEN user clicks button, THE system SHALL save data.

出力:
(declare-const user_clicks_button Bool)
(declare-const system_saves_data Bool)
(assert (=> user_clicks_button system_saves_data))
(check-sat)
```

#### State-driven（状態駆動）

```
入力: WHILE in maintenance mode, THE system SHALL reject requests.

出力:
(declare-const maintenance_mode Bool)
(declare-const requests_rejected Bool)
(assert (=> maintenance_mode requests_rejected))
(check-sat)
```

#### Unwanted（禁止）

```
入力: THE system SHALL NOT store passwords in plain text.

出力:
(declare-const passwords_plain_text Bool)
(assert (not passwords_plain_text))
(check-sat)
```

#### Optional（条件付き）

```
入力: IF user is admin, THEN THE system SHALL show dashboard.

出力:
(declare-const user_is_admin Bool)
(declare-const dashboard_shown Bool)
(assert (=> user_is_admin dashboard_shown))
(check-sat)
```

---

## 6. トレーサビリティDB

### 6.1 概要

要件・設計・コード・テスト間のトレーサビリティリンクを管理するデータベースです。

### 6.2 使用例

```typescript
import { TraceabilityDB } from '@nahisaho/musubix-formal-verify';

const db = new TraceabilityDB();
await db.initialize('./trace.db');

// ノード追加
await db.addNode({
  id: 'REQ-001',
  type: 'requirement',
  title: 'User Authentication',
  content: 'THE system SHALL authenticate users...',
});

await db.addNode({
  id: 'DES-001',
  type: 'design',
  title: 'Auth Module Design',
  content: 'C4 Component diagram...',
});

// リンク追加
await db.addLink({
  source: 'REQ-001',
  target: 'DES-001',
  type: 'implements',
  confidence: 0.95,
  description: 'Design implements requirement',
});

// クエリ
const related = await db.getRelatedNodes('REQ-001', {
  direction: 'downstream',
  maxDepth: 3,
});
```

### 6.3 ノードタイプ

| タイプ | 説明 | ID形式 |
|--------|------|--------|
| `requirement` | 要件 | `REQ-XXX` |
| `design` | 設計 | `DES-XXX` |
| `code` | コード | `CODE-XXX` |
| `test` | テスト | `TEST-XXX` |
| `task` | タスク | `TSK-XXX` |
| `documentation` | 文書 | `DOC-XXX` |

### 6.4 リンクタイプ

| タイプ | 説明 | 方向 |
|--------|------|------|
| `satisfies` | 充足する | 下流 → 上流 |
| `implements` | 実装する | 下流 → 上流 |
| `verifies` | 検証する | テスト → 対象 |
| `traces-to` | 追跡する | 双方向 |
| `depends-on` | 依存する | 依存元 → 依存先 |

---

## 7. 影響分析

### 7.1 概要

ノードの変更による影響範囲を分析します。

### 7.2 使用例

```typescript
import { ImpactAnalyzer } from '@nahisaho/musubix-formal-verify';

const analyzer = new ImpactAnalyzer(db);

// 影響分析
const impact = await analyzer.analyze('REQ-001', {
  maxDepth: 5,
  decayRate: 0.7,
  minImpactScore: 0.1,
});

console.log(impact.sourceId);      // 'REQ-001'
console.log(impact.impactedNodes); // 影響を受けるノード一覧
console.log(impact.totalImpacted); // 影響ノード数
```

### 7.3 影響スコア

影響スコアは、ソースからの距離に応じて減衰します。

```
影響スコア = decayRate ^ (距離 - 1)

例（decayRate = 0.7）:
- 距離1: 1.0
- 距離2: 0.7
- 距離3: 0.49
- 距離4: 0.343
```

---

## 8. MCPツール

### 8.1 概要

Model Context Protocol（MCP）経由で形式検証機能を提供するツールです。

### 8.2 利用可能なツール

| ツール名 | 説明 |
|---------|------|
| `verify_precondition` | 事前条件の検証 |
| `verify_postcondition` | 事後条件（Hoareトリプル）の検証 |
| `ears_to_smt` | EARS要件→SMT-LIB2変換 |
| `trace_add_link` | トレーサビリティリンク追加 |
| `trace_query` | トレーサビリティクエリ |
| `trace_impact` | 影響分析 |

### 8.3 ツール使用例（MCP経由）

```json
// verify_precondition
{
  "tool": "verify_precondition",
  "arguments": {
    "condition": {
      "expression": "amount > 0",
      "format": "javascript"
    },
    "variables": [
      { "name": "amount", "type": "Int" }
    ]
  }
}

// ears_to_smt
{
  "tool": "ears_to_smt",
  "arguments": {
    "requirement": "WHEN user logs in, THE system SHALL create session."
  }
}

// trace_impact
{
  "tool": "trace_impact",
  "arguments": {
    "nodeId": "REQ-001",
    "maxDepth": 5
  }
}
```

---

## 9. インストールと使用

### 9.1 インストール

```bash
npm install @nahisaho/musubix-formal-verify
```

### 9.2 Z3のセットアップ

WebAssembly版は自動的にインストールされます。プロセス版フォールバックを使用する場合は、z3をシステムにインストールしてください。

```bash
# Ubuntu/Debian
sudo apt-get install z3

# macOS
brew install z3

# Windows
# https://github.com/Z3Prover/z3/releases からダウンロード
```

### 9.3 基本的な使用

```typescript
import {
  Z3Adapter,
  PreconditionVerifier,
  PostconditionVerifier,
  EarsToSmtConverter,
  TraceabilityDB,
  ImpactAnalyzer,
} from '@nahisaho/musubix-formal-verify';

// 初期化
const z3 = new Z3Adapter();
await z3.initialize();

// 検証器
const preVerifier = new PreconditionVerifier();
const postVerifier = new PostconditionVerifier();

// 変換器
const converter = new EarsToSmtConverter();

// トレーサビリティ
const db = new TraceabilityDB();
const analyzer = new ImpactAnalyzer(db);
```

---

## 10. 関連ドキュメント

| ドキュメント | 説明 |
|-------------|------|
| [MUSUBIX-Overview.md](MUSUBIX-Overview.md) | 全体概要 |
| [MUSUBIX-Core.md](MUSUBIX-Core.md) | Coreパッケージ |
| [API-REFERENCE.md](API-REFERENCE.md) | APIリファレンス |
| [USER-GUIDE.md](USER-GUIDE.md) | ユーザーガイド |

---

**© 2026 MUSUBIX Project**
