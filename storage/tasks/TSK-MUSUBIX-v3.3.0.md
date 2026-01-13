# MUSUBIX v3.3.0 タスク分解書
# Scaffold Enhancement & Pattern Learning Integration

**文書ID**: TSK-MUSUBIX-v3.3.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-14  
**ステータス**: Draft  
**参照文書**: REQ-MUSUBIX-v3.3.0.md, DES-MUSUBIX-v3.3.0.md

---

## 1. タスク概要

### 1.1 実装スコープ

| カテゴリ | P0タスク | P1タスク | P2タスク | 合計 |
|---------|---------|---------|---------|------|
| SCF (Scaffold) | 3 | 2 | 1 | 6 |
| PTN (Pattern) | 2 | 3 | 1 | 6 |
| EXD (Expert) | 1 | 1 | 0 | 2 |
| NFR (非機能) | 1 | 2 | 0 | 3 |
| **合計** | **7** | **8** | **2** | **17** |

**注**: REQ-EXD-003, REQ-EXD-004, REQ-EXD-005はCopilotプロンプト/P2のためv3.4.0へ延期

### 1.2 工数見積もり

| 優先度 | 見積もり時間 | タスク数 |
|--------|-------------|---------|
| P0（必須） | 8時間 | 7 |
| P1（重要） | 6時間 | 8 |
| P2（任意） | 2時間 | 2 |
| **合計** | **16時間** | **17** |

### 1.3 依存関係図

```
TSK-SCF-001 (VO Generator)
    │
    ├── TSK-SCF-002 (VO Tests)
    │
TSK-SCF-003 (Status Generator)
    │
    ├── TSK-SCF-004 (Status Tests)
    │
    └────────┬────────┘
             │
             ▼
TSK-SCF-005 (Scaffold統合)
             │
             ▼
TSK-SCF-006 (Result Aggregator)
             │
             ▼
TSK-PTN-001 (Auto Extractor)
             │
             ├── TSK-PTN-002 (Pattern検出器)
             │
             └── TSK-PTN-003 (Library統合)
                      │
                      ▼
             TSK-PTN-004 (Decay Manager)
                      │
                      ▼
             TSK-PTN-005 (Recommender)
                      │
                      ▼
             TSK-EXD-001 (Expert Integrator)
                      │
                      ▼
             TSK-NFR-001 (Performance)
```

---

## 2. Scaffold Enhancement タスク（SCF）

### TSK-SCF-001: Value Object Generator実装
**優先度**: P0  
**見積もり**: 1.5時間  
**依存**: なし  
**トレース**: REQ-SCF-001, REQ-SCF-002 → DES-SCF-001

#### 作業内容
1. `packages/core/src/cli/generators/value-object-generator.ts` を新規作成
2. `ValueObjectSpec` インターフェース実装
3. `ValueObjectGenerator` クラス実装
4. テンプレート生成ロジック実装
5. バリデーション関数生成

#### 受入基準
- [ ] `ValueObjectGenerator.generate()` が正常動作
- [ ] 生成されたVOがTypeScript型チェックを通過
- [ ] 生成されたテストが実行可能

#### ファイル
```
packages/core/src/cli/generators/
├── index.ts                    # NEW: export追加
└── value-object-generator.ts   # NEW
```

---

### TSK-SCF-002: Value Object Generatorテスト
**優先度**: P0  
**見積もり**: 0.5時間  
**依存**: TSK-SCF-001  
**トレース**: REQ-SCF-001, REQ-SCF-002 → DES-SCF-001

#### 作業内容
1. `__tests__/value-object-generator.test.ts` 作成
2. 正常系テスト（Price, Email, Quantity等）
3. 異常系テスト（無効な名前、空配列等）
4. テンプレート出力検証

#### 受入基準
- [ ] 5つ以上のテストケース
- [ ] カバレッジ80%以上

#### ファイル
```
packages/core/src/cli/generators/__tests__/
└── value-object-generator.test.ts  # NEW
```

---

### TSK-SCF-003: Status Machine Generator実装
**優先度**: P0  
**見積もり**: 1.5時間  
**依存**: なし  
**トレース**: REQ-SCF-003, REQ-SCF-004 → DES-SCF-002

#### 作業内容
1. `packages/core/src/cli/generators/status-machine-generator.ts` を新規作成
2. `StatusMachineSpec` インターフェース実装
3. `StatusMachineGenerator` クラス実装
4. `-s "Entity=status"` パーサー実装（ADR-v3.3.0-001準拠）
5. 遷移マップ生成ロジック実装

#### 受入基準
- [ ] `StatusMachineGenerator.generate()` が正常動作
- [ ] `-s "Order=draft,Task=pending"` が正しくパースされる
- [ ] 生成された遷移マップが正しい

#### ファイル
```
packages/core/src/cli/generators/
└── status-machine-generator.ts  # NEW
```

---

### TSK-SCF-004: Status Machine Generatorテスト
**優先度**: P1  
**見積もり**: 0.5時間  
**依存**: TSK-SCF-003  
**トレース**: REQ-SCF-003, REQ-SCF-004 → DES-SCF-002

#### 作業内容
1. `__tests__/status-machine-generator.test.ts` 作成
2. -sオプションパーサーテスト
3. 遷移マップ生成テスト
4. enum生成オプションテスト

#### 受入基準
- [ ] 5つ以上のテストケース
- [ ] `-s` オプション構文テスト網羅

#### ファイル
```
packages/core/src/cli/generators/__tests__/
└── status-machine-generator.test.ts  # NEW
```

---

### TSK-SCF-005: Scaffold Command統合
**優先度**: P0  
**見積もり**: 1時間  
**依存**: TSK-SCF-001, TSK-SCF-003  
**トレース**: REQ-SCF-001, REQ-SCF-003 → DES-SCF-001, DES-SCF-002

#### 作業内容
1. `scaffold.ts` に `-v` オプション処理を追加
2. `scaffold.ts` に `-s` オプション処理を修正（ADR-v3.3.0-001準拠）
3. `ValueObjectGenerator` 呼び出し統合
4. `StatusMachineGenerator` 呼び出し統合
5. 既存テスト更新

#### 受入基準
- [ ] `npx musubix scaffold domain-model test -v "Price,Email"` が動作
- [ ] `npx musubix scaffold domain-model test -s "Order=draft"` が動作
- [ ] 既存の `-e` オプションと併用可能

#### ファイル
```
packages/core/src/cli/commands/
└── scaffold.ts  # MODIFIED
```

---

### TSK-SCF-006: Scaffold Result Aggregator実装
**優先度**: P1  
**見積もり**: 1時間  
**依存**: TSK-SCF-005  
**トレース**: REQ-SCF-005, REQ-SCF-006 → DES-SCF-003

#### 作業内容
1. `scaffold-result-aggregator.ts` を新規作成
2. `ScaffoldSummary` インターフェース実装
3. サマリー集約ロジック実装
4. 整形出力ロジック実装
5. `--dry-run` オプション対応

#### 受入基準
- [ ] 生成結果サマリーが正しく表示される
- [ ] `--dry-run` でファイル作成なしにプレビュー表示

#### ファイル
```
packages/core/src/cli/generators/
└── scaffold-result-aggregator.ts  # NEW
```

---

## 3. Pattern Learning タスク（PTN）

### TSK-PTN-001: Pattern Auto Extractor実装
**優先度**: P0  
**見積もり**: 1.5時間  
**依存**: TSK-SCF-005  
**トレース**: REQ-PTN-001 → DES-PTN-001

#### 作業内容
1. `packages/pattern-mcp/src/extractor/auto-extractor.ts` を新規作成
2. `PatternAutoExtractor` クラス実装
3. `extractFromDirectory()` 実装
4. `extractAndRegister()` 実装（Scaffold統合用）
5. 重複チェックロジック実装

#### 受入基準
- [ ] Scaffold後に自動でパターン抽出が実行される
- [ ] 抽出されたパターンがライブラリに登録される
- [ ] 初期信頼度60%で登録される

#### ファイル
```
packages/pattern-mcp/src/extractor/
├── index.ts          # MODIFIED: export追加
└── auto-extractor.ts # NEW
```

---

### TSK-PTN-002: Pattern検出器実装
**優先度**: P0  
**見積もり**: 1時間  
**依存**: TSK-PTN-001  
**トレース**: REQ-PTN-002 → DES-PTN-001

#### 作業内容
1. 組み込みパターン検出器を実装
2. Entity-Input-DTO検出器
3. Result-Type検出器
4. Status-Transition-Map検出器
5. Test-Counter-Reset検出器

#### 受入基準
- [ ] 5種類以上のパターンを検出可能
- [ ] 信頼度スコアが正しく計算される

#### ファイル
```
packages/pattern-mcp/src/extractor/
└── auto-extractor.ts # MODIFIED: 検出器追加
```

---

### TSK-PTN-003: Library統合・CLIコマンド
**優先度**: P1  
**見積もり**: 0.5時間  
**依存**: TSK-PTN-001, TSK-PTN-002  
**トレース**: REQ-PTN-002 → DES-PTN-001

#### 作業内容
1. `npx musubix learn extract <path>` コマンド追加
2. PatternLibraryとの統合
3. 出力フォーマット実装

#### 受入基準
- [ ] `npx musubix learn extract src/` が動作
- [ ] 検出パターン一覧が表示される

#### ファイル
```
packages/core/src/cli/commands/
└── learn.ts  # MODIFIED
```

---

### TSK-PTN-004: Pattern Decay Manager実装
**優先度**: P1  
**見積もり**: 1時間  
**依存**: TSK-PTN-003  
**トレース**: REQ-PTN-003, REQ-PTN-004 → DES-PTN-003

#### 作業内容
1. `packages/pattern-mcp/src/library/pattern-decay-manager.ts` を新規作成
2. `PatternDecayManager` クラス実装
3. `incrementConfidence()` 実装（+5%, max 95%）
4. `applyDecay()` 実装（-10%, archive < 30%）
5. `npx musubix learn decay` コマンド更新

#### 受入基準
- [ ] パターン使用時に信頼度が増加
- [ ] 減衰実行時に未使用パターンの信頼度が減少
- [ ] 30%未満のパターンがアーカイブされる

#### ファイル
```
packages/pattern-mcp/src/library/
├── index.ts              # MODIFIED: export追加
└── pattern-decay-manager.ts # NEW
```

---

### TSK-PTN-005: Pattern Recommender実装
**優先度**: P1  
**見積もり**: 1.5時間  
**依存**: TSK-PTN-004  
**トレース**: REQ-PTN-005 → DES-PTN-004

#### 作業内容
1. `packages/pattern-mcp/src/recommender/pattern-recommender.ts` を新規作成
2. `PatternRecommender` クラス実装
3. `analyzeContext()` 実装
4. `recommend()` 実装
5. `exportContextForCopilot()` 実装（Copilot連携用）
6. `npx musubix learn recommend` コマンド実装

#### 受入基準
- [ ] プロジェクトコンテキストが正しく解析される
- [ ] 関連パターンが推薦される
- [ ] Copilot連携用のコンテキスト出力が可能

#### ファイル
```
packages/pattern-mcp/src/recommender/
├── index.ts               # NEW
└── pattern-recommender.ts # NEW
```

---

### TSK-PTN-006: Pattern Apply実装
**優先度**: P2  
**見積もり**: 1時間  
**依存**: TSK-PTN-005  
**トレース**: REQ-PTN-006 → DES-PTN-004

#### 作業内容
1. `npx musubix learn apply <pattern-id>` コマンド実装
2. パターンテンプレート適用ロジック
3. プロジェクト固有のカスタマイズ

#### 受入基準
- [ ] パターンIDを指定してコード生成可能

#### ファイル
```
packages/core/src/cli/commands/
└── learn.ts  # MODIFIED
```

---

## 4. Expert-Delegation Integration タスク（EXD）

### TSK-EXD-001: Scaffold Expert Integrator実装
**優先度**: P1  
**見積もり**: 1.5時間  
**依存**: TSK-SCF-005  
**トレース**: REQ-EXD-001, REQ-EXD-002 → DES-EXD-001, DES-EXD-002

#### 作業内容
1. `packages/expert-delegation/src/integrators/scaffold-expert-integrator.ts` を新規作成
2. `ScaffoldExpertIntegrator` クラス実装
3. `analyzeWithArchitect()` 実装
4. タイムアウト・fallback実装（ADR-v3.3.0-002準拠）
5. `--expert` オプション対応

#### 受入基準
- [ ] `npx musubix scaffold domain-model test -e "Order" --expert` が動作
- [ ] タイムアウト時にfallbackで基本scaffold実行
- [ ] Architect分析結果が出力される

#### ファイル
```
packages/expert-delegation/src/integrators/
├── index.ts                       # NEW
├── scaffold-expert-integrator.ts  # NEW
└── security-expert-integrator.ts  # NEW
```

---

### TSK-EXD-002: Security Expert Integrator実装
**優先度**: P1  
**見積もり**: 1時間  
**依存**: TSK-EXD-001  
**トレース**: REQ-EXD-002 → DES-EXD-002

#### 作業内容
1. `security-expert-integrator.ts` を新規作成
2. `SecurityExpertIntegrator` クラス実装
3. `reviewGeneratedCode()` 実装
4. `--security-check` オプション対応

#### 受入基準
- [ ] `npx musubix scaffold domain-model test -e "User" --security-check` が動作
- [ ] セキュリティ警告が出力される

#### ファイル
```
packages/expert-delegation/src/integrators/
└── security-expert-integrator.ts  # NEW
```

---

## 5. 非機能要件タスク（NFR）

### TSK-NFR-001: Performance Optimization
**優先度**: P1  
**見積もり**: 0.5時間  
**依存**: TSK-SCF-005  
**トレース**: REQ-NFR-001, REQ-NFR-002 → DES-NFR-001

#### 作業内容
1. `packages/core/src/cli/utils/performance.ts` を新規作成
2. 並列ファイル生成実装
3. パフォーマンス計測ユーティリティ

#### 受入基準
- [ ] 5エンティティのscaffoldが2秒以内
- [ ] 10エンティティのscaffoldが5秒以内

#### ファイル
```
packages/core/src/cli/utils/
└── performance.ts  # NEW
```

---

### TSK-NFR-002: Backward Compatibility
**優先度**: P1  
**見積もり**: 0.5時間  
**依存**: すべてのタスク  
**トレース**: REQ-NFR-003 → DES-NFR-002

#### 作業内容
1. `packages/core/src/cli/utils/compatibility.ts` を新規作成
2. v3.2.0プロジェクト互換性チェック
3. 学習データ互換性チェック

#### 受入基準
- [ ] v3.2.0で生成されたプロジェクトがv3.3.0で正常動作
- [ ] v3.2.0のlearning-data.jsonがv3.3.0で読み込み可能

#### ファイル
```
packages/core/src/cli/utils/
└── compatibility.ts  # NEW
```

---

### TSK-NFR-003: Integration Test
**優先度**: P0  
**見積もり**: 1時間  
**依存**: すべてのタスク  
**トレース**: 全REQ

#### 作業内容
1. E2E統合テスト作成
2. 全オプション組み合わせテスト
3. 既存テストとの互換性確認

#### 受入基準
- [ ] 全CLIオプションの統合テスト合格
- [ ] 既存4500+テストが引き続き合格

#### ファイル
```
packages/core/src/__tests__/
└── scaffold-integration.test.ts  # NEW
```

---

## 6. 実装順序

### Phase 1: 基盤（3時間）
```
TSK-SCF-001 (VO Generator)      ──┐
TSK-SCF-003 (Status Generator)  ──┼── 並行実装可
                                  │
TSK-SCF-002 (VO Tests)          ──┤
TSK-SCF-004 (Status Tests)      ──┘
```

### Phase 2: 統合（2時間）
```
TSK-SCF-005 (Scaffold統合)
    │
    ▼
TSK-SCF-006 (Result Aggregator)
```

### Phase 3: パターン学習（4時間）
```
TSK-PTN-001 (Auto Extractor)
    │
    ▼
TSK-PTN-002 (Pattern検出器)
    │
    ▼
TSK-PTN-003 (Library統合)
    │
    ▼
TSK-PTN-004 (Decay Manager)
    │
    ▼
TSK-PTN-005 (Recommender)
```

### Phase 4: Expert統合（2.5時間）
```
TSK-EXD-001 (Scaffold Expert)
    │
    ▼
TSK-EXD-002 (Security Expert)
```

### Phase 5: 最終確認（1.5時間）
```
TSK-NFR-001 (Performance)
    │
    ▼
TSK-NFR-002 (Compatibility)
    │
    ▼
TSK-NFR-003 (Integration Test)
```

---

## 7. トレーサビリティマトリクス

| タスクID | 要件ID | 設計ID | ファイル | 見積もり |
|----------|--------|--------|----------|---------|
| TSK-SCF-001 | REQ-SCF-001,002 | DES-SCF-001 | value-object-generator.ts | 1.5h |
| TSK-SCF-002 | REQ-SCF-001,002 | DES-SCF-001 | value-object-generator.test.ts | 0.5h |
| TSK-SCF-003 | REQ-SCF-003,004 | DES-SCF-002 | status-machine-generator.ts | 1.5h |
| TSK-SCF-004 | REQ-SCF-003,004 | DES-SCF-002 | status-machine-generator.test.ts | 0.5h |
| TSK-SCF-005 | REQ-SCF-001,003 | DES-SCF-001,002 | scaffold.ts | 1h |
| TSK-SCF-006 | REQ-SCF-005,006 | DES-SCF-003 | scaffold-result-aggregator.ts | 1h |
| TSK-PTN-001 | REQ-PTN-001 | DES-PTN-001 | auto-extractor.ts | 1.5h |
| TSK-PTN-002 | REQ-PTN-002 | DES-PTN-001 | auto-extractor.ts | 1h |
| TSK-PTN-003 | REQ-PTN-002 | DES-PTN-001 | learn.ts | 0.5h |
| TSK-PTN-004 | REQ-PTN-003,004 | DES-PTN-003 | pattern-decay-manager.ts | 1h |
| TSK-PTN-005 | REQ-PTN-005 | DES-PTN-004 | pattern-recommender.ts | 1.5h |
| TSK-PTN-006 | REQ-PTN-006 | DES-PTN-004 | learn.ts | 1h |
| TSK-EXD-001 | REQ-EXD-001 | DES-EXD-001 | scaffold-expert-integrator.ts | 1.5h |
| TSK-EXD-002 | REQ-EXD-002 | DES-EXD-002 | security-expert-integrator.ts | 1h |
| TSK-NFR-001 | REQ-NFR-001,002 | DES-NFR-001 | performance.ts | 0.5h |
| TSK-NFR-002 | REQ-NFR-003 | DES-NFR-002 | compatibility.ts | 0.5h |
| TSK-NFR-003 | 全REQ | 全DES | scaffold-integration.test.ts | 1h |

---

## 8. 承認

| 役割 | 氏名 | 日付 | 署名 |
|------|------|------|------|
| 作成者 | AI Agent | 2026-01-14 | ✓ |
| レビュアー | | | |
| 承認者 | | | |

---

**文書終了**
