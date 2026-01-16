# TSK-DR-v3.4.0 - Deep Research Integration タスク分解書

| 項目 | 内容 |
|-----|------|
| **Document ID** | TSK-DR-v3.4.0 |
| **Version** | 1.1 |
| **Status** | ✅ Approved |
| **Author** | MUSUBIX AI Agent |
| **Created** | 2026-01-16 |
| **Last Updated** | 2026-01-16 |
| **Traceability** | DES-DR-v3.4.0, REQ-MUSUBIX-v3.4.0 |

---

## 1. タスク分解概要

### 1.1 目的

本タスク分解書は、DES-DR-v3.4.0で定義された設計を実装可能なタスク単位に分解する。各タスクは以下の要件を満たす：

1. **実装サイズ**: 2-8時間で完了可能
2. **独立性**: 依存関係が明確で並列実行可能
3. **テスタビリティ**: 単体テストで検証可能
4. **トレーサビリティ**: REQ/DES/TSK/TSTの完全追跡

### 1.2 タスク分類

| カテゴリ | タスク数 | 概要 |
|---------|---------|------|
| **Foundation** | 13 | Engine、Providers、Knowledge、Utils |
| **Security** | 3 | SecretManager、ContentSanitizer、SecureLogger |
| **Performance** | 3 | ParallelExecutor、CachingLayer、ResourceMonitor |
| **Integration** | 6 | Expert/Neural/Orchestrator/Knowledge/Workflow/MCP |
| **CLI/MCP** | 2 | ✅ CLI Tool（完了）、✅ MCP Tools（完了） |
| **Testing** | 1 | E2E Tests |
| **Error Handling** | 1 | 包括的エラーハンドリング |
| **Total** | 29 | |

### 1.3 実装状況

| 状態 | タスク数 | 割合 |
|-----|---------|------|
| ✅ **完了** | 2 | 7% (TSK-DR-019, TSK-DR-020) |
| ⏳ **未着手** | 27 | 93% |
| **Total** | 29 | 100% |

---

## 2. Foundation タスク（13タスク）

### TSK-DR-001: ResearchEngine - Template Method実装

**優先度**: P0（必須）  
**見積**: 8時間  
**担当**: Phase 4-4  
**依存**: なし

#### 目的
ResearchEngineのTemplate Methodパターン実装。

#### 実装内容
1. `ResearchEngine`クラス作成
2. Template Methodの実装:
   - `research()`: メインメソッド
   - `initialize()`: 初期化
   - `generateQuestions()`: 質問生成
   - `search()`: 検索実行
   - `read()`: Webページ読み取り
   - `reason()`: 推論実行
   - `evaluate()`: 進捗評価
   - `shouldStop()`: 終了判定
   - `generateReport()`: レポート生成
3. 進捗コールバック機構
4. エラーハンドリング

#### 成果物
- `packages/deep-research/src/engine/research-engine.ts` (300-400行)
- `packages/deep-research/src/engine/research-engine.test.ts` (150-200行)

#### 受け入れ基準
- [ ] Template Methodパターン実装
- [ ] 10イテレーション実行可能
- [ ] 進捗コールバック動作
- [ ] テストカバレッジ >90%

#### トレーサビリティ
- **REQ**: REQ-DR-CORE-001
- **DES**: ResearchEngine (Section 2.4)
- **TST**: research-engine.test.ts

---

### TSK-DR-002: JinaProvider実装

**優先度**: P0（必須）  
**見積**: 4時間  
**担当**: Phase 4-4  
**依存**: なし

#### 目的
Jina Search API統合によるWeb検索機能。

#### 実装内容
1. `JinaProvider`クラス作成（SearchProvider実装）
2. Jina Search API呼び出し:
   - `search()`: 検索実行
   - `validateConfig()`: API key検証
3. レスポンスパース（JSON→SearchResult[]）
4. エラーハンドリング（ネットワークエラー、APIエラー）
5. Jina Reader API統合（Webページ読み取り）

#### 成果物
- `packages/deep-research/src/providers/jina-provider.ts` (150-200行)
- `packages/deep-research/src/providers/jina-provider.test.ts` (100-150行)

#### 受け入れ基準
- [ ] Jina Search API呼び出し成功
- [ ] SearchResult型への変換成功
- [ ] API keyなし時のエラーハンドリング
- [ ] テストカバレッジ >85%

#### トレーサビリティ
- **REQ**: REQ-DR-CORE-002, REQ-DR-CORE-003
- **DES**: SearchProvider (Section 3.3)
- **TST**: jina-provider.test.ts

---

### TSK-DR-003: BraveProvider実装

**優先度**: P1（重要）  
**見積**: 4時間  
**担当**: Phase 4-4  
**依存**: なし

#### 目的
Brave Search API統合によるWeb検索機能。

#### 実装内容
1. `BraveProvider`クラス作成（SearchProvider実装）
2. Brave Search API呼び出し:
   - `search()`: 検索実行
   - `validateConfig()`: API key検証
3. レスポンスパース（JSON→SearchResult[]）
4. エラーハンドリング

#### 成果物
- `packages/deep-research/src/providers/brave-provider.ts` (150-200行)
- `packages/deep-research/src/providers/brave-provider.test.ts` (100-150行)

#### 受け入れ基準
- [ ] Brave Search API呼び出し成功
- [ ] SearchResult型への変換成功
- [ ] API keyなし時のエラーハンドリング
- [ ] テストカバレッジ >85%

#### トレーサビリティ
- **REQ**: REQ-DR-CORE-002
- **DES**: SearchProvider (Section 3.3)
- **TST**: brave-provider.test.ts

---

### TSK-DR-004: DuckDuckGoProvider実装

**優先度**: P2（任意）  
**見積**: 4時間  
**担当**: Phase 4-4  
**依存**: なし

#### 目的
DuckDuckGo検索統合（API keyなし）。

#### 実装内容
1. `DuckDuckGoProvider`クラス作成（SearchProvider実装）
2. DuckDuckGo検索（HTML Scraping or unofficial API）:
   - `search()`: 検索実行
   - `validateConfig()`: 設定検証（API keyなし）
3. レスポンスパース（HTML→SearchResult[]）
4. Rate limiting対応

#### 成果物
- `packages/deep-research/src/providers/duckduckgo-provider.ts` (150-200行)
- `packages/deep-research/src/providers/duckduckgo-provider.test.ts` (100-150行)

#### 受け入れ基準
- [ ] DuckDuckGo検索成功
- [ ] SearchResult型への変換成功
- [ ] Rate limiting対応
- [ ] テストカバレッジ >80%

#### トレーサビリティ
- **REQ**: REQ-DR-CORE-002
- **DES**: SearchProvider (Section 3.3)
- **TST**: duckduckgo-provider.test.ts

---

### TSK-DR-005: VSCodeLMProvider実装

**優先度**: P0（必須）  
**見積**: 6時間  
**担当**: Phase 4-4  
**依存**: なし

#### 目的
VS Code LM API統合によるLM推論機能。

#### 実装内容
1. `VSCodeLMProvider`クラス作成（LMProvider実装）
2. VS Code LM API呼び出し:
   - `generateText()`: テキスト生成
   - `checkAvailability()`: モデル利用可能性確認
3. ストリーミング対応（for await...of）
4. トークン数カウント
5. エラーハンドリング（モデル未選択、リクエスト失敗）

#### 成果物
- `packages/deep-research/src/providers/vscode-lm-provider.ts` (150-200行)
- `packages/deep-research/src/providers/vscode-lm-provider.test.ts` (100-150行)

#### 受け入れ基準
- [ ] vscode.lm.sendRequest()呼び出し成功
- [ ] ストリーミングレスポンス処理
- [ ] LMResponse型への変換成功
- [ ] テストカバレッジ >85%

#### トレーサビリティ
- **REQ**: REQ-DR-CORE-004, REQ-DR-INT-001
- **DES**: LMProvider (Section 3.4)
- **TST**: vscode-lm-provider.test.ts

---

### TSK-DR-006: ExpertDelegationProvider実装

**優先度**: P1（重要）  
**見積**: 6時間  
**担当**: Phase 4-4  
**依存**: なし

#### 目的
Expert Delegation統合によるAIエキスパート委譲。

#### 実装内容
1. `ExpertDelegationProvider`クラス作成（LMProvider実装）
2. ExpertDelegator統合:
   - `generateText()`: エキスパートに委譲
   - `selectExpert()`: プロンプトベースのエキスパート選択
   - `checkAvailability()`: エキスパート利用可能性確認
3. エキスパート選択ロジック（research/analysis/synthesis）
4. タイムアウト・フォールバック対応

#### 成果物
- `packages/deep-research/src/providers/expert-delegation-provider.ts` (150-200行)
- `packages/deep-research/src/providers/expert-delegation-provider.test.ts` (100-150行)

#### 受け入れ基準
- [ ] ExpertDelegator.consult()呼び出し成功
- [ ] エキスパート選択ロジック動作
- [ ] タイムアウト・フォールバック動作
- [ ] テストカバレッジ >85%

#### トレーサビリティ
- **REQ**: REQ-DR-INT-002
- **DES**: ExpertDelegationProvider (Section 5.1)
- **TST**: expert-delegation-provider.test.ts

---

### TSK-DR-007: KnowledgeBase実装

**優先度**: P0（必須）  
**見積**: 6時間  
**担当**: Phase 4-4  
**依存**: なし

#### 目的
知識グラフによる学習済み情報管理。

#### 実装内容
1. `KnowledgeBase`クラス作成
2. インメモリ知識グラフ:
   - `addItems()`: 知識項目追加
   - `getItems()`: 全知識項目取得
   - `query()`: キーワード検索
   - `getRelated()`: 関連知識項目取得
3. 重複検出・マージ
4. 信頼度スコアリング
5. @musubix/knowledge統合（永続化）

#### 成果物
- `packages/deep-research/src/knowledge/knowledge-base.ts` (200-250行)
- `packages/deep-research/src/knowledge/knowledge-base.test.ts` (150-200行)

#### 受け入れ基準
- [ ] 知識項目の追加・取得動作
- [ ] キーワード検索動作
- [ ] 重複検出・マージ動作
- [ ] テストカバレッジ >90%

#### トレーサビリティ
- **REQ**: REQ-DR-CORE-005, REQ-DR-INT-008
- **DES**: KnowledgeBase (Section 5.4)
- **TST**: knowledge-base.test.ts

---

### TSK-DR-008: QuestionGenerator実装

**優先度**: P0（必須）  
**見積**: 5時間  
**担当**: Phase 4-4  
**依存**: TSK-DR-005 (VSCodeLMProvider)

#### 目的
反省的質問生成によるリサーチクエリ拡張。

#### 実装内容
1. `QuestionGenerator`クラス作成
2. LM prompting:
   - `generateReflectiveQuestions()`: 質問生成
   - プロンプトテンプレート設計
3. 質問優先度付け
4. 既存知識ベースの活用
5. 質問数制御（デフォルト3-5個）

#### 成果物
- `packages/deep-research/src/reasoning/question-generator.ts` (150-200行)
- `packages/deep-research/src/reasoning/question-generator.test.ts` (100-150行)

#### 受け入れ基準
- [ ] LMによる質問生成動作
- [ ] 優先度付け動作
- [ ] 質問数制御動作
- [ ] テストカバレッジ >85%

#### トレーサビリティ
- **REQ**: REQ-DR-CORE-006, REQ-DR-CORE-009
- **DES**: QuestionGenerator (Section 2.3)
- **TST**: question-generator.test.ts

---

### TSK-DR-009: KnowledgeReasoner実装

**優先度**: P0（必須）  
**見積**: 6時間  
**担当**: Phase 4-4  
**依存**: TSK-DR-005 (VSCodeLMProvider), TSK-DR-007 (KnowledgeBase)

#### 目的
Webコンテンツからの知識抽出・推論。

#### 実装内容
1. `KnowledgeReasoner`クラス作成
2. LM推論:
   - `analyzeAndReason()`: コンテンツ分析
   - プロンプトテンプレート設計（事実抽出）
3. 事実抽出（structured output）
4. 信頼度スコアリング
5. KnowledgeBase統合

#### 成果物
- `packages/deep-research/src/reasoning/knowledge-reasoner.ts` (200-250行)
- `packages/deep-research/src/reasoning/knowledge-reasoner.test.ts` (150-200行)

#### 受け入れ基準
- [ ] Webコンテンツから事実抽出
- [ ] 信頼度スコアリング動作
- [ ] KnowledgeBase統合動作
- [ ] テストカバレッジ >85%

#### トレーサビリティ
- **REQ**: REQ-DR-CORE-004, REQ-DR-CORE-005
- **DES**: KnowledgeReasoner (Section 2.3)
- **TST**: knowledge-reasoner.test.ts

---

### TSK-DR-010: AnswerEvaluator実装

**優先度**: P0（必須）  
**見積**: 5時間  
**担当**: Phase 4-4  
**依存**: TSK-DR-005 (VSCodeLMProvider), TSK-DR-007 (KnowledgeBase)

#### 目的
進捗評価と終了判定。

#### 実装内容
1. `AnswerEvaluator`クラス作成
2. LM評価:
   - `evaluateProgress()`: 進捗評価
   - プロンプトテンプレート設計（自己評価）
3. 信頼度スコアリング（0-1）
4. 終了判定ロジック:
   - 信頼度 >0.8 or イテレーション上限
5. 決定的回答検出

#### 成果物
- `packages/deep-research/src/reasoning/answer-evaluator.ts` (150-200行)
- `packages/deep-research/src/reasoning/answer-evaluator.test.ts` (100-150行)

#### 受け入れ基準
- [ ] 進捗評価動作
- [ ] 信頼度スコアリング動作
- [ ] 終了判定動作
- [ ] テストカバレッジ >85%

#### トレーサビリティ
- **REQ**: REQ-DR-CORE-007
- **DES**: AnswerEvaluator (Section 2.3)
- **TST**: answer-evaluator.test.ts

---

### TSK-DR-011: ReportGenerator実装

**優先度**: P0（必須）  
**見積**: 5時間  
**担当**: Phase 4-4  
**依存**: TSK-DR-007 (KnowledgeBase)

#### 目的
Markdown/JSONレポート生成。

#### 実装内容
1. `ReportGenerator`クラス作成
2. レポート生成:
   - `generateMarkdown()`: Markdown形式
   - `generateJSON()`: JSON形式
3. セクション構造:
   - クエリ
   - 回答
   - 信頼度
   - 参考文献（References）
   - 知識グラフ
   - メトリクス（イテレーション、トークン、時間）
4. テンプレートエンジン（Handlebars or 文字列テンプレート）

#### 成果物
- `packages/deep-research/src/reporters/report-generator.ts` (200-250行)
- `packages/deep-research/src/reporters/report-generator.test.ts` (100-150行)

#### 受け入れ基準
- [ ] Markdownレポート生成動作
- [ ] JSONレポート生成動作
- [ ] 全セクション含まれる
- [ ] テストカバレッジ >90%

#### トレーサビリティ
- **REQ**: REQ-DR-CORE-008, REQ-DR-CORE-010
- **DES**: ReportGenerator (Section 2.3)
- **TST**: report-generator.test.ts

---

### TSK-DR-012: TrajectoryLogger実装

**優先度**: P1（重要）  
**見積**: 4時間  
**担当**: Phase 4-4  
**依存**: なし

#### 目的
反復ログとパフォーマンスメトリクスの記録。

#### 実装内容
1. `TrajectoryLogger`クラス作成
2. ログ記録:
   - `logIteration()`: 反復ログ
   - `logPhase()`: フェーズログ
   - `logMetrics()`: メトリクスログ
3. ログ構造化（IterationLog型）
4. エクスポート機能（JSON, Parquet）
5. ログ圧縮（大量ログ対応）

#### 成果物
- `packages/deep-research/src/utils/trajectory-logger.ts` (150-200行)
- `packages/deep-research/src/utils/trajectory-logger.test.ts` (100-150行)

#### 受け入れ基準
- [ ] 反復ログ記録動作
- [ ] メトリクスログ動作
- [ ] JSONエクスポート動作
- [ ] テストカバレッジ >85%

#### トレーサビリティ
- **REQ**: REQ-DR-NFR-006
- **DES**: TrajectoryLogger (Section 2.3)
- **TST**: trajectory-logger.test.ts

---

### TSK-DR-013: TokenTracker実装

**優先度**: P0（必須）  
**見積**: 3時間  
**担当**: Phase 4-4  
**依存**: なし

#### 目的
トークン使用量追跡と予算管理。

#### 実装内容
1. `TokenTracker`クラス作成
2. トークン追跡:
   - `addTokens()`: トークン加算
   - `getRemainingBudget()`: 残予算取得
   - `isBudgetExceeded()`: 予算超過判定
3. 予算超過時のエラー
4. メトリクス取得

#### 成果物
- `packages/deep-research/src/utils/token-tracker.ts` (100-150行)
- `packages/deep-research/src/utils/token-tracker.test.ts` (80-100行)

#### 受け入れ基準
- [ ] トークン追跡動作
- [ ] 予算超過検出動作
- [ ] エラー送出動作
- [ ] テストカバレッジ >90%

#### トレーサビリティ
- **REQ**: REQ-DR-NFR-002
- **DES**: ResourceMonitor (Section 7.3)
- **TST**: token-tracker.test.ts

---

## 3. Security タスク（3タスク）

### TSK-DR-014: SecretManager実装

**優先度**: P0（必須）  
**見積**: 3時間  
**担当**: Phase 4-5  
**依存**: なし

#### 目的
API key管理と秘匿化。

#### 実装内容
1. `SecretManager`クラス作成
2. シークレット管理:
   - `setSecret()`: API key保存
   - `getSecret()`: API key取得
   - `redact()`: テキストからAPI key除去
3. メモリ内保持（永続化なし）
4. ログ出力時の自動秘匿

#### 成果物
- `packages/deep-research/src/security/secret-manager.ts` (100-150行)
- `packages/deep-research/src/security/secret-manager.test.ts` (80-100行)

#### 受け入れ基準
- [ ] API key保存・取得動作
- [ ] Redact機能動作
- [ ] ログ秘匿動作
- [ ] テストカバレッジ >90%

#### トレーサビリティ
- **REQ**: REQ-DR-NFR-003
- **DES**: SecretManager (Section 6.1)
- **TST**: secret-manager.test.ts

---

### TSK-DR-015: ContentSanitizer実装

**優先度**: P0（必須）  
**見積**: 4時間  
**担当**: Phase 4-5  
**依存**: なし

#### 目的
XSS防止とコンテンツサニタイゼーション。

#### 実装内容
1. `ContentSanitizer`クラス作成
2. サニタイゼーション:
   - `sanitizeHTML()`: HTMLタグ除去
   - `detectMalicious()`: 悪意あるコンテンツ検出
   - `isSafeURL()`: URL安全性検証
3. ホワイトリストベースのフィルタリング
4. スクリプトタグ・イベントハンドラーの除去

#### 成果物
- `packages/deep-research/src/security/content-sanitizer.ts` (150-200行)
- `packages/deep-research/src/security/content-sanitizer.test.ts` (100-150行)

#### 受け入れ基準
- [ ] HTML sanitization動作
- [ ] 悪意あるコンテンツ検出動作
- [ ] URL検証動作
- [ ] テストカバレッジ >90%

#### トレーサビリティ
- **REQ**: REQ-DR-NFR-003
- **DES**: ContentSanitizer (Section 6.2)
- **TST**: content-sanitizer.test.ts

---

### TSK-DR-016: SecureLogger実装

**優先度**: P1（重要）  
**見積**: 3時間  
**担当**: Phase 4-5  
**依存**: TSK-DR-014 (SecretManager)

#### 目的
秘匿化ロギング。

#### 実装内容
1. `SecureLogger`クラス作成
2. ロギング:
   - `log()`: 自動秘匿ログ
   - `redactObject()`: オブジェクト再帰秘匿
3. SecretManager統合
4. 構造化ログ対応（JSON）

#### 成果物
- `packages/deep-research/src/security/secure-logger.ts` (100-150行)
- `packages/deep-research/src/security/secure-logger.test.ts` (80-100行)

#### 受け入れ基準
- [ ] 自動秘匿ログ動作
- [ ] オブジェクト再帰秘匿動作
- [ ] 構造化ログ動作
- [ ] テストカバレッジ >90%

#### トレーサビリティ
- **REQ**: REQ-DR-NFR-003
- **DES**: SecureLogger (Section 6.3)
- **TST**: secure-logger.test.ts

---

## 4. Performance タスク（3タスク）

### TSK-DR-017: ParallelExecutor実装

**優先度**: P0（必須）  
**見積**: 4時間  
**担当**: Phase 4-6  
**依存**: なし

#### 目的
並列実行による高速化（5秒以内応答）。

#### 実装内容
1. `ParallelExecutor`クラス作成
2. 並列実行:
   - `readWebPages()`: 並列Webページ読み取り
   - `searchMultipleProviders()`: 並列検索
3. p-limit統合（最大5並列）
4. エラーハンドリング（部分失敗許容）
5. タイムアウト対応

#### 成果物
- `packages/deep-research/src/performance/parallel-executor.ts` (150-200行)
- `packages/deep-research/src/performance/parallel-executor.test.ts` (100-150行)

#### 受け入れ基準
- [ ] 並列実行動作（最大5）
- [ ] 部分失敗許容動作
- [ ] タイムアウト動作
- [ ] テストカバレッジ >85%

#### トレーサビリティ
- **REQ**: REQ-DR-NFR-001
- **DES**: ParallelExecutor (Section 7.1)
- **TST**: parallel-executor.test.ts

---

### TSK-DR-018: CachingLayer実装

**優先度**: P1（重要）  
**見積**: 5時間  
**担当**: Phase 4-6  
**依存**: なし

#### 目的
LRUキャッシングによる高速化。

#### 実装内容
1. `LRUCache`クラス作成
2. キャッシュ機能:
   - `get()`: キャッシュ取得
   - `set()`: キャッシュ保存
   - `evictLRU()`: LRU削除
3. TTL対応（1-2時間）
4. ヒット率計測
5. `CachingLayer`クラス（SearchResult、WebContentキャッシュ）

#### 成果物
- `packages/deep-research/src/performance/lru-cache.ts` (150-200行)
- `packages/deep-research/src/performance/caching-layer.ts` (100-150行)
- `packages/deep-research/src/performance/caching-layer.test.ts` (150-200行)

#### 受け入れ基準
- [ ] LRUキャッシュ動作
- [ ] TTL expiration動作
- [ ] ヒット率計測動作
- [ ] テストカバレッジ >85%

#### トレーサビリティ
- **REQ**: REQ-DR-NFR-004
- **DES**: CachingLayer (Section 7.2)
- **TST**: caching-layer.test.ts

---

### TSK-DR-019: ✅ CLI Tool実装（完了）

**優先度**: P0（必須）  
**見積**: 6時間  
**担当**: Phase 4-3  
**依存**: なし

#### 目的
`npx musubix deep-research <query>`コマンド実装。

#### 実装内容
1. ✅ `deep-research.ts`コマンド作成
2. ✅ Commander.js統合
3. ✅ オプション定義:
   - `-i, --max-iterations`
   - `-t, --token-budget`
   - `-o, --output`
   - `-f, --format`
   - `-p, --provider`
   - `-v, --verbose`
4. ✅ 進捗表示（コンソール出力）
5. ✅ ファイル出力（Markdown/JSON）
6. ✅ エラーハンドリング

#### 成果物
- ✅ `packages/core/src/cli/commands/deep-research.ts` (268行)
- ✅ ビルド成功、実行可能

#### 受け入れ基準
- [x] ✅ コマンド実行成功
- [x] ✅ 全オプション動作
- [x] ✅ 進捗表示動作
- [x] ✅ ファイル出力動作

#### トレーサビリティ
- **REQ**: REQ-DR-INT-006
- **DES**: CLI API (Section 3.6)
- **TST**: 手動テスト完了

---

### TSK-DR-020: ✅ MCP Tools実装（完了）

**優先度**: P0（必須）  
**見積**: 6時間  
**担当**: Phase 4-3  
**依存**: なし

#### 目的
3つのMCPツール実装（start/status/report）。

#### 実装内容
1. ✅ `DeepResearchMCPHandler`クラス作成
2. ✅ セッション管理（Map<string, ResearchSession>）
3. ✅ 3ツール実装:
   - `deep_research_start`: セッション作成
   - `deep_research_status`: ステータス取得
   - `deep_research_report`: レポート生成
4. ✅ JSON Schema定義
5. ✅ エラーハンドリング

#### 成果物
- ✅ `packages/deep-research/src/mcp/tools.ts` (410行)
- ✅ `packages/deep-research/src/mcp/tools.test.ts` (13/13テスト合格)

#### 受け入れ基準
- [x] ✅ 3ツール動作確認
- [x] ✅ セッション管理動作
- [x] ✅ JSON Schema検証
- [x] ✅ テストカバレッジ 100%

#### トレーサビリティ
- **REQ**: REQ-DR-INT-005
- **DES**: MCP Tools API (Section 3.5)
- **TST**: tools.test.ts (13/13合格)

---

## 5. Integration タスク（6タスク）

### TSK-DR-021: VS Code Extension統合

**優先度**: P0（必須）  
**見積**: 8時間  
**担当**: Phase 4-7  
**依存**: TSK-DR-001, TSK-DR-020

#### 目的
VS Code拡張機能としてDeep Researchを統合。

#### 実装内容
1. VS Code Extension API統合
2. コマンドパレット登録:
   - `MUSUBIX: Deep Research`
3. WebViewパネル（進捗表示）
4. Output Channel（ログ出力）
5. Settings統合（maxIterations、tokenBudget等）
6. MCP Client統合

#### 成果物
- `packages/vscode-extension/src/commands/deep-research.ts` (200-300行)
- `packages/vscode-extension/src/views/deep-research-panel.ts` (150-200行)

#### 受け入れ基準
- [ ] コマンドパレットから実行可能
- [ ] WebViewで進捗表示
- [ ] Output Channelでログ表示
- [ ] Settings統合動作

#### トレーサビリティ
- **REQ**: REQ-DR-INT-006
- **DES**: CLI/MCP統合 (Section 3)
- **TST**: 手動テスト

---

### TSK-DR-022: Expert Delegation統合

**優先度**: P1（重要）  
**見積**: 6時間  
**担当**: Phase 4-7  
**依存**: TSK-DR-006

#### 目的
@nahisaho/musubix-expert-delegation統合。

#### 実装内容
1. ExpertDelegationProviderの統合
2. エキスパートタイプ選択ロジック改善
3. タイムアウト・フォールバック検証
4. E2Eテスト

#### 成果物
- `packages/deep-research/src/integration/expert-delegation.test.ts` (100-150行)

#### 受け入れ基準
- [ ] ExpertDelegator呼び出し成功
- [ ] エキスパート選択動作
- [ ] タイムアウト動作
- [ ] E2Eテスト合格

#### トレーサビリティ
- **REQ**: REQ-DR-INT-002
- **DES**: Expert Delegation統合 (Section 5.1)
- **TST**: expert-delegation.test.ts

---

### TSK-DR-023: Neural Search統合

**優先度**: P1（重要）  
**見積**: 6時間  
**担当**: Phase 4-7  
**依存**: なし

#### 目的
@nahisaho/musubix-neural-search統合。

#### 実装内容
1. NeuralSearchProviderの実装
2. @musubix/knowledge統合によるローカル検索
3. ハイブリッドランキング（BM25 + ベクトル類似度）
4. E2Eテスト

#### 成果物
- `packages/deep-research/src/providers/neural-search-provider.ts` (150-200行)
- `packages/deep-research/src/providers/neural-search-provider.test.ts` (100-150行)

#### 受け入れ基準
- [ ] NeuralSearchEngine呼び出し成功
- [ ] ハイブリッドランキング動作
- [ ] ローカル検索動作
- [ ] E2Eテスト合格

#### トレーサビリティ
- **REQ**: REQ-DR-INT-003
- **DES**: Neural Search統合 (Section 5.2)
- **TST**: neural-search-provider.test.ts

---

### TSK-DR-024: Agent Orchestrator統合

**優先度**: P2（任意）  
**見積**: 6時間  
**担当**: Phase 4-7  
**依存**: TSK-DR-001

#### 目的
@nahisaho/musubix-agent-orchestrator統合。

#### 実装内容
1. OrchestrationEngineの実装
2. タスク複雑度分析
3. サブリサーチ分解
4. 並列実行統合
5. E2Eテスト

#### 成果物
- `packages/deep-research/src/integration/orchestration-engine.ts` (150-200行)
- `packages/deep-research/src/integration/orchestration-engine.test.ts` (100-150行)

#### 受け入れ基準
- [ ] AgentOrchestrator呼び出し成功
- [ ] タスク分解動作
- [ ] 並列実行動作
- [ ] E2Eテスト合格

#### トレーサビリティ
- **REQ**: REQ-DR-INT-004
- **DES**: Agent Orchestrator統合 (Section 5.3)
- **TST**: orchestration-engine.test.ts

---

### TSK-DR-025: Knowledge Store統合

**優先度**: P1（重要）  
**見積**: 4時間  
**担当**: Phase 4-7  
**依存**: TSK-DR-007

#### 目的
@musubix/knowledge統合による知識永続化。

#### 実装内容
1. KnowledgeBaseへの@musubix/knowledge統合
2. エンティティ型定義（fact）
3. リレーション追加（tracesTo）
4. クエリ最適化
5. E2Eテスト

#### 成果物
- `packages/deep-research/src/integration/knowledge-store.test.ts` (100-150行)

#### 受け入れ基準
- [ ] KnowledgeStore呼び出し成功
- [ ] エンティティ追加動作
- [ ] クエリ動作
- [ ] E2Eテスト合格

#### トレーサビリティ
- **REQ**: REQ-DR-INT-008
- **DES**: Knowledge Store統合 (Section 5.4)
- **TST**: knowledge-store.test.ts

---

### TSK-DR-026: Workflow Engine統合

**優先度**: P2（任意）  
**見積**: 6時間  
**担当**: Phase 4-7  
**依存**: TSK-DR-001

#### 目的
@nahisaho/musubix-workflow-engine統合。

#### 実装内容
1. ResearchWorkflowの実装
2. 5フェーズ定義（initialization/iteration/synthesis/reporting/completion）
3. 品質ゲート定義
4. フェーズ遷移検証
5. E2Eテスト

#### 成果物
- `packages/deep-research/src/integration/research-workflow.ts` (150-200行)
- `packages/deep-research/src/integration/research-workflow.test.ts` (100-150行)

#### 受け入れ基準
- [ ] WorkflowEngine呼び出し成功
- [ ] フェーズ遷移動作
- [ ] 品質ゲート検証動作
- [ ] E2Eテスト合格

#### トレーサビリティ
- **REQ**: REQ-DR-INT-009
- **DES**: Workflow Engine統合 (Section 5.5)
- **TST**: research-workflow.test.ts

---

## 6. Testing タスク（1タスク）

### TSK-DR-027: E2Eテスト

**優先度**: P0（必須）  
**見積**: 6時間  
**担当**: Phase 4-8  
**依存**: すべてのタスク

#### 目的
End-to-Endシナリオテスト。

#### 実装内容
1. E2Eテストスイート作成
2. シナリオ:
   - Scenario 1: 単純な質問（"What is TypeScript?"）
   - Scenario 2: 複雑な質問（"Compare Lean 4 and Coq for formal verification"）
   - Scenario 3: API keyなし（DuckDuckGoフォールバック）
   - Scenario 4: トークン予算超過
   - Scenario 5: ネットワークエラー
3. モック統合（LM API、Search API）
4. メトリクス検証（5秒以内、15,000トークン以内）

#### 成果物
- `packages/deep-research/src/test/e2e.test.ts` (200-300行)

#### 受け入れ基準
- [ ] 5シナリオすべて合格
- [ ] パフォーマンス基準達成
- [ ] エラーハンドリング検証
- [ ] テストカバレッジ全体 >85%

#### トレーサビリティ
- **REQ**: すべての要件
- **DES**: すべての設計
- **TST**: e2e.test.ts

---

## 7. Error Handling タスク（1タスク）

### TSK-DR-028: エラーハンドリング最終化

**優先度**: P0（必須）  
**見積**: 4時間  
**担当**: Phase 4-8  
**依存**: すべてのタスク

#### 目的
包括的エラーハンドリングの最終化。

#### 実装内容
1. すべてのエラーケース検証
2. カスタムErrorクラスの一貫性確認
3. エラーメッセージの改善
4. フォールバック処理の検証
5. エラードキュメント作成

#### 成果物
- `packages/deep-research/docs/ERROR-HANDLING.md` (50-100行)
- 各ファイルのエラーハンドリング改善

#### 受け入れ基準
- [ ] すべてのエラーケースでカスタムError使用
- [ ] エラーメッセージが明確
- [ ] フォールバック動作検証
- [ ] エラードキュメント完備

#### トレーサビリティ
- **REQ**: REQ-DR-NFR-005
- **DES**: Error Types (Section 4.2)
- **TST**: 各テストファイル

---

## 8. タスク依存関係グラフ

```
Phase 4-4: Foundation & Integration
├── TSK-DR-001: ResearchEngine (8h)
├── TSK-DR-002: JinaProvider (4h)
├── TSK-DR-003: BraveProvider (4h)
├── TSK-DR-004: DuckDuckGoProvider (4h)
├── TSK-DR-005: VSCodeLMProvider (6h)
│   └── TSK-DR-008: QuestionGenerator (5h)
│   └── TSK-DR-009: KnowledgeReasoner (6h)
│   └── TSK-DR-010: AnswerEvaluator (5h)
├── TSK-DR-006: ExpertDelegationProvider (6h)
├── TSK-DR-007: KnowledgeBase (6h)
│   └── TSK-DR-009: KnowledgeReasoner (6h)
│   └── TSK-DR-010: AnswerEvaluator (5h)
│   └── TSK-DR-011: ReportGenerator (5h)
├── TSK-DR-011: ReportGenerator (5h)
├── TSK-DR-012: TrajectoryLogger (4h)
└── TSK-DR-013: TokenTracker (3h)

Phase 4-5: Security
├── TSK-DR-014: SecretManager (3h)
│   └── TSK-DR-016: SecureLogger (3h)
├── TSK-DR-015: ContentSanitizer (4h)
└── TSK-DR-016: SecureLogger (3h)

Phase 4-6: Performance
├── TSK-DR-017: ParallelExecutor (4h)
├── TSK-DR-018: CachingLayer (5h)
├── ✅ TSK-DR-019: CLI Tool (完了)
└── ✅ TSK-DR-020: MCP Tools (完了)

Phase 4-7: Integration & VS Code Extension
├── TSK-DR-021: VS Code Extension (8h) [依存: TSK-DR-001, TSK-DR-020]
├── TSK-DR-022: Expert Delegation (6h) [依存: TSK-DR-006]
├── TSK-DR-023: Neural Search (6h)
├── TSK-DR-024: Agent Orchestrator (6h) [依存: TSK-DR-001]
├── TSK-DR-025: Knowledge Store (4h) [依存: TSK-DR-007]
└── TSK-DR-026: Workflow Engine (6h) [依存: TSK-DR-001]

Phase 4-8: Testing & Error Handling
├── TSK-DR-027: E2E Tests (6h) [依存: すべて]
└── TSK-DR-028: Error Handling (4h) [依存: すべて]
```

---

## 9. 工数見積とスケジュール

### 9.1 総工数

| カテゴリ | タスク数 | 総工数 | 平均工数 |
|---------|---------|-------|---------|
| Foundation | 13 | 66時間 | 5.1時間 |
| Security | 3 | 10時間 | 3.3時間 |
| Performance | 4 | 15時間 (2完了) | 3.8時間 |
| Integration | 6 | 36時間 | 6.0時間 |
| Testing | 1 | 6時間 | 6.0時間 |
| Error Handling | 1 | 4時間 | 4.0時間 |
| **Total** | **28** | **137時間** (完了12時間除く) | **4.9時間** |

### 9.2 フェーズ別スケジュール

| Phase | タスク | 工数 | 並列化 | 実時間 |
|-------|--------|------|--------|--------|
| **Phase 4-4** | TSK-DR-001~013 | 66時間 | 3並列 | 22時間 (3日) |
| **Phase 4-5** | TSK-DR-014~016 | 10時間 | 2並列 | 5時間 (1日) |
| **Phase 4-6** | TSK-DR-017~018 | 9時間 | 2並列 | 5時間 (1日) |
| **Phase 4-7** | TSK-DR-021~026 | 36時間 | 3並列 | 12時間 (2日) |
| **Phase 4-8** | TSK-DR-027~028 | 10時間 | 1並列 | 10時間 (2日) |
| **Total** | | **131時間** | | **54時間 (9日)** |

*注: 並列化は独立タスクを同時実行可能と仮定*

### 9.3 優先度別タスク

| 優先度 | タスク数 | 概要 |
|--------|---------|------|
| **P0（必須）** | 16 | Engine、Providers、Knowledge、Security、CLI/MCP、E2E |
| **P1（重要）** | 8 | BraveProvider、TrajectoryLogger、SecureLogger、CachingLayer、統合 |
| **P2（任意）** | 3 | DuckDuckGoProvider、Agent Orchestrator、Workflow Engine |

**推奨実装順序**:
1. P0タスク → P1タスク → P2タスク
2. Foundation（TSK-DR-001~013）→ Security（TSK-DR-014~016）→ Performance（TSK-DR-017~018）→ Integration（TSK-DR-021~026）→ Testing（TSK-DR-027~028）

---

## 10. 受け入れ基準サマリー

### 10.1 全体メトリクス

| 指標 | 目標 | 測定方法 |
|-----|------|---------|
| **テストカバレッジ** | >85% | `npm run test:coverage` |
| **テスト合格率** | 100% | `npm test` |
| **ビルド成功** | 100% | `npm run build` |
| **型エラー** | 0 | `npm run typecheck` |
| **Lintエラー** | 0 | `npm run lint` |

### 10.2 非機能要件達成

| NFR | 要件 | 受け入れ基準 |
|-----|------|-------------|
| **REQ-DR-NFR-001** | 5秒以内応答 | E2Eテストでp95 <5秒 |
| **REQ-DR-NFR-002** | トークン効率 | 15,000トークン以内で完了 |
| **REQ-DR-NFR-003** | セキュリティ | API key漏洩0件、XSS脆弱性0件 |
| **REQ-DR-NFR-004** | キャッシング | ヒット率 >50% |
| **REQ-DR-NFR-005** | エラーハンドリング | すべてのエラーケースでカスタムError使用 |
| **REQ-DR-NFR-006** | ロギング | すべてのイテレーションでログ記録 |

---

## 11. リスクと対策

### 11.1 技術的リスク

| リスク | 影響 | 対策 |
|--------|------|------|
| **VS Code LM API変更** | 高 | Adapter Patternによる抽象化、バージョン固定 |
| **Search API Rate Limiting** | 中 | リトライ処理、複数プロバイダー対応 |
| **トークン予算超過** | 中 | TokenTracker厳格監視、早期終了ロジック |
| **LM応答品質** | 中 | プロンプトエンジニアリング、Expert Delegation活用 |

### 11.2 スケジュールリスク

| リスク | 影響 | 対策 |
|--------|------|------|
| **見積超過** | 中 | バッファ20%確保、P2タスクを後回し |
| **依存タスク遅延** | 高 | 並列化可能なタスクを優先実装 |
| **テスト不足** | 高 | TDD徹底、継続的テスト実行 |

---

## 12. 次のステップ

### 12.1 Phase 3承認後

Phase 3（タスク分解）承認後、Phase 4（実装）を以下の順序で進める：

1. **Phase 4-4**: Foundation（TSK-DR-001~013）- 22時間（3日）
2. **Phase 4-5**: Security（TSK-DR-014~016）- 5時間（1日）
3. **Phase 4-6**: Performance（TSK-DR-017~018）- 5時間（1日）
4. **Phase 4-7**: Integration（TSK-DR-021~026）- 12時間（2日）
5. **Phase 4-8**: Testing & Error Handling（TSK-DR-027~028）- 10時間（2日）

**総実装期間**: 約9日（並列化考慮）

### 12.2 承認チェックリスト

- [x] ✅ タスク分解の粒度適切（2-8時間）
- [x] ✅ 依存関係明確
- [x] ✅ 優先度付け適切
- [x] ✅ 工数見積妥当
- [x] ✅ 受け入れ基準明確
- [x] ✅ トレーサビリティ100%
- [x] ✅ リスク対策明確

### 12.3 ユーザー承認

- [x] ✅ **2026-01-16承認** - Phase 3完了、Phase 4へ進む

---

## 13. 変更履歴

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-16 | MUSUBIX AI Agent | 初版作成 - 28タスク分解、工数見積、依存関係グラフ、受け入れ基準 |
| 1.1 | 2026-01-16 | MUSUBIX AI Agent | ✅ **ユーザー承認取得・Phase 3完了** |

---

**Phase 3 完了**: ✅ タスク分解書承認済み。Phase 4（実装）へ進む。
