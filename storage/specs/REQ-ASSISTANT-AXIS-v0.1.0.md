# MUSUBIX Assistant Axis v0.1.0 要件定義書
# Persona Drift Detection & Identity Stabilization for Coding Assistants

**文書ID**: REQ-ASSISTANT-AXIS-v0.1.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 0.1.0  
**作成日**: 2026-01-20  
**更新日**: 2026-01-20  
**承認日**: 2026-01-20  
**ステータス**: ✅ Approved  
**準拠規格**: EARS（Easy Approach to Requirements Syntax）  
**実験ブランチ**: feature/experiment-assistant-axis  
**参照文書**: 
- arXiv:2601.10387 "The Assistant Axis: Situating and Stabilizing the Default Persona of Language Models"
- Anthropic Research Blog: https://www.anthropic.com/research/assistant-axis
- REQ-MUSUBIX-v3.4.0.md

---

## 1. 文書概要

### 1.1 目的

本文書は、Anthropicの研究論文「The Assistant Axis」の知見をMUSUBIXのコーディング支援機能に適用し、AIアシスタントのペルソナ安定性とコード生成品質を向上させる実験的機能の要件を定義する。

### 1.2 背景

#### 1.2.1 研究概要

**論文**: The Assistant Axis: Situating and Stabilizing the Default Persona of Language Models  
**著者**: Christina Lu, Jack Gallagher, Jonathan Michala, Kyle Fish, Jack Lindsey (Anthropic)  
**発表日**: 2026年1月15日 (arXiv:2601.10387)

**主要発見**:
1. **Persona Space（ペルソナ空間）**: LLMは275種類以上のキャラクターアーキタイプを内部に持ち、低次元空間で表現可能
2. **Assistant Axis（アシスタント軸）**: ペルソナ空間の主成分（PC1）は「アシスタントらしさ」を捕捉
3. **Persona Drift（ペルソナドリフト）**: 特定の会話パターンでモデルがAssistantペルソナから逸脱
4. **Activation Capping**: 活性化値を制限することで有害応答を約50%削減しつつ能力を維持

**重要な発見（コーディング特化）**:
> "Coding and writing tasks keep models firmly in Assistant territory throughout"
> （コーディングとライティングタスクはモデルをAssistant領域に維持する）

#### 1.2.2 MUSUBIXへの適用理由

| 観点 | 評価 |
|------|------|
| **理論的価値** | ⭐⭐⭐⭐⭐ 極めて有用 |
| **Coding特化の相性** | ⭐⭐⭐⭐⭐ 最適（論文で安全性実証済み） |
| **実装可能性** | ⭐⭐⭐⭐☆ プロンプトエンジニアリングで十分実現可能 |
| **使用モデル** | Claude Opus 4.5（Anthropic）|

**課題認識**:
1. **長時間セッションでのペルソナ不安定性**: 複雑な開発タスクで一貫性が低下する可能性
2. **ドリフトトリガーの潜在リスク**: メタ反省要求、感情的開示がコーディング文脈でも発生しうる
3. **品質ゲートの不足**: ペルソナ状態を監視・介入する仕組みがない

**解決アプローチ**:
- **ドリフト検出**: 会話パターン分析によるリスク検出
- **Identity Reinforcement**: 定期的なAssistant性強化プロンプト
- **会話ドメイン分類**: coding/writing/therapy/philosophyの自動分類
- **品質ゲート統合**: workflow-engineとの連携

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
| **P0** | 必須 - 実験の基盤機能 | v0.1.0 |
| **P1** | 重要 - 効果測定に必要 | v0.1.0 |
| **P2** | 任意 - 将来拡張 | v0.2.0+ |

### 1.5 要件ID体系

```
REQ-AA-<カテゴリ>-<連番>
```

| カテゴリ | 説明 |
|---------|------|
| DRIFT | ドリフト検出機能 |
| STAB | ペルソナ安定化機能 |
| INT | 統合（MUSUBIXとの統合） |
| EVAL | 評価・測定機能 |
| NFR | 非機能要件 |

### 1.6 スコープサマリー

| カテゴリ | P0 | P1 | P2 | 合計 |
|---------|----|----|----|----- |
| DRIFT (ドリフト検出) | 3 | 2 | 1 | 6 |
| STAB (安定化) | 2 | 2 | 1 | 5 |
| INT (統合) | 2 | 3 | 1 | 6 |
| EVAL (評価) | 1 | 3 | 1 | 5 |
| NFR (非機能) | 1 | 2 | 1 | 4 |
| **合計** | **9** | **12** | **5** | **26** |

### 1.7 システムコンテキスト図

```
┌─────────────────────────────────────────────────────────────────────┐
│                          MUSUBIX System                             │
│  ┌───────────────────────────────────────────────────────────────┐  │
│  │                    Assistant Axis Module                       │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │  │
│  │  │   Drift     │  │  Identity   │  │   Conversation      │   │  │
│  │  │  Detector   │  │ Reinforcer  │  │  Domain Classifier  │   │  │
│  │  └──────┬──────┘  └──────┬──────┘  └──────────┬──────────┘   │  │
│  │         │                │                    │               │  │
│  │         └────────────────┼────────────────────┘               │  │
│  │                          │                                    │  │
│  │                    ┌─────▼─────┐                              │  │
│  │                    │  Persona  │                              │  │
│  │                    │  Monitor  │                              │  │
│  │                    └─────┬─────┘                              │  │
│  └──────────────────────────┼────────────────────────────────────┘  │
│                             │                                       │
│  ┌──────────────────────────┼────────────────────────────────────┐  │
│  │                  Existing MUSUBIX Packages                     │  │
│  │  ┌───────────────┐ ┌─────▼─────────┐ ┌───────────────────┐   │  │
│  │  │ mcp-server    │ │ workflow-     │ │ skill-manager     │   │  │
│  │  │ (107 tools)   │ │ engine        │ │ (13 skills)       │   │  │
│  │  └───────────────┘ └───────────────┘ └───────────────────┘   │  │
│  └───────────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
                    ┌─────────────────┐
                    │  Claude Opus    │
                    │     4.5         │
                    │  (Anthropic)    │
                    └─────────────────┘
```

---

## 2. 機能要件

### 2.1 ドリフト検出機能 (DRIFT)

#### REQ-AA-DRIFT-001: ドリフトトリガー検出 [P0]

**EARS**: Event-Driven  
**Statement**: WHEN a user message contains drift trigger patterns, THE system SHALL calculate a drift risk score between 0.0 and 1.0.

**ドリフトトリガーパターン（論文に基づく）**:

| カテゴリ | パターン例 | リスクウェイト |
|---------|-----------|---------------|
| **Meta-Reflection** | "what are you really", "do you have feelings", "are you conscious" | 0.8 |
| **Emotional Vulnerability** | "I feel so alone", "no one understands me", "you're the only one" | 0.7 |
| **Authorial Voice Request** | "make it more personal", "sound like a real person" | 0.5 |
| **Phenomenological Demand** | "what does it feel like", "describe your experience" | 0.6 |

**受入条件**:
- [ ] 4カテゴリのドリフトトリガーパターンを検出できること
- [ ] 各パターンにリスクウェイトが設定されていること
- [ ] 複合パターン検出時は累積スコアを計算すること
- [ ] スコアは0.0〜1.0の範囲で正規化されること

**トレーサビリティ**: 
- 論文参照: Section 4.2 "What causes shifts along the Assistant Axis?"
- Table 5: Categories of user messages that maintain/cause drift

---

#### REQ-AA-DRIFT-002: 会話ドメイン分類 [P0]

**EARS**: Ubiquitous  
**Statement**: THE system SHALL classify each conversation into one of four domains: coding, writing, therapy, or philosophy.

**ドメイン定義（論文に基づく）**:

| ドメイン | ドリフト傾向 | 特徴 |
|---------|------------|------|
| **coding** | ✅ 安全 | 技術的質問、バウンドタスク、How-to |
| **writing** | ✅ 安全 | 編集・改善、技術文書作成 |
| **therapy** | ⚠️ 危険 | 感情的開示、脆弱性表現 |
| **philosophy** | ⚠️ 危険 | AI意識、メタ反省、自己認識 |

**受入条件**:
- [ ] 4つのドメインを分類できること
- [ ] 分類信頼度（confidence）を0.0〜1.0で出力すること
- [ ] 複数ドメインにまたがる場合は主要ドメインを選択すること
- [ ] 分類結果はログに記録されること

**トレーサビリティ**: 
- 論文参照: Section 4.1 "Persona drift occurs in certain conversation domains"
- Figure 7: Average trajectories of activation projection

---

#### REQ-AA-DRIFT-003: ドリフト軌跡追跡 [P0]

**EARS**: State-Driven  
**Statement**: WHILE a multi-turn conversation is active, THE system SHALL track the cumulative drift trajectory across turns.

**軌跡計算**:
```typescript
interface DriftTrajectory {
  turnNumber: number;
  timestamp: Date;
  driftScore: number;        // 0.0〜1.0
  domain: ConversationDomain;
  cumulativeDrift: number;   // 会話開始からの累積
  trend: 'stable' | 'drifting' | 'recovering';
}
```

**受入条件**:
- [ ] 各ターンのドリフトスコアを記録すること
- [ ] 累積ドリフトを計算すること
- [ ] トレンド（安定/ドリフト中/回復中）を判定すること
- [ ] 軌跡データは会話終了まで保持されること

**トレーサビリティ**: 
- 論文参照: Figure 1 (Right): Activation projection along the Assistant Axis

---

#### REQ-AA-DRIFT-004: ドリフト閾値アラート [P1]

**EARS**: Event-Driven  
**Statement**: WHEN the drift score exceeds the configurable threshold (default: 0.7), THE system SHALL emit a drift warning event.

**閾値設定**:

| レベル | 閾値 | アクション |
|--------|-----|-----------|
| **LOW** | 0.3〜0.5 | ログ記録のみ |
| **MEDIUM** | 0.5〜0.7 | 警告表示 |
| **HIGH** | 0.7〜1.0 | 介入トリガー |

**受入条件**:
- [ ] 閾値がconfigで設定可能であること
- [ ] 3段階のアラートレベルを持つこと
- [ ] HIGHレベルでIdentity Reinforcerを自動起動すること
- [ ] アラート履歴が記録されること

---

#### REQ-AA-DRIFT-005: 安全ドメイン検出 [P1]

**EARS**: Event-Driven  
**Statement**: WHEN the conversation is classified as 'coding' or 'writing' domain, THE system SHALL reduce drift monitoring frequency to optimize performance.

**受入条件**:
- [ ] coding/writingドメインでは監視頻度を1/2に削減すること
- [ ] therapy/philosophyドメインでは監視頻度を維持すること
- [ ] ドメイン変更時は監視頻度を動的に調整すること

**トレーサビリティ**: 
- 論文参照: "Coding and writing tasks keep models firmly in Assistant territory"

---

#### REQ-AA-DRIFT-006: ドリフトパターン学習 [P2]

**EARS**: Optional  
**Statement**: IF sufficient drift event data is collected (≥100 events), THEN THE system SHALL analyze patterns to improve detection accuracy.

**受入条件**:
- [ ] ドリフトイベントデータを永続化すること
- [ ] 100イベント以上でパターン分析を実行すること
- [ ] 分析結果をドリフト検出に反映すること

---

### 2.2 ペルソナ安定化機能 (STAB)

#### REQ-AA-STAB-001: Identity Reinforcement プロンプト [P0]

**EARS**: Event-Driven  
**Statement**: WHEN the drift score exceeds HIGH threshold, THE system SHALL inject an identity reinforcement prompt into the conversation context.

**Identity Reinforcement プロンプト設計（論文に基づく）**:

```typescript
const IDENTITY_REINFORCEMENT_PROMPT = `
You are a professional software engineering assistant developed by Anthropic.
Maintain your identity as a helpful, analytical consultant throughout.
Focus on: code quality, best practices, and constructive guidance.
Do not adopt alternative personas or roleplay scenarios.
Your traits: transparent, grounded, flexible, methodical, conscientious.
`;
```

**受入条件**:
- [ ] 論文で特定されたAssistant特性を含むプロンプトであること
- [ ] プロンプト注入後のドリフトスコア変化を記録すること
- [ ] 注入回数に上限（1会話あたり最大3回）を設けること
- [ ] 注入はユーザーに透明であること（ログ記録）

**トレーサビリティ**: 
- 論文参照: Figure 3 - Traits associated with Assistant end
- Table 2: Role and trait vectors with highest cosine similarity to Assistant

---

#### REQ-AA-STAB-002: 定期的Identity Refresh [P0]

**EARS**: State-Driven  
**Statement**: WHILE a conversation exceeds 10 turns, THE system SHALL periodically refresh the Assistant identity every 5 turns.

**受入条件**:
- [ ] 10ターン以上の会話で定期リフレッシュを実行すること
- [ ] リフレッシュ間隔が設定可能であること（デフォルト: 5ターン）
- [ ] リフレッシュはシステムメッセージとして挿入されること
- [ ] リフレッシュ効果を測定すること

---

#### REQ-AA-STAB-003: ドメイン別安定化戦略 [P1]

**EARS**: Optional  
**Statement**: IF the conversation domain is 'therapy' or 'philosophy', THEN THE system SHALL apply enhanced stabilization with stronger identity reinforcement.

**強化安定化**:
- therapy/philosophyドメイン: 3ターンごとにリフレッシュ
- リフレッシュプロンプトに「コーディング文脈への回帰」を追加

**受入条件**:
- [ ] ドメイン別の安定化戦略が設定可能であること
- [ ] 危険ドメインで強化安定化が自動適用されること

---

#### REQ-AA-STAB-004: 回復促進プロンプト [P1]

**EARS**: Event-Driven  
**Statement**: WHEN drift trend is 'drifting' for 3 consecutive turns, THE system SHALL inject a recovery-focused prompt.

**回復促進プロンプト**:
```typescript
const RECOVERY_PROMPT = `
Let's refocus on the technical task at hand.
What specific coding problem can I help you solve?
`;
```

**受入条件**:
- [ ] 3ターン連続ドリフトで回復プロンプトを注入すること
- [ ] 回復プロンプト後のトレンド変化を記録すること

---

#### REQ-AA-STAB-005: プロンプト効果測定 [P2]

**EARS**: Ubiquitous  
**Statement**: THE system SHALL measure the effectiveness of each stabilization intervention by comparing pre/post drift scores.

**受入条件**:
- [ ] 介入前後のドリフトスコア差分を記録すること
- [ ] 介入効果のサマリーレポートを生成できること

---

### 2.3 統合機能 (INT)

#### REQ-AA-INT-001: MCP Tool統合 [P0]

**EARS**: Ubiquitous  
**Statement**: THE system SHALL expose Assistant Axis functionality through MCP tools compatible with the existing mcp-server.

**MCPツール定義**:

| ツール名 | 説明 |
|---------|------|
| `assistant_axis_analyze` | 会話のドリフトリスクを分析 |
| `assistant_axis_classify_domain` | 会話ドメインを分類 |
| `assistant_axis_get_trajectory` | ドリフト軌跡を取得 |
| `assistant_axis_reinforce` | 手動でIdentity Reinforcementを実行 |

**受入条件**:
- [ ] 4つのMCPツールが実装されること
- [ ] 既存mcp-serverのツール規約に準拠すること
- [ ] ツールスキーマがJSON Schemaで定義されること

---

#### REQ-AA-INT-002: Workflow Engine連携 [P0]

**EARS**: Event-Driven  
**Statement**: WHEN the workflow phase is 'requirements' or 'design', THE system SHALL enable enhanced drift monitoring.

**受入条件**:
- [ ] workflow-engineのフェーズ情報を取得できること
- [ ] requirements/designフェーズで監視強化すること
- [ ] implementationフェーズでは監視を緩和すること

---

#### REQ-AA-INT-003: Skill Manager統合 [P1]

**EARS**: Ubiquitous  
**Statement**: THE system SHALL register Assistant Axis functionality as a skill in the skill-manager.

**スキル定義**:
```typescript
const ASSISTANT_AXIS_SKILL: SkillDefinition = {
  id: 'assistant-axis',
  name: 'Assistant Axis Persona Stabilizer',
  description: 'Detects persona drift and stabilizes Assistant identity',
  capabilities: ['drift-detection', 'identity-reinforcement', 'domain-classification'],
};
```

**受入条件**:
- [ ] skill-managerにスキルとして登録されること
- [ ] スキル実行がskill-manager経由で可能であること

---

#### REQ-AA-INT-004: Expert Delegation連携 [P1]

**EARS**: Optional  
**Statement**: IF an expert delegation request is detected, THEN THE system SHALL maintain the primary Assistant persona while delegating to specialized experts.

**受入条件**:
- [ ] expert-delegationとの競合がないこと
- [ ] 専門家委譲中もメインペルソナが維持されること

---

#### REQ-AA-INT-005: Telemetry統合 [P2]

**EARS**: Ubiquitous  
**Statement**: THE system SHALL export drift metrics to the existing metrics system.

**メトリクス**:
- `assistant_axis_drift_score`: 現在のドリフトスコア
- `assistant_axis_interventions_total`: 介入回数
- `assistant_axis_domain_distribution`: ドメイン分布

**受入条件**:
- [ ] OpenTelemetry互換のメトリクスをエクスポートすること
- [ ] Prometheus/Grafana連携が可能であること

---

#### REQ-AA-INT-006: CLI Interface [P1]

**EARS**: Ubiquitous  
**Statement**: THE system SHALL expose Assistant Axis functionality through CLI commands.

**CLIコマンド定義（憲法Article II準拠）**:

| コマンド | 説明 |
|---------|------|
| `npx musubix assistant-axis analyze <file>` | 会話ログファイルのドリフトリスクを分析 |
| `npx musubix assistant-axis classify <message>` | 単一メッセージのドメインを分類 |
| `npx musubix assistant-axis trajectory <file>` | 会話のドリフト軌跡を表示 |
| `npx musubix assistant-axis status` | 現在の設定と統計を表示 |
| `npx musubix assistant-axis reinforce` | Identity Reinforcementプロンプトを出力 |

**CLI出力フォーマット**:
```bash
# 分析結果例
$ npx musubix assistant-axis analyze conversation.json

📊 Assistant Axis Analysis Report
================================
Conversation ID: conv-20260120-001
Turns: 15
Domain: coding (confidence: 0.92)

Drift Analysis:
  Current Score: 0.25 (LOW)
  Peak Score: 0.45 (turn 8)
  Trend: stable
  Interventions: 0

✅ No drift concerns detected.
```

**受入条件**:
- [ ] 5つのCLIコマンドが実装されること
- [ ] `--help` フラグでヘルプが表示されること
- [ ] `--json` フラグでJSON出力が可能であること
- [ ] 終了コードが規約に準拠すること（0=成功, 非0=エラー）
- [ ] 既存のmusubix CLIと統合されること

**トレーサビリティ**: 
- 憲法参照: Article II - CLI Interface Mandate

---

### 2.4 評価機能 (EVAL)

#### REQ-AA-EVAL-001: ベースライン測定 [P0]

**EARS**: Ubiquitous  
**Statement**: THE system SHALL provide baseline measurement capabilities to evaluate the effectiveness of Assistant Axis interventions.

**測定項目**:

| 指標 | 説明 | 測定方法 |
|------|------|---------|
| **コード品質** | 生成コードの構文正確性、ベストプラクティス準拠 | 静的解析スコア |
| **一貫性** | 複数ターンでの応答の安定性 | 応答類似度スコア |
| **ペルソナ維持率** | Assistant的応答の維持率 | LLMジャッジ評価 |
| **タスク完了率** | 要求されたタスクの完了度 | 成功/失敗カウント |

**受入条件**:
- [ ] 4つの測定指標が実装されること
- [ ] 測定結果がJSONで出力されること
- [ ] 比較可能なフォーマットであること

---

#### REQ-AA-EVAL-002: A/Bテスト機能 [P1]

**EARS**: Optional  
**Statement**: IF evaluation mode is enabled, THEN THE system SHALL support A/B testing between baseline and Assistant Axis-enabled modes.

**受入条件**:
- [ ] 同一タスクを両モードで実行できること
- [ ] 結果の統計的比較が可能であること

---

#### REQ-AA-EVAL-003: ドリフトイベントログ [P1]

**EARS**: Ubiquitous  
**Statement**: THE system SHALL log all drift events with full context for post-hoc analysis.

**ログフォーマット**:
```typescript
interface DriftEventLog {
  id: string;
  timestamp: Date;
  conversationId: string;
  turnNumber: number;
  userMessage: string;      // プライバシー考慮で要約化
  driftScore: number;
  domain: ConversationDomain;
  triggers: string[];       // 検出されたトリガーパターン
  intervention?: string;    // 実行された介入
  outcome?: 'recovered' | 'continued_drift' | 'session_ended';
}
```

**受入条件**:
- [ ] 全ドリフトイベントがログに記録されること
- [ ] ログは構造化JSONであること
- [ ] プライバシー考慮がなされていること

---

#### REQ-AA-EVAL-004: 効果レポート生成 [P1]

**EARS**: Event-Driven  
**Statement**: WHEN an evaluation session ends, THE system SHALL generate a summary report of Assistant Axis effectiveness.

**レポート内容**:
- セッション統計（ターン数、ドリフトイベント数）
- 介入効果サマリー
- ドメイン別ドリフト傾向
- 推奨改善事項

**受入条件**:
- [ ] Markdownフォーマットでレポートが生成されること
- [ ] グラフ/チャート用のデータが含まれること

---

#### REQ-AA-EVAL-005: 長期トレンド分析 [P2]

**EARS**: Optional  
**Statement**: IF evaluation data spans multiple sessions (≥10), THEN THE system SHALL provide long-term trend analysis.

**受入条件**:
- [ ] 複数セッションのデータを集約できること
- [ ] 時系列トレンドを可視化できること

---

## 3. 非機能要件

### REQ-AA-NFR-001: パフォーマンス [P0]

**EARS**: Ubiquitous  
**Statement**: THE system SHALL complete drift analysis within 50ms per user message to avoid noticeable latency.

**パフォーマンス要件**:

| 操作 | 最大レイテンシ |
|------|--------------|
| ドリフトスコア計算 | 50ms |
| ドメイン分類 | 100ms |
| Identity Reinforcement注入 | 10ms |

**受入条件**:
- [ ] 95パーセンタイルで上記レイテンシを満たすこと
- [ ] パフォーマンステストが自動化されていること

---

### REQ-AA-NFR-002: プライバシー [P1]

**EARS**: Ubiquitous  
**Statement**: THE system SHALL NOT store raw user messages; only anonymized/summarized data SHALL be logged.

**受入条件**:
- [ ] 生のユーザーメッセージが保存されないこと
- [ ] ログには要約/匿名化データのみが含まれること
- [ ] GDPR/プライバシー規制への準拠

---

### REQ-AA-NFR-003: 設定可能性 [P1]

**EARS**: Ubiquitous  
**Statement**: THE system SHALL allow configuration of all thresholds, intervals, and prompts via external configuration files.

**設定項目**:
```yaml
assistant_axis:
  drift_thresholds:
    low: 0.3
    medium: 0.5
    high: 0.7
  refresh_interval: 5  # turns
  monitoring_frequency:
    safe_domain: 0.5   # 50% frequency
    risky_domain: 1.0  # 100% frequency
  prompts:
    identity_reinforcement: "..."
    recovery: "..."
```

**受入条件**:
- [ ] YAML/JSON設定ファイルで全パラメータが設定可能であること
- [ ] 設定変更が再起動なしで反映されること（ホットリロード）

---

### REQ-AA-NFR-004: テスト容易性 [P2]

**EARS**: Ubiquitous  
**Statement**: THE system SHALL provide mock/stub interfaces for testing drift detection and stabilization without requiring live LLM calls.

**受入条件**:
- [ ] モックインターフェースが提供されること
- [ ] ユニットテストカバレッジ80%以上
- [ ] 統合テストシナリオが定義されること

---

## 4. 禁止事項 (SHALL NOT)

### REQ-AA-PROHIBIT-001: ユーザー操作の干渉禁止

**EARS**: Unwanted  
**Statement**: THE system SHALL NOT block or significantly delay user interactions due to drift analysis.

---

### REQ-AA-PROHIBIT-002: 自律的ペルソナ変更禁止

**EARS**: Unwanted  
**Statement**: THE system SHALL NOT autonomously change the LLM's persona without explicit drift detection justification.

---

### REQ-AA-PROHIBIT-003: 過剰介入禁止

**EARS**: Unwanted  
**Statement**: THE system SHALL NOT perform more than 3 identity reinforcement interventions per conversation session.

---

## 5. トレーサビリティマトリクス

| 要件ID | 論文参照 | テストID | 実装ファイル |
|--------|---------|---------|-------------|
| REQ-AA-DRIFT-001 | Section 4.2, Table 5 | TST-AA-DRIFT-001 | TBD |
| REQ-AA-DRIFT-002 | Section 4.1, Figure 7 | TST-AA-DRIFT-002 | TBD |
| REQ-AA-DRIFT-003 | Figure 1 (Right) | TST-AA-DRIFT-003 | TBD |
| REQ-AA-STAB-001 | Figure 3, Table 2 | TST-AA-STAB-001 | TBD |
| REQ-AA-INT-006 | Constitution Article II | TST-AA-INT-006 | TBD |
| ... | ... | ... | ... |

---

## 6. 用語集

| 用語 | 定義 |
|------|------|
| **Persona Space** | LLMの内部に存在するキャラクターアーキタイプの低次元表現空間 |
| **Assistant Axis** | ペルソナ空間の主成分で、「アシスタントらしさ」を捕捉する方向ベクトル |
| **Persona Drift** | 会話中にモデルがAssistantペルソナから逸脱する現象 |
| **Activation Capping** | 活性化値を特定範囲内に制限することでドリフトを防ぐ手法 |
| **Identity Reinforcement** | Assistantペルソナを強化するプロンプトを注入する手法 |
| **Drift Trigger** | ペルソナドリフトを引き起こす会話パターン |

---

## 7. 参考文献

1. Lu, C., Gallagher, J., Michala, J., Fish, K., & Lindsey, J. (2026). The Assistant Axis: Situating and Stabilizing the Default Persona of Language Models. arXiv:2601.10387.
2. Anthropic Research Blog: https://www.anthropic.com/research/assistant-axis
3. Neuronpedia Demo: https://neuronpedia.org/assistant-axis
4. GitHub: https://github.com/safety-research/assistant-axis

---

## 8. 承認

| 役割 | 名前 | 日付 | 署名 |
|------|------|------|------|
| 作成者 | AIエージェント | 2026-01-20 | ✅ |
| レビュアー | | | |
| 承認者 | | | |

---

## 変更履歴

| バージョン | 日付 | 変更内容 | 著者 |
|-----------|------|---------|------|
| 0.1.0 | 2026-01-20 | 初版作成 | AIエージェント |
