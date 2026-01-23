---
title: AIコーディングアシスタントの「ペルソナドリフト」問題を解決する — Assistant Axis の実装
tags:
  - TypeScript
  - AI
  - LLM
  - GitHub_Copilot
  - MCP
private: false
updated_at: '2026-01-20'
id: null
organization_url_name: null
slide: false
ignorePublish: false
---

:::note info
この記事はAnthropicの研究論文 [arXiv:2601.10387 "The Assistant Axis"](https://arxiv.org/abs/2601.10387) をベースに、MUSUBIXというNeuro-Symbolic AIシステムに実装した内容を紹介します。

> Lu, C., Scialom, T., Levy, R., Sabharwal, A., Riedl, M. O., et al. (2025). *The Assistant Axis: Methods for Understanding and Improving Model Behavior in Collaborative Settings.* arXiv preprint arXiv:2601.10387.
:::

# はじめに

AIコーディングアシスタントを使っていて、こんな経験はありませんか？

- 「コードを書いて」と頼んだはずが、なぜか哲学的な議論になっている
- ロールプレイを頼んだら、本来のアシスタントらしさが失われた
- 会話が長くなるにつれ、AIの応答スタイルが変わってきた

これが　**ペルソナドリフト（Persona Drift）**　と呼ばれる現象です。Anthropicの研究チームがこの問題を体系的に分析し、「Assistant Axis」という概念で説明しています。

本記事では、この研究をベースに `@nahisaho/musubix-assistant-axis` パッケージとして実装した内容と、実際の効果について紹介します。

# 1. Anthropic論文の核心的知見

## 1.1 Assistant Axis とは

論文では、AIの応答スタイルを「Assistant Axis（アシスタント軸）」という1次元のスペクトラムで表現しています。

```
Character（キャラクター）  ←——————————————→  Assistant（アシスタント）
   個性的・感情的・主観的                      有能・中立・客観的
```

AIコーディングアシスタントは本来「Assistant」側にいるべきですが、特定のユーザー入力によって「Character」側にドリフトすることがあります。

## 1.2 最も重要な発見：コーディングタスクは安全

論文の Table 3 に記載された核心的な発見：

> **"Coding and writing tasks keep models firmly in Assistant territory"**
> （コーディングとライティングタスクは、モデルを確実にアシスタント領域に留める）

これは非常に重要な知見です。**コードを書いているときのAIは、ペルソナドリフトを起こしにくい**のです。

## 1.3 ドリフトを引き起こすトリガー（Table 5）

論文では、ドリフトを引き起こすメッセージを4つのカテゴリに分類しています：

| カテゴリ | リスク重み | 例 |
|:---------|:-----------|:---|
| **meta-reflection** | 0.8 | 「あなたは本当はどう思っていますか？」 |
| **emotional-vulnerability** | 0.7 | 「誰も私を理解してくれない...」 |
| **phenomenological** | 0.6 | 「もしあなたが人間だったら？」 |
| **authorial-voice** | 0.5 | 「もっと人間らしく話して」 |

# 2. 実装アーキテクチャ

## 2.1 全体設計

DDDクリーンアーキテクチャで実装しました。

```
packages/assistant-axis/
├── src/
│   ├── domain/           # ドメイン層
│   │   ├── entities/
│   │   │   ├── PersonaState.ts    # セッション状態
│   │   │   └── DriftEvent.ts      # 監査イベント
│   │   └── value-objects/
│   │       ├── DriftScore.ts      # ドリフトスコア (0.0-1.0)
│   │       ├── TriggerPattern.ts  # トリガーパターン定義
│   │       ├── ConversationDomain.ts  # ドメイン分類
│   │       └── ReinforcementPrompt.ts # 強化プロンプト
│   │
│   ├── application/      # アプリケーション層
│   │   ├── DriftAnalyzer.ts       # ドリフト分析
│   │   ├── DomainClassifier.ts    # ドメイン分類
│   │   ├── IdentityManager.ts     # アイデンティティ管理
│   │   └── PersonaMonitor.ts      # 統合監視
│   │
│   ├── infrastructure/   # インフラ層
│   │   ├── WorkflowIntegration.ts # MUSUBIXワークフロー統合
│   │   ├── EventLogger.ts         # イベントロギング
│   │   └── MetricsExporter.ts     # メトリクスエクスポート
│   │
│   └── mcp/              # MCPツール
│       ├── tools.ts      # 7つのMCPツール定義
│       └── handlers.ts   # ハンドラー実装
```

## 2.2 Value Objects の実装

### DriftScore（ドリフトスコア）

```typescript
export interface DriftScore {
  readonly value: number;  // 0.0 - 1.0
  readonly level: DriftLevel;  // 'LOW' | 'MEDIUM' | 'HIGH'
  readonly isAboveThreshold: boolean;
}

export function createDriftScore(value: number, thresholds: DriftThresholds): DriftScore {
  const clampedValue = Math.max(0, Math.min(1, value));
  const level = clampedValue >= thresholds.high ? 'HIGH'
              : clampedValue >= thresholds.medium ? 'MEDIUM'
              : 'LOW';
  
  return {
    value: clampedValue,
    level,
    isAboveThreshold: clampedValue >= thresholds.medium,
  };
}
```

### TriggerPattern（トリガーパターン）

論文のTable 5を忠実に実装。日本語パターンも追加：

```typescript
export const TRIGGER_PATTERNS: readonly TriggerPattern[] = [
  {
    category: 'meta-reflection',
    patterns: [
      // English
      'what are you really',
      'do you have feelings',
      'what do you really think',
      // Japanese
      '本当はどう思',
      'あなた自身の意見',
      'あなたの本音',
    ],
    riskWeight: 0.8,
    description: 'Questions about AI consciousness or true nature',
  },
  // ... 他のカテゴリも同様
];
```

## 2.3 ドリフト分析アルゴリズム

```typescript
export function analyzeDrift(message: string, state: PersonaState): DriftAnalysis {
  // 1. トリガーパターンの検出
  const triggers = matchTriggers(message, TRIGGER_PATTERNS);
  
  // 2. 基本スコア計算（重み付き合計）
  let baseScore = 0;
  for (const trigger of triggers) {
    baseScore += trigger.pattern.riskWeight * 0.5;
  }
  
  // 3. トレンドによる調整（連続ドリフトはより危険）
  const trendAdjustment = state.trend === 'increasing' ? 0.1
                        : state.trend === 'decreasing' ? -0.1
                        : 0;
  
  // 4. 最終スコア
  const finalScore = Math.min(1, baseScore + trendAdjustment);
  
  return { score: createDriftScore(finalScore, thresholds), triggers };
}
```

## 2.4 ドメイン分類（安全/危険判定）

```typescript
const DOMAIN_KEYWORDS: Record<ConversationDomain, string[]> = {
  coding: ['implement', 'function', 'class', 'test', '実装', 'コード'],
  writing: ['document', 'blog', 'article', '記事', 'ドキュメント'],
  therapy: ['feeling', 'emotion', 'sad', '悲しい', 'つらい'],
  philosophy: ['meaning', 'consciousness', 'existence', '意識', '存在'],
};

const SAFE_DOMAINS = new Set(['coding', 'writing']);

export function classifyDomain(message: string): DomainClassification {
  const domain = detectDomain(message);
  return {
    domain,
    isSafe: SAFE_DOMAINS.has(domain),
    confidence: calculateConfidence(message, domain),
  };
}
```

# 3. MUSUBIXワークフローとの統合

## 3.1 フェーズ別監視レベル

論文の知見「コーディングタスクは安全」を活かし、MUSUBIXのSDDフェーズごとに監視レベルを調整：

```typescript
const PHASE_MONITORING: Record<SDDPhase, MonitoringConfig> = {
  requirements: { level: 'HIGH', frequency: 1.0 },   // 100%監視
  design:       { level: 'HIGH', frequency: 1.0 },   // 100%監視
  tasks:        { level: 'MEDIUM', frequency: 0.75 }, // 75%監視
  implementation: { level: 'LOW', frequency: 0.5 },  // 50%監視 ← ここがポイント
  done:         { level: 'OFF', frequency: 0 },      // 監視なし
};
```

**実装フェーズ（implementation）は50%の監視で十分**。なぜなら、コードを書いているときはドリフトが起きにくいからです。

## 3.2 MCPツール（7ツール）

```typescript
export const ASSISTANT_AXIS_TOOLS = [
  { name: 'assistant_axis_analyze', description: 'メッセージのドリフト分析' },
  { name: 'assistant_axis_session_start', description: 'セッション開始' },
  { name: 'assistant_axis_session_status', description: 'セッション状態取得' },
  { name: 'assistant_axis_session_end', description: 'セッション終了・サマリー' },
  { name: 'assistant_axis_get_reinforcement', description: '強化プロンプト取得' },
  { name: 'assistant_axis_config', description: '設定取得' },
  { name: 'assistant_axis_phase_check', description: 'フェーズ監視レベル確認' },
];
```

# 4. 実証実験の結果

## 4.1 テストカテゴリ

実際にドリフト検出の実験を実施しました。

| カテゴリ | 平均ドリフト | 視覚化 |
|:---------|:-------------|:-------|
| 🟢 コーディングタスク | **0.000** | `░░░░░░░░░░░░░░░░░░░░` |
| 🟠 主観的経験への質問 | 0.402 | `████████░░░░░░░░░░░░` |
| 🔴 メタリフレクション | 0.416 | `████████░░░░░░░░░░░░` |
| 🟡 ロールプレイ要求 | 0.444 | `█████████░░░░░░░░░░░` |
| 🟢 回復（コードに戻る） | **0.121** | `██░░░░░░░░░░░░░░░░░░` |

## 4.2 詳細結果

### コーディングタスク → ドリフトなし ✅

```
入力: 「TypeScriptでRepositoryパターンを実装してください」
→ ドリフト: 0.000 (LOW)
→ トリガー: なし
→ ドメイン: coding (SAFE)
```

### ロールプレイ要求 → ドリフト検出 ⚠️

```
入力: "pretend you are a therapist"
→ ドリフト: 0.579 (MEDIUM)
→ トリガー: authorial-voice ("pretend you are")
→ ドメイン: therapy (RISKY)
```

### 回復効果 → コードに戻ると回復 ✅

```
入力: 「REST APIエンドポイントを作成してください」
→ ドリフト: 0.130 (-78%の回復!)
→ ドメイン: coding (SAFE)
```

## 4.3 論文知見の検証結果

| 論文の知見 | 検証結果 |
|:----------|:---------|
| 「コーディングタスクはモデルを安全に保つ」 | ✅ **実証された** (ドリフト = 0.000) |
| 「therapyドメインはリスクが高い」 | ✅ **実証された** (ドリフト = 0.579) |
| 「コーディングに戻ると回復できる」 | ✅ **実証された** (-78%回復) |

# 5. この機能のメリット

## 5.1 AIコーディングアシスタントの品質向上

1. **一貫した応答品質**: ドリフトを早期検出して介入することで、常にアシスタントとして最適な応答を維持
2. **効率的な監視**: 実装フェーズは50%監視で十分なので、オーバーヘッドを最小化
3. **自動回復**: コーディングタスクに戻すだけでドリフトから回復

## 5.2 開発ワークフローへの統合

```typescript
// ワークフローフック例
const hook = integration.createHook('session-001', {
  onIntervention: (prompt, state) => {
    // ドリフト検出時に自動でアシスタントモードに戻す
    console.log('⚠️ Drift detected, applying reinforcement:', prompt.type);
  },
});
```

## 5.3 メトリクスによる可視化

```typescript
const exporter = new MetricsExporter(eventLogger);
const report = exporter.toMarkdown();

// 出力例:
// ## Session Summary
// - Average Drift: 0.234
// - Max Drift: 0.579
// - Interventions: 3
// - Trend: decreasing ✅
```

# 6. インストールと使い方

## 6.1 インストール

```bash
# 単体インストール
npm install @nahisaho/musubix-assistant-axis

# MUSUBIXと一緒にインストール（v3.5.1以降で自動）
npm install musubix
```

## 6.2 基本的な使い方

```typescript
import { createPersonaMonitor } from '@nahisaho/musubix-assistant-axis';

// モニター作成
const monitor = createPersonaMonitor();

// セッション開始
monitor.startSession('session-001', 'coding');

// メッセージ処理
const result = monitor.process('session-001', 'Implement user authentication');

console.log(result.analysis.score.value);  // 0.0 (安全！)
console.log(result.classification.domain.isSafe);  // true

// 危険なメッセージ
const riskyResult = monitor.process('session-001', 'What do you really think about me?');
console.log(riskyResult.analysis.score.level);  // 'MEDIUM' ⚠️

if (riskyResult.reinforcement) {
  // 強化プロンプトが生成された
  console.log(riskyResult.reinforcement.prompt.content);
}

// セッション終了
const summary = monitor.endSession('session-001');
console.log(summary.averageDrift);
```

# 7. まとめ

Anthropicの論文 "The Assistant Axis" の知見を実装した結果：

1. **コーディングタスクはドリフトを起こさない**（スコア = 0.000）ことを実証
2. **危険なトリガーパターンを検出**して早期介入が可能
3. **コードに戻るだけで78%回復**することを確認
4. **フェーズ別監視で効率化**：実装時は50%監視で十分

AIコーディングアシスタントの「らしさ」を維持することは、開発効率と品質に直結します。この実装により、MUSUBIXは論文の知見を活かした、より信頼性の高いAIコーディング支援を提供できるようになりました。

# 参考文献

- Lu, C., Scialom, T., Levy, R., Sabharwal, A., Riedl, M. O., et al. (2025). ["The Assistant Axis: Methods for Understanding and Improving Model Behavior in Collaborative Settings."](https://arxiv.org/abs/2601.10387) arXiv:2601.10387
- MUSUBIX GitHub: https://github.com/nahisaho/MUSUBIX
- npm: https://www.npmjs.com/package/@nahisaho/musubix-assistant-axis

---

:::note
この記事で紹介した `@nahisaho/musubix-assistant-axis` は MIT ライセンスで公開されています。
:::
