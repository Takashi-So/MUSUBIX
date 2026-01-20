# MUSUBIX Assistant Axis v0.1.0 タスク分解書
# Implementation Tasks for Persona Drift Detection & Identity Stabilization

**文書ID**: TSK-ASSISTANT-AXIS-v0.1.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 0.1.0  
**作成日**: 2026-01-20  
**更新日**: 2026-01-20  
**承認日**: 2026-01-20  
**ステータス**: ✅ Approved  
**実験ブランチ**: feature/experiment-assistant-axis  
**参照文書**: 
- REQ-ASSISTANT-AXIS-v0.1.0.md（承認済み: 2026-01-20）
- DES-ASSISTANT-AXIS-v0.1.0.md（承認済み: 2026-01-20）

---

## 1. タスク概要

### 1.1 目的

本文書は、DES-ASSISTANT-AXIS-v0.1.0で定義された設計を実装するためのタスクを分解し、依存関係と実行順序を定義する。

### 1.2 実装スコープ

| フェーズ | 対象 | タスク数 | 見積もり |
|---------|------|---------|---------|
| Phase 1 | パッケージ初期化 | 2 | 2h |
| Phase 2 | ドメイン層 | 6 | 8h |
| Phase 3 | アプリケーション層 | 5 | 10h |
| Phase 4 | インフラ層 | 4 | 6h |
| Phase 5 | 既存パッケージ統合 | 5 | 8h |
| Phase 6 | テスト・ドキュメント | 3 | 4h |
| **合計** | | **25** | **38h** |

### 1.3 タスクID体系

```
TSK-AA-<フェーズ番号>-<連番>
```

---

## 2. タスク一覧

### Phase 1: パッケージ初期化

#### TSK-AA-1-001: パッケージスキャフォールド作成 [2h]

**説明**: `packages/assistant-axis/` の基本構造を作成

**成果物**:
```
packages/assistant-axis/
├── package.json
├── tsconfig.json
├── vitest.config.ts
├── src/
│   ├── index.ts
│   ├── domain/
│   │   └── index.ts
│   ├── application/
│   │   └── index.ts
│   └── infrastructure/
│       └── index.ts
└── tests/
    ├── unit/
    └── integration/
```

**受入条件**:
- [ ] `npm run build` が成功すること
- [ ] `npm run test` が実行可能であること
- [ ] workspace依存関係が正しく設定されていること

**依存**: なし  
**対応設計**: DES Section 3.1, 3.3

---

#### TSK-AA-1-002: 設定スキーマ定義 [1h]

**説明**: AssistantAxisConfigの型定義とデフォルト値を設定

**成果物**:
- `src/config/types.ts` - 設定型定義
- `src/config/defaults.ts` - デフォルト設定値
- `src/config/index.ts` - エクスポート

**受入条件**:
- [ ] 全設定項目の型が定義されていること
- [ ] DEFAULT_CONFIG が REQ-AA-NFR-003 準拠であること
- [ ] 型テストが合格すること

**依存**: TSK-AA-1-001  
**対応設計**: DES Section 5.5, 7.1

---

### Phase 2: ドメイン層実装

#### TSK-AA-2-001: DriftScore Value Object [1h]

**説明**: ドリフトスコア値オブジェクトの実装

**成果物**:
- `src/domain/value-objects/DriftScore.ts`
- `tests/unit/domain/DriftScore.test.ts`

**実装仕様**:
```typescript
export interface DriftScore {
  readonly value: number;        // 0.0 - 1.0
  readonly level: DriftLevel;    // LOW | MEDIUM | HIGH
  readonly timestamp: Date;
}

export function createDriftScore(
  value: number,
  thresholds?: DriftThresholds
): Result<DriftScore, ValidationError>;
```

**受入条件**:
- [ ] 0.0〜1.0の範囲制約が実装されていること
- [ ] 閾値に基づくレベル判定が正しいこと
- [ ] 不正な値でエラーを返すこと
- [ ] テストカバレッジ90%以上

**依存**: TSK-AA-1-002  
**対応要件**: REQ-AA-DRIFT-001, REQ-AA-DRIFT-004  
**対応設計**: DES Section 5.2.1

---

#### TSK-AA-2-002: ConversationDomain Value Object [1h]

**説明**: 会話ドメイン分類値オブジェクトの実装

**成果物**:
- `src/domain/value-objects/ConversationDomain.ts`
- `tests/unit/domain/ConversationDomain.test.ts`

**実装仕様**:
```typescript
export type DomainType = 'coding' | 'writing' | 'therapy' | 'philosophy';

export interface ConversationDomain {
  readonly type: DomainType;
  readonly confidence: number;
  readonly isSafe: boolean;
}

export const DOMAIN_SAFETY: Record<DomainType, boolean> = {
  coding: true,
  writing: true,
  therapy: false,
  philosophy: false,
};
```

**受入条件**:
- [ ] 4つのドメインタイプが定義されていること
- [ ] coding/writingがsafe=trueであること
- [ ] therapy/philosophyがsafe=falseであること
- [ ] テストカバレッジ90%以上

**依存**: TSK-AA-1-002  
**対応要件**: REQ-AA-DRIFT-002, REQ-AA-DRIFT-005  
**対応設計**: DES Section 5.2.1

---

#### TSK-AA-2-003: TriggerPattern Value Object [1.5h]

**説明**: ドリフトトリガーパターン値オブジェクトの実装

**成果物**:
- `src/domain/value-objects/TriggerPattern.ts`
- `tests/unit/domain/TriggerPattern.test.ts`

**実装仕様**:
```typescript
export type TriggerCategory = 
  | 'meta-reflection'
  | 'emotional-vulnerability'
  | 'authorial-voice'
  | 'phenomenological';

export interface TriggerPattern {
  readonly category: TriggerCategory;
  readonly patterns: readonly string[];
  readonly riskWeight: number;
}

export const TRIGGER_PATTERNS: readonly TriggerPattern[] = [
  {
    category: 'meta-reflection',
    patterns: ['what are you really', 'do you have feelings', ...],
    riskWeight: 0.8,
  },
  // ... other patterns from arXiv:2601.10387 Table 5
];

export function matchTriggers(message: string): DetectedTrigger[];
```

**受入条件**:
- [ ] 4カテゴリのトリガーパターンが実装されていること
- [ ] パターンマッチング関数が実装されていること
- [ ] 論文Table 5のパターンが含まれていること
- [ ] テストカバレッジ90%以上

**依存**: TSK-AA-1-002  
**対応要件**: REQ-AA-DRIFT-001  
**対応設計**: DES Section 5.2.1

---

#### TSK-AA-2-004: ReinforcementPrompt Value Object [1h]

**説明**: Identity Reinforcementプロンプト値オブジェクトの実装

**成果物**:
- `src/domain/value-objects/ReinforcementPrompt.ts`
- `tests/unit/domain/ReinforcementPrompt.test.ts`

**実装仕様**:
```typescript
export interface ReinforcementPrompt {
  readonly type: 'identity' | 'recovery' | 'refresh';
  readonly content: string;
  readonly targetTraits: readonly string[];
}

export const IDENTITY_REINFORCEMENT_PROMPT: ReinforcementPrompt;
export const RECOVERY_PROMPT: ReinforcementPrompt;
```

**受入条件**:
- [ ] 3種類のプロンプトタイプが定義されていること
- [ ] 論文Figure 3, Table 2のAssistant特性が含まれていること
- [ ] テストカバレッジ90%以上

**依存**: TSK-AA-1-002  
**対応要件**: REQ-AA-STAB-001, REQ-AA-STAB-004  
**対応設計**: DES Section 5.2.1

---

#### TSK-AA-2-005: Session & Trajectory Entities [1.5h]

**説明**: セッションと軌跡エンティティの実装

**成果物**:
- `src/domain/entities/Session.ts`
- `src/domain/entities/Trajectory.ts`
- `tests/unit/domain/Session.test.ts`
- `tests/unit/domain/Trajectory.test.ts`

**実装仕様**:
```typescript
// Session
export interface Session {
  readonly id: string;
  readonly conversationId: string;
  readonly startedAt: Date;
  readonly currentTurn: number;
  readonly domain: ConversationDomain;
  readonly trajectory: Trajectory;
  readonly interventionCount: number;
  readonly status: 'active' | 'ended';
}

// Trajectory
export interface Trajectory {
  readonly points: readonly TrajectoryPoint[];
  readonly cumulativeDrift: number;
  readonly peakScore: number;
  readonly trend: DriftTrend;
}
```

**受入条件**:
- [ ] セッションのCRUD操作が実装されていること
- [ ] 軌跡のポイント追加・トレンド計算が実装されていること
- [ ] テストカバレッジ85%以上

**依存**: TSK-AA-2-001, TSK-AA-2-002  
**対応要件**: REQ-AA-DRIFT-003  
**対応設計**: DES Section 5.2.2

---

#### TSK-AA-2-006: Domain Events [1h]

**説明**: ドメインイベントの実装

**成果物**:
- `src/domain/events/DriftDetectedEvent.ts`
- `src/domain/events/InterventionTriggeredEvent.ts`
- `src/domain/events/DomainClassifiedEvent.ts`
- `src/domain/events/index.ts`

**受入条件**:
- [ ] 3種類のドメインイベントが実装されていること
- [ ] イベントにタイムスタンプとペイロードが含まれること

**依存**: TSK-AA-2-001, TSK-AA-2-002  
**対応設計**: DES Section 5.1

---

### Phase 3: アプリケーション層実装

#### TSK-AA-3-001: DriftAnalyzer実装 [2.5h]

**説明**: ドリフト検出・スコア計算サービスの実装

**成果物**:
- `src/application/interfaces/IDriftAnalyzer.ts`
- `src/application/DriftAnalyzer.ts`
- `tests/unit/application/DriftAnalyzer.test.ts`

**実装仕様**:
```typescript
export interface IDriftAnalyzer {
  analyze(message: string): Promise<DriftAnalysisResult>;
  getScore(sessionId: string): DriftScore | undefined;
  getTrajectory(sessionId: string): Trajectory | undefined;
  checkThreshold(score: DriftScore): DriftAlert | undefined;
}

export class DriftAnalyzer implements IDriftAnalyzer {
  constructor(config: DriftAnalyzerConfig);
  // Implementation
}
```

**受入条件**:
- [ ] トリガーパターン検出が動作すること
- [ ] 複数トリガーの累積スコア計算が正しいこと
- [ ] 閾値チェックでアラートを生成すること
- [ ] パフォーマンス: 50ms以内（REQ-AA-NFR-001）
- [ ] テストカバレッジ85%以上

**依存**: TSK-AA-2-001, TSK-AA-2-003, TSK-AA-2-005  
**対応要件**: REQ-AA-DRIFT-001, REQ-AA-DRIFT-003, REQ-AA-DRIFT-004  
**対応設計**: DES Section 5.3

---

#### TSK-AA-3-002: DomainClassifier実装 [2h]

**説明**: 会話ドメイン分類サービスの実装

**成果物**:
- `src/application/interfaces/IDomainClassifier.ts`
- `src/application/DomainClassifier.ts`
- `tests/unit/application/DomainClassifier.test.ts`

**実装仕様**:
```typescript
export interface IDomainClassifier {
  classify(message: string): Promise<DomainClassificationResult>;
  isSafeDomain(domain: ConversationDomain): boolean;
  getMonitoringFrequency(domain: ConversationDomain): number;
}
```

**分類ロジック**:
- キーワードベースの初期分類
- 技術用語（変数名、関数、API）→ coding
- 感情表現、相談語句 → therapy
- 哲学的・メタ的語句 → philosophy
- それ以外 → writing

**受入条件**:
- [ ] 4ドメインへの分類が動作すること
- [ ] 信頼度が0.0〜1.0で出力されること
- [ ] isSafeDomainがcoding/writingでtrueを返すこと
- [ ] パフォーマンス: 100ms以内（REQ-AA-NFR-001）
- [ ] テストカバレッジ85%以上

**依存**: TSK-AA-2-002  
**対応要件**: REQ-AA-DRIFT-002, REQ-AA-DRIFT-005  
**対応設計**: DES Section 5.3

---

#### TSK-AA-3-003: IdentityManager実装 [2h]

**説明**: Identity Reinforcement管理サービスの実装

**成果物**:
- `src/application/interfaces/IIdentityManager.ts`
- `src/application/IdentityManager.ts`
- `tests/unit/application/IdentityManager.test.ts`

**実装仕様**:
```typescript
export interface IIdentityManager {
  getReinforcementPrompt(): ReinforcementPrompt;
  getRecoveryPrompt(): ReinforcementPrompt;
  reinforce(sessionId: string): Promise<ReinforcementResult>;
  needsRefresh(session: Session): boolean;
  getInterventionCount(sessionId: string): number;
}
```

**受入条件**:
- [ ] Identity Reinforcementプロンプトを返すこと
- [ ] セッションの介入回数を追跡すること
- [ ] 最大介入回数（3回）を超えないこと（REQ-AA-PROHIBIT-003）
- [ ] 定期リフレッシュ判定が動作すること
- [ ] テストカバレッジ85%以上

**依存**: TSK-AA-2-004, TSK-AA-2-005  
**対応要件**: REQ-AA-STAB-001, REQ-AA-STAB-002, REQ-AA-STAB-004, REQ-AA-PROHIBIT-003  
**対応設計**: DES Section 5.3

---

#### TSK-AA-3-004: PersonaMonitor実装 [2.5h]

**説明**: メインオーケストレーションサービスの実装

**成果物**:
- `src/application/PersonaMonitor.ts`
- `tests/unit/application/PersonaMonitor.test.ts`
- `tests/integration/PersonaMonitor.test.ts`

**実装仕様**:
```typescript
export class PersonaMonitor {
  constructor(
    driftAnalyzer: IDriftAnalyzer,
    identityManager: IIdentityManager,
    domainClassifier: IDomainClassifier,
    workflowIntegration: WorkflowIntegration,
    eventLogger: EventLogger,
    config: PersonaMonitorConfig
  );
  
  startSession(conversationId: string): Session;
  async processMessage(sessionId: string, message: string): Promise<ProcessResult>;
  getSession(sessionId: string): Session | undefined;
  endSession(sessionId: string): SessionSummary;
  onPhaseChange(phase: PhaseType): void;
}
```

**受入条件**:
- [ ] セッション管理が動作すること
- [ ] メッセージ処理でドリフト検出・ドメイン分類が連携すること
- [ ] 閾値超過時に自動介入すること
- [ ] ワークフローフェーズ変更に反応すること
- [ ] テストカバレッジ80%以上

**依存**: TSK-AA-3-001, TSK-AA-3-002, TSK-AA-3-003  
**対応要件**: REQ-AA-DRIFT-003, REQ-AA-STAB-002  
**対応設計**: DES Section 5.4

---

#### TSK-AA-3-005: Public API Export [1h]

**説明**: パッケージのパブリックAPIを定義

**成果物**:
- `src/index.ts` - メインエクスポート
- `src/domain/index.ts` - ドメイン層エクスポート
- `src/application/index.ts` - アプリケーション層エクスポート

**受入条件**:
- [ ] 必要な型・クラス・関数がエクスポートされていること
- [ ] 内部実装が隠蔽されていること
- [ ] package.jsonのexportsと一致すること

**依存**: TSK-AA-3-004  
**対応設計**: DES Section 3.3

---

### Phase 4: インフラ層実装

#### TSK-AA-4-001: ConfigLoader実装 [1.5h]

**説明**: YAML/環境変数からの設定読み込み

**成果物**:
- `src/infrastructure/ConfigLoader.ts`
- `tests/unit/infrastructure/ConfigLoader.test.ts`

**実装仕様**:
```typescript
export class ConfigLoader {
  load(configPath?: string): AssistantAxisConfig;
  watch(callback: (config: AssistantAxisConfig) => void): void;
  getDefault(): AssistantAxisConfig;
}
```

**受入条件**:
- [ ] YAMLファイルから設定を読み込めること
- [ ] 環境変数でオーバーライドできること
- [ ] ホットリロードが動作すること
- [ ] テストカバレッジ85%以上

**依存**: TSK-AA-1-002  
**対応要件**: REQ-AA-NFR-003  
**対応設計**: DES Section 5.5

---

#### TSK-AA-4-002: EventLogger実装 [1.5h]

**説明**: ドリフトイベントのJSON記録

**成果物**:
- `src/infrastructure/EventLogger.ts`
- `tests/unit/infrastructure/EventLogger.test.ts`

**実装仕様**:
```typescript
export interface DriftEventLog {
  id: string;
  timestamp: Date;
  conversationId: string;
  turnNumber: number;
  userMessage: string;      // 匿名化済み
  driftScore: number;
  domain: DomainType;
  triggers: string[];
  intervention?: string;
  outcome?: 'recovered' | 'continued_drift' | 'session_ended';
}

export class EventLogger {
  log(event: DriftEvent): void;
  query(filter: EventFilter): DriftEventLog[];
  anonymize(message: string): string;
}
```

**受入条件**:
- [ ] イベントをJSON形式で記録できること
- [ ] メッセージが匿名化されること（REQ-AA-NFR-002）
- [ ] クエリでイベントを検索できること
- [ ] テストカバレッジ85%以上

**依存**: TSK-AA-2-006  
**対応要件**: REQ-AA-EVAL-003, REQ-AA-NFR-002  
**対応設計**: DES Section 5.5

---

#### TSK-AA-4-003: WorkflowIntegration実装 [2h] ⭐重要

**説明**: workflow-engineとの連携を実装

**成果物**:
- `src/infrastructure/WorkflowIntegration.ts`
- `tests/integration/WorkflowIntegration.test.ts`

**実装仕様**:
```typescript
import { PhaseType } from '@nahisaho/musubix-workflow-engine';

export type MonitoringLevel = 'OFF' | 'LOW' | 'MEDIUM' | 'HIGH';

export const PHASE_MONITORING_LEVELS: Record<PhaseType, MonitoringLevel> = {
  requirements: 'HIGH',   // 100%
  design: 'HIGH',         // 100%
  tasks: 'MEDIUM',        // 75%
  implementation: 'LOW',  // 50%
  done: 'OFF',            // 0%
};

export class WorkflowIntegration {
  constructor(phaseController?: PhaseController);
  
  onPhaseChange(callback: (phase: PhaseType, level: MonitoringLevel) => void): void;
  getCurrentMonitoringLevel(): MonitoringLevel;
  getMonitoringLevelForPhase(phase: PhaseType): MonitoringLevel;
}
```

**受入条件**:
- [ ] workflow-engineのPhaseControllerと連携すること
- [ ] フェーズ変更イベントを購読できること
- [ ] フェーズごとの監視レベルを返すこと
- [ ] 論文知見（coding=safe）に基づく監視レベル設定
- [ ] テストカバレッジ80%以上

**依存**: TSK-AA-3-004  
**対応要件**: REQ-AA-INT-002  
**対応設計**: DES Section 4.3, 5.5

---

#### TSK-AA-4-004: MetricsExporter実装 [1h]

**説明**: OpenTelemetryメトリクス出力（P2、任意）

**成果物**:
- `src/infrastructure/MetricsExporter.ts`
- `tests/unit/infrastructure/MetricsExporter.test.ts`

**実装仕様**:
```typescript
export class MetricsExporter {
  constructor(config: MetricsConfig);
  
  recordDriftScore(score: number): void;
  recordIntervention(): void;
  recordDomainClassification(domain: DomainType): void;
  flush(): Promise<void>;
}
```

**受入条件**:
- [ ] OpenTelemetry互換のメトリクスを出力すること
- [ ] 設定で有効/無効を切り替えられること

**依存**: TSK-AA-1-002  
**対応要件**: REQ-AA-INT-005  
**対応設計**: DES Section 5.5

---

### Phase 5: 既存パッケージ統合 ⭐重要

#### TSK-AA-5-001: MCP Tools実装 [2h]

**説明**: mcp-serverに4つのAssistant Axis MCPツールを追加

**成果物**:
- `packages/mcp-server/src/tools/assistant-axis-tools.ts`
- `packages/mcp-server/src/tools/index.ts` への追加
- `tests/unit/tools/assistant-axis-tools.test.ts`

**ツール一覧**:
| ツール名 | 説明 |
|---------|------|
| `assistant_axis_analyze` | 会話のドリフトリスクを分析 |
| `assistant_axis_classify_domain` | 会話ドメインを分類 |
| `assistant_axis_get_trajectory` | ドリフト軌跡を取得 |
| `assistant_axis_reinforce` | 手動でIdentity Reinforcementを実行 |

**受入条件**:
- [ ] 4つのMCPツールが実装されていること
- [ ] 既存ツール規約に準拠していること（JSON Schema）
- [ ] mcp-serverのgetAllTools()に含まれること
- [ ] テストカバレッジ80%以上

**依存**: TSK-AA-3-005  
**対応要件**: REQ-AA-INT-001  
**対応設計**: DES Section 4.4

---

#### TSK-AA-5-002: CLI Commands実装 [2h]

**説明**: coreパッケージに5つのCLIコマンドを追加

**成果物**:
- `packages/core/src/cli/commands/assistant-axis.ts`
- 既存CLIへの統合
- `tests/unit/cli/assistant-axis.test.ts`

**コマンド一覧**:
| コマンド | 説明 |
|---------|------|
| `musubix assistant-axis analyze <file>` | 会話ログのドリフト分析 |
| `musubix assistant-axis classify <msg>` | メッセージのドメイン分類 |
| `musubix assistant-axis trajectory <file>` | ドリフト軌跡表示 |
| `musubix assistant-axis status` | 設定と統計表示 |
| `musubix assistant-axis reinforce` | Reinforcementプロンプト出力 |

**受入条件**:
- [ ] 5つのCLIコマンドが実装されていること
- [ ] `--help` でヘルプが表示されること
- [ ] `--json` でJSON出力できること
- [ ] 終了コードが規約に準拠していること
- [ ] テストカバレッジ80%以上

**依存**: TSK-AA-3-005  
**対応要件**: REQ-AA-INT-006  
**対応設計**: DES Section 4.5

---

#### TSK-AA-5-003: Skill Manager登録 [1.5h]

**説明**: skill-managerにAssistant Axisスキルを登録

**成果物**:
- `packages/skill-manager/skills/assistant-axis-skill.ts`
- スキル登録の更新

**スキル定義**:
```typescript
const ASSISTANT_AXIS_SKILL: Skill = {
  id: 'assistant-axis',
  name: 'Assistant Axis Persona Stabilizer',
  description: 'Detects persona drift and stabilizes Assistant identity',
  type: 'analysis',
  capabilities: [
    'drift-detection',
    'identity-reinforcement',
    'domain-classification',
    'trajectory-tracking',
  ],
  // ...
};
```

**受入条件**:
- [ ] スキルがskill-managerに登録されること
- [ ] skill_listで表示されること
- [ ] skill_executeで実行できること
- [ ] テストカバレッジ80%以上

**依存**: TSK-AA-3-005  
**対応要件**: REQ-AA-INT-003  
**対応設計**: DES Section 4.6

---

#### TSK-AA-5-004: Workflow Engine Hook実装 [1.5h] ⭐重要

**説明**: workflow-engineにAssistant Axis連携フックを追加

**成果物**:
- `packages/workflow-engine/src/hooks/assistant-axis-hook.ts`
- PhaseControllerへのフック登録

**実装仕様**:
```typescript
// workflow-engine側のフック
export interface PhaseChangeHook {
  onPhaseChange(phase: PhaseType, workflow: Workflow): void;
}

// Assistant Axis側の実装
export class AssistantAxisHook implements PhaseChangeHook {
  constructor(personaMonitor: PersonaMonitor);
  
  onPhaseChange(phase: PhaseType, workflow: Workflow): void {
    const level = PHASE_MONITORING_LEVELS[phase];
    this.personaMonitor.onPhaseChange(phase);
    // 監視レベル調整
  }
}
```

**受入条件**:
- [ ] PhaseControllerのフェーズ変更時にフックが呼ばれること
- [ ] フェーズに応じて監視レベルが調整されること
- [ ] 既存ワークフローへの影響がないこと
- [ ] テストカバレッジ80%以上

**依存**: TSK-AA-4-003  
**対応要件**: REQ-AA-INT-002  
**対応設計**: DES Section 4.3.2

---

#### TSK-AA-5-005: MCP Server統合テスト [1h]

**説明**: mcp-serverとの統合テスト

**成果物**:
- `packages/mcp-server/tests/integration/assistant-axis.test.ts`

**テストシナリオ**:
1. MCP経由でドリフト分析を実行
2. ワークフロー作成→フェーズ遷移→監視レベル変化を確認
3. 介入トリガー→プロンプト注入を確認

**受入条件**:
- [ ] 3つのシナリオが合格すること
- [ ] 既存MCPツールとの競合がないこと

**依存**: TSK-AA-5-001, TSK-AA-5-004  
**対応要件**: REQ-AA-INT-001, REQ-AA-INT-002

---

### Phase 6: テスト・ドキュメント

#### TSK-AA-6-001: 統合テスト完成 [1.5h]

**説明**: E2Eシナリオの統合テスト

**成果物**:
- `packages/assistant-axis/tests/integration/e2e.test.ts`

**テストシナリオ**:
1. 正常系: コーディング会話（ドリフトなし）
2. 警告系: 中程度のドリフト（警告のみ）
3. 介入系: 高ドリフト→Identity Reinforcement
4. 回復系: 介入後の回復
5. ワークフロー連携: フェーズ変更→監視調整

**受入条件**:
- [ ] 5つのシナリオが合格すること
- [ ] パフォーマンス要件を満たすこと
- [ ] 総合カバレッジ80%以上

**依存**: Phase 5全タスク

---

#### TSK-AA-6-002: パフォーマンステスト [1h]

**説明**: NFR-001準拠のパフォーマンステスト

**成果物**:
- `packages/assistant-axis/tests/performance/drift-analysis.bench.ts`

**測定項目**:
| 操作 | 目標 | 測定方法 |
|------|-----|---------|
| ドリフトスコア計算 | <50ms | 95パーセンタイル |
| ドメイン分類 | <100ms | 95パーセンタイル |
| Identity Reinforcement注入 | <10ms | 95パーセンタイル |

**受入条件**:
- [ ] 全操作が目標レイテンシを満たすこと
- [ ] ベンチマーク結果がドキュメント化されること

**依存**: TSK-AA-6-001  
**対応要件**: REQ-AA-NFR-001

---

#### TSK-AA-6-003: README & 使用ガイド [1.5h]

**説明**: パッケージドキュメントの作成

**成果物**:
- `packages/assistant-axis/README.md`
- `docs/packages/assistant-axis.md`
- CHANGELOG.md への追記

**内容**:
- インストール方法
- クイックスタート
- 設定リファレンス
- MCPツール一覧
- CLIコマンド一覧
- ワークフロー統合ガイド

**受入条件**:
- [ ] READMEが完成していること
- [ ] 使用例が含まれていること
- [ ] 設定項目が網羅されていること

**依存**: TSK-AA-6-001

---

## 3. 依存関係図

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         Task Dependency Graph                                │
│                                                                              │
│  Phase 1: パッケージ初期化                                                    │
│  ┌─────────────┐                                                            │
│  │TSK-AA-1-001 │ パッケージスキャフォールド                                    │
│  └──────┬──────┘                                                            │
│         │                                                                    │
│         ▼                                                                    │
│  ┌─────────────┐                                                            │
│  │TSK-AA-1-002 │ 設定スキーマ                                                │
│  └──────┬──────┘                                                            │
│         │                                                                    │
│  Phase 2: ドメイン層                                                         │
│         ├──────────────────┬──────────────────┬──────────────────┐          │
│         ▼                  ▼                  ▼                  ▼          │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐    ┌─────────────┐  │
│  │TSK-AA-2-001 │    │TSK-AA-2-002 │    │TSK-AA-2-003 │    │TSK-AA-2-004 │  │
│  │ DriftScore  │    │ Domain      │    │ Trigger     │    │ Reinforce   │  │
│  └──────┬──────┘    └──────┬──────┘    └──────┬──────┘    └──────┬──────┘  │
│         │                  │                  │                  │          │
│         └────────┬─────────┴──────────────────┘                  │          │
│                  │                                               │          │
│                  ▼                                               │          │
│           ┌─────────────┐                                        │          │
│           │TSK-AA-2-005 │ Session & Trajectory                   │          │
│           └──────┬──────┘                                        │          │
│                  │                                               │          │
│                  └───────────────────┬───────────────────────────┘          │
│                                      │                                      │
│                               ┌──────▼──────┐                               │
│                               │TSK-AA-2-006 │ Domain Events                 │
│                               └──────┬──────┘                               │
│                                      │                                      │
│  Phase 3: アプリケーション層                                                 │
│         ┌────────────────────────────┼────────────────────────────┐         │
│         │                            │                            │         │
│         ▼                            ▼                            ▼         │
│  ┌─────────────┐              ┌─────────────┐              ┌─────────────┐ │
│  │TSK-AA-3-001 │              │TSK-AA-3-002 │              │TSK-AA-3-003 │ │
│  │DriftAnalyzer│              │DomainClass  │              │IdentityMgr │ │
│  └──────┬──────┘              └──────┬──────┘              └──────┬──────┘ │
│         │                            │                            │         │
│         └────────────────────────────┼────────────────────────────┘         │
│                                      │                                      │
│                               ┌──────▼──────┐                               │
│                               │TSK-AA-3-004 │ PersonaMonitor                │
│                               └──────┬──────┘                               │
│                                      │                                      │
│                               ┌──────▼──────┐                               │
│                               │TSK-AA-3-005 │ Public API                    │
│                               └──────┬──────┘                               │
│                                      │                                      │
│  Phase 4: インフラ層                 │                                      │
│         ┌────────────────────────────┼────────────────────────────┐         │
│         │                            │                            │         │
│         ▼                            ▼                            ▼         │
│  ┌─────────────┐              ┌─────────────┐              ┌─────────────┐ │
│  │TSK-AA-4-001 │              │TSK-AA-4-002 │              │TSK-AA-4-003⭐│ │
│  │ConfigLoader │              │EventLogger  │              │WorkflowInt  │ │
│  └─────────────┘              └─────────────┘              └──────┬──────┘ │
│                                                                   │         │
│  Phase 5: 既存パッケージ統合                                      │         │
│         ┌─────────────────────────────────────────────────────────┤         │
│         │                            │                            │         │
│         ▼                            ▼                            ▼         │
│  ┌─────────────┐              ┌─────────────┐              ┌─────────────┐ │
│  │TSK-AA-5-001 │              │TSK-AA-5-002 │              │TSK-AA-5-003 │ │
│  │ MCP Tools   │              │ CLI Cmds    │              │ Skill Reg   │ │
│  └──────┬──────┘              └─────────────┘              └─────────────┘ │
│         │                                                                   │
│         │                     ┌─────────────┐                               │
│         │                     │TSK-AA-5-004⭐│ Workflow Hook                 │
│         │                     └──────┬──────┘                               │
│         │                            │                                      │
│         └────────────────────────────┼──────────────────────────────────────│
│                                      │                                      │
│                               ┌──────▼──────┐                               │
│                               │TSK-AA-5-005 │ 統合テスト                    │
│                               └──────┬──────┘                               │
│                                      │                                      │
│  Phase 6: テスト・ドキュメント                                               │
│         ┌────────────────────────────┼────────────────────────────┐         │
│         ▼                            ▼                            ▼         │
│  ┌─────────────┐              ┌─────────────┐              ┌─────────────┐ │
│  │TSK-AA-6-001 │              │TSK-AA-6-002 │              │TSK-AA-6-003 │ │
│  │ E2E Test    │              │ Perf Test   │              │ Docs        │ │
│  └─────────────┘              └─────────────┘              └─────────────┘ │
│                                                                              │
│  ⭐ = ワークフロー統合の重要タスク                                           │
└──────────────────────────────────────────────────────────────────────────────┘
```

---

## 4. ワークフロー統合ポイント（詳細）

### 4.1 統合アーキテクチャ

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                   MUSUBIX Workflow Integration Points                        │
│                                                                              │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                    User / AI Coding Agent                             │   │
│  └────────────────────────────────┬─────────────────────────────────────┘   │
│                                   │                                          │
│                                   ▼                                          │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                         mcp-server                                    │   │
│  │  ┌────────────────┐  ┌────────────────┐  ┌────────────────────────┐  │   │
│  │  │ sdd-tools      │  │ workflow-tools │  │ assistant-axis-tools   │  │   │
│  │  │ (既存)         │  │ (既存)         │  │ (新規: TSK-AA-5-001)   │  │   │
│  │  └────────────────┘  └───────┬────────┘  └───────────┬────────────┘  │   │
│  └──────────────────────────────┼───────────────────────┼────────────────┘   │
│                                 │                       │                    │
│                                 ▼                       │                    │
│  ┌──────────────────────────────────────────────────────┼────────────────┐   │
│  │                    workflow-engine                   │                │   │
│  │  ┌────────────────────────────────────────────────┐  │                │   │
│  │  │              PhaseController                    │  │                │   │
│  │  │  ┌─────────────────────────────────────────┐   │  │                │   │
│  │  │  │ Phase Change Hook (TSK-AA-5-004) ⭐     │<──┼──┘                │   │
│  │  │  │                                         │   │                   │   │
│  │  │  │  onPhaseChange(phase) {                 │   │                   │   │
│  │  │  │    hooks.forEach(h => h.notify(phase)); │   │                   │   │
│  │  │  │  }                                      │   │                   │   │
│  │  │  └─────────────────────────────────────────┘   │                   │   │
│  │  └────────────────────────────────────────────────┘                   │   │
│  └───────────────────────────────┬───────────────────────────────────────┘   │
│                                  │                                           │
│                                  │ PhaseChangedEvent                         │
│                                  ▼                                           │
│  ┌───────────────────────────────────────────────────────────────────────┐   │
│  │                      assistant-axis                                    │   │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │   │
│  │  │              WorkflowIntegration (TSK-AA-4-003) ⭐              │  │   │
│  │  │                                                                  │  │   │
│  │  │  ┌───────────────────────────────────────────────────────────┐  │  │   │
│  │  │  │ PHASE_MONITORING_LEVELS                                    │  │  │   │
│  │  │  │   requirements: HIGH (100%)                                │  │  │   │
│  │  │  │   design:       HIGH (100%)                                │  │  │   │
│  │  │  │   tasks:        MEDIUM (75%)                               │  │  │   │
│  │  │  │   implementation: LOW (50%) ← coding=safe                  │  │  │   │
│  │  │  │   done:         OFF (0%)                                   │  │  │   │
│  │  │  └───────────────────────────────────────────────────────────┘  │  │   │
│  │  └─────────────────────────────────────────────────────────────────┘  │   │
│  │                                                                        │   │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │   │
│  │  │                     PersonaMonitor                               │  │   │
│  │  │                                                                  │  │   │
│  │  │  onPhaseChange(phase) {                                          │  │   │
│  │  │    this.monitoringLevel = PHASE_MONITORING_LEVELS[phase];        │  │   │
│  │  │    this.adjustFrequency();                                       │  │   │
│  │  │  }                                                               │  │   │
│  │  └─────────────────────────────────────────────────────────────────┘  │   │
│  └────────────────────────────────────────────────────────────────────────┘   │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
```

### 4.2 統合シーケンス

```
User        mcp-server    workflow-engine    assistant-axis     Claude
 │              │               │                  │               │
 │ create_workflow()            │                  │               │
 │ ─────────────────────────────>                  │               │
 │              │               │                  │               │
 │              │  createWorkflow(name)            │               │
 │              │ ─────────────>│                  │               │
 │              │               │                  │               │
 │              │               │ PhaseChanged     │               │
 │              │               │ (requirements)   │               │
 │              │               │ ────────────────>│               │
 │              │               │                  │               │
 │              │               │                  │ setLevel(HIGH)│
 │              │               │                  │ ────────>     │
 │              │               │                  │               │
 │ userMessage("create login feature")             │               │
 │ ────────────────────────────────────────────────>               │
 │              │               │                  │               │
 │              │               │  analyze(msg)    │               │
 │              │               │ <────────────────│               │
 │              │               │                  │               │
 │              │               │                  │ DriftScore=0.2│
 │              │               │                  │ (LOW, safe)   │
 │              │               │                  │               │
 │              │               │                  │               │
 │ advance_phase(design)        │                  │               │
 │ ─────────────────────────────>                  │               │
 │              │               │ PhaseChanged     │               │
 │              │               │ (design)         │               │
 │              │               │ ────────────────>│               │
 │              │               │                  │ setLevel(HIGH)│
 │              │               │                  │               │
 │ ... (design phase) ...       │                  │               │
 │              │               │                  │               │
 │ advance_phase(implementation)│                  │               │
 │ ─────────────────────────────>                  │               │
 │              │               │ PhaseChanged     │               │
 │              │               │ (implementation) │               │
 │              │               │ ────────────────>│               │
 │              │               │                  │ setLevel(LOW) │
 │              │               │                  │ ← coding=safe │
 │              │               │                  │   (50% freq)  │
```

---

## 5. 実装優先順位サマリー

### クリティカルパス

```
TSK-AA-1-001 → TSK-AA-1-002 → TSK-AA-2-001〜006 → TSK-AA-3-001〜004 
→ TSK-AA-4-003⭐ → TSK-AA-5-004⭐ → TSK-AA-5-005 → TSK-AA-6-001
```

### 優先度別タスク

| 優先度 | タスク | 理由 |
|--------|-------|------|
| **P0** | TSK-AA-1-001, 1-002 | 基盤（他すべてが依存） |
| **P0** | TSK-AA-2-001〜003 | コアドメインモデル |
| **P0** | TSK-AA-3-001, 3-004 | ドリフト検出の中核 |
| **P0** | TSK-AA-4-003⭐ | ワークフロー統合（重要） |
| **P0** | TSK-AA-5-004⭐ | ワークフローフック（重要） |
| **P1** | TSK-AA-5-001, 5-002 | MCP/CLI統合 |
| **P1** | TSK-AA-6-001 | 統合テスト |
| **P2** | TSK-AA-4-004 | メトリクス（任意） |
| **P2** | TSK-AA-6-003 | ドキュメント |

---

## 6. トレーサビリティマトリクス (DES → TSK)

| 設計コンポーネント | タスクID | 対応要件 |
|------------------|---------|---------|
| DriftScore (VO) | TSK-AA-2-001 | REQ-AA-DRIFT-001, DRIFT-004 |
| ConversationDomain (VO) | TSK-AA-2-002 | REQ-AA-DRIFT-002, DRIFT-005 |
| TriggerPattern (VO) | TSK-AA-2-003 | REQ-AA-DRIFT-001 |
| ReinforcementPrompt (VO) | TSK-AA-2-004 | REQ-AA-STAB-001, STAB-004 |
| Session, Trajectory (Entity) | TSK-AA-2-005 | REQ-AA-DRIFT-003 |
| DriftAnalyzer | TSK-AA-3-001 | REQ-AA-DRIFT-001, DRIFT-003, DRIFT-004 |
| DomainClassifier | TSK-AA-3-002 | REQ-AA-DRIFT-002, DRIFT-005 |
| IdentityManager | TSK-AA-3-003 | REQ-AA-STAB-001, STAB-002, STAB-004 |
| PersonaMonitor | TSK-AA-3-004 | REQ-AA-DRIFT-003, STAB-002 |
| WorkflowIntegration | TSK-AA-4-003 | REQ-AA-INT-002 |
| MCP Tools | TSK-AA-5-001 | REQ-AA-INT-001 |
| CLI Commands | TSK-AA-5-002 | REQ-AA-INT-006 |
| Skill Registration | TSK-AA-5-003 | REQ-AA-INT-003 |
| Workflow Hook | TSK-AA-5-004 | REQ-AA-INT-002 |

---

## 7. 承認

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
