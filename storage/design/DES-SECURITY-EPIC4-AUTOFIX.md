# EPIC-4: 自動修正提案 設計書

**Version**: 1.0.0
**Date**: 2026-01-08
**Status**: ✅ APPROVED
**Trace**: REQ-FIX-001 〜 REQ-FIX-005

---

## 1. 概要

### 1.1 目的

検出された脆弱性に対して、VS Code LM API 経由で LLM による修正提案を生成し、Z3 SMT Solver で形式検証を行うシステムを設計する。

### 1.2 設計方針

- **VS Code LM API**: Copilot/LLM へのアクセス抽象化
- **Z3 Integration**: musubix-formal-verify パッケージとの連携
- **Human-in-the-loop**: 自動適用は人間承認必須

---

## 2. C4モデル

### 2.1 Container Diagram

```
┌──────────────────────────────────────────────────────────────────────┐
│                         VS Code Extension                             │
│  ┌────────────────────┐                                              │
│  │   VS Code LM API   │◀─────────────────────────────────────────┐   │
│  └────────────────────┘                                          │   │
└───────────────────────────────────────────────────────────────────┼───┘
                                                                    │
┌───────────────────────────────────────────────────────────────────┼───┐
│                      MUSUBIX Security Package                     │   │
│                                                                   │   │
│  ┌────────────────────┐     ┌────────────────────┐               │   │
│  │  Rule Engine       │────▶│  Fix Generator     │───────────────┘   │
│  │  (Findings)        │     │  (LLM Integration) │                   │
│  └────────────────────┘     └─────────┬──────────┘                   │
│                                       │ fix suggestions              │
│                                       ▼                              │
│                            ┌────────────────────┐                    │
│                            │  Fix Verifier      │                    │
│                            │  (Z3 Integration)  │                    │
│                            └─────────┬──────────┘                    │
│                                      │ verified fixes                │
│                                      ▼                               │
│                            ┌────────────────────┐                    │
│                            │  Safety Scorer     │                    │
│                            │  (Multi-criteria)  │                    │
│                            └─────────┬──────────┘                    │
│                                      │ scored fixes                  │
│                                      ▼                               │
│                            ┌────────────────────┐                    │
│                            │  Patch Applier     │                    │
│                            │  (Human Approval)  │                    │
│                            └────────────────────┘                    │
│                                                                      │
└──────────────────────────────────────────────────────────────────────┘
                                       │
                                       ▼
                            ┌────────────────────┐
                            │  musubix-formal-   │
                            │  verify (Z3)       │
                            └────────────────────┘
```

### 2.2 Component Diagram

```
packages/security/src/
├── autofix/                         # NEW: 自動修正モジュール
│   ├── index.ts                     # Public exports
│   ├── llm/
│   │   ├── lm-api-adapter.ts        # VS Code LM API アダプター
│   │   ├── prompt-builder.ts        # プロンプト構築
│   │   ├── prompt-templates.ts      # プロンプトテンプレート
│   │   └── response-parser.ts       # LLM レスポンスパーサー
│   ├── verification/
│   │   ├── z3-adapter.ts            # Z3 統合アダプター
│   │   ├── semantic-verifier.ts     # セマンティクス検証
│   │   ├── taint-verifier.ts        # テイントフロー検証
│   │   └── verification-result.ts   # 検証結果型
│   ├── scoring/
│   │   ├── safety-scorer.ts         # 安全性スコアリング
│   │   ├── criteria.ts              # 評価基準定義
│   │   └── score-calculator.ts      # スコア計算
│   ├── patch/
│   │   ├── patch-applier.ts         # パッチ適用
│   │   ├── diff-generator.ts        # diff 生成
│   │   ├── backup-manager.ts        # バックアップ管理
│   │   └── rollback.ts              # ロールバック
│   └── learning/
│       ├── feedback-collector.ts    # フィードバック収集
│       └── pattern-learner.ts       # パターン学習
└── types/
    └── autofix.ts                   # 型定義
```

---

## 3. コンポーネント設計

### 3.1 DES-FIX-001: VS Code LM API Adapter

**Trace**: REQ-FIX-001

```typescript
// packages/security/src/autofix/llm/lm-api-adapter.ts

/**
 * VS Code LM API アダプター
 * VS Code 拡張機能内で Copilot/LLM にアクセス
 */
export interface LMApiAdapter {
  /**
   * LLM が利用可能か
   */
  isAvailable(): Promise<boolean>;
  
  /**
   * 修正提案を生成
   */
  generateFix(request: FixRequest): Promise<FixSuggestion[]>;
  
  /**
   * ストリーミング生成
   */
  generateFixStream(
    request: FixRequest,
    onChunk: (chunk: string) => void
  ): Promise<FixSuggestion[]>;
}

/**
 * VS Code LM API 実装
 */
export class VSCodeLMAdapter implements LMApiAdapter {
  constructor(private readonly extensionContext: vscode.ExtensionContext);
  
  async isAvailable(): Promise<boolean> {
    // VS Code LM API の存在確認
    return typeof vscode !== 'undefined' && 
           vscode.lm !== undefined &&
           (await vscode.lm.selectChatModels()).length > 0;
  }
  
  async generateFix(request: FixRequest): Promise<FixSuggestion[]> {
    const models = await vscode.lm.selectChatModels({
      vendor: 'copilot',
      family: 'gpt-4'
    });
    
    if (models.length === 0) {
      throw new Error('No LLM models available');
    }
    
    const prompt = this.buildPrompt(request);
    const response = await models[0].sendRequest(
      [vscode.LanguageModelChatMessage.User(prompt)],
      {},
      new vscode.CancellationTokenSource().token
    );
    
    return this.parseResponse(response);
  }
}

/**
 * CLI/テスト用モックアダプター
 */
export class MockLMAdapter implements LMApiAdapter {
  async isAvailable(): Promise<boolean> {
    return false; // CLI では LM API 利用不可
  }
  
  async generateFix(request: FixRequest): Promise<FixSuggestion[]> {
    // テンプレートベースの簡易修正提案
    return this.generateTemplateBasedFix(request);
  }
}
```

### 3.2 DES-FIX-002: Prompt Builder

**Trace**: REQ-FIX-001

```typescript
// packages/security/src/autofix/llm/prompt-builder.ts

/**
 * 修正リクエスト
 */
export interface FixRequest {
  /** 検出結果 */
  finding: RuleFinding;
  /** 脆弱なコード */
  vulnerableCode: string;
  /** コンテキスト（前後のコード） */
  context: CodeContext;
  /** CWE 詳細情報 */
  cweInfo?: CWEInfo;
  /** 言語/フレームワーク */
  language: string;
  framework?: string;
}

/**
 * プロンプトビルダー
 */
export class PromptBuilder {
  private templates: Map<string, string>;
  
  constructor();
  
  /**
   * 修正提案プロンプトを構築
   */
  buildFixPrompt(request: FixRequest): string {
    return `
You are a security expert fixing a ${request.finding.cwe} vulnerability.

## Vulnerability Details
- **CWE**: ${request.finding.cwe}
- **Severity**: ${request.finding.severity}
- **Description**: ${request.finding.message}

## Vulnerable Code
\`\`\`${request.language}
${request.vulnerableCode}
\`\`\`

## Context
${request.context.before}
// <VULNERABLE CODE HERE>
${request.context.after}

## Requirements
1. Fix the vulnerability while preserving the original functionality
2. Use proper sanitization/validation for ${request.finding.cwe}
3. Provide up to 3 different fix approaches
4. Each fix must include:
   - A brief explanation
   - The fixed code as a unified diff

## Output Format
Provide fixes in the following JSON format:
\`\`\`json
{
  "fixes": [
    {
      "approach": "description of the approach",
      "explanation": "why this fix works",
      "diff": "unified diff here"
    }
  ]
}
\`\`\`
`;
  }
  
  /**
   * カスタムテンプレートを登録
   */
  registerTemplate(cwe: string, template: string): void;
}
```

### 3.3 DES-FIX-003: Z3 Adapter

**Trace**: REQ-FIX-002

```typescript
// packages/security/src/autofix/verification/z3-adapter.ts

import { Z3Solver } from '@nahisaho/musubix-formal-verify';

/**
 * Z3 統合アダプター
 */
export class Z3Adapter {
  private solver: Z3Solver;
  
  constructor();
  
  /**
   * セマンティクス保持検証
   * 修正前後で同じ入力に対して同じ出力を返すか
   */
  async verifySemanticPreservation(
    original: string,
    fixed: string
  ): Promise<VerificationResult>;
  
  /**
   * テイントフロー除去検証
   * 修正後にテイントが sink に到達しないか
   */
  async verifyTaintRemoval(
    fixed: string,
    taintFlow: TaintFlow
  ): Promise<VerificationResult>;
  
  /**
   * 入力バリデーション追加検証
   * 適切なバリデーションが追加されているか
   */
  async verifyInputValidation(
    fixed: string,
    expectedValidation: ValidationSpec
  ): Promise<VerificationResult>;
}

export interface VerificationResult {
  verified: boolean;
  confidence: number;  // 0.0 - 1.0
  details: string;
  counterexample?: string;  // 検証失敗時の反例
}
```

### 3.4 DES-FIX-004: Semantic Verifier

**Trace**: REQ-FIX-002

```typescript
// packages/security/src/autofix/verification/semantic-verifier.ts

/**
 * セマンティクス検証器
 */
export class SemanticVerifier {
  private z3Adapter: Z3Adapter;
  private taintAnalyzer: EnhancedTaintAnalyzer;
  
  constructor(z3Adapter: Z3Adapter);
  
  /**
   * 修正を包括的に検証
   */
  async verify(
    original: string,
    fixed: string,
    finding: RuleFinding
  ): Promise<VerificationReport> {
    const results: VerificationResult[] = [];
    
    // 1. セマンティクス保持
    results.push(await this.z3Adapter.verifySemanticPreservation(original, fixed));
    
    // 2. テイントフロー除去
    const originalTaint = await this.taintAnalyzer.analyze(original);
    const fixedTaint = await this.taintAnalyzer.analyze(fixed);
    results.push(this.compareTaintFlows(originalTaint, fixedTaint, finding));
    
    // 3. 新規脆弱性の導入チェック
    results.push(await this.checkNoNewVulnerabilities(fixed));
    
    return this.aggregateResults(results);
  }
}

export interface VerificationReport {
  passed: boolean;
  overallConfidence: number;
  results: VerificationResult[];
  recommendations: string[];
}
```

### 3.5 DES-FIX-005: Safety Scorer

**Trace**: REQ-FIX-003

```typescript
// packages/security/src/autofix/scoring/safety-scorer.ts

/**
 * 安全性スコアリング基準
 */
export interface ScoringCriteria {
  /** セマンティクス保持 (30%) */
  semanticPreservation: number;
  /** 脆弱性除去 (30%) */
  vulnerabilityRemoval: number;
  /** コード品質 (20%) */
  codeQuality: number;
  /** パフォーマンス影響 (10%) */
  performanceImpact: number;
  /** 後方互換性 (10%) */
  backwardCompatibility: number;
}

/**
 * 修正安全性スコア
 */
export interface SafetyScore {
  total: number;  // 0.0 - 1.0
  criteria: ScoringCriteria;
  humanReviewRequired: boolean;
  recommendation: 'apply' | 'review' | 'reject';
}

/**
 * 安全性スコアラー
 */
export class SafetyScorer {
  private threshold: number = 0.7;
  
  constructor(options?: ScorerOptions);
  
  /**
   * 修正をスコアリング
   */
  async score(
    original: string,
    fixed: string,
    verification: VerificationReport
  ): Promise<SafetyScore> {
    const criteria: ScoringCriteria = {
      semanticPreservation: this.scoreSemantics(verification),
      vulnerabilityRemoval: this.scoreVulnRemoval(verification),
      codeQuality: await this.scoreCodeQuality(fixed),
      performanceImpact: await this.scorePerformance(original, fixed),
      backwardCompatibility: this.scoreCompatibility(original, fixed),
    };
    
    const total = this.calculateTotal(criteria);
    
    return {
      total,
      criteria,
      humanReviewRequired: total < this.threshold || !verification.passed,
      recommendation: this.getRecommendation(total, verification),
    };
  }
  
  private calculateTotal(criteria: ScoringCriteria): number {
    return (
      criteria.semanticPreservation * 0.30 +
      criteria.vulnerabilityRemoval * 0.30 +
      criteria.codeQuality * 0.20 +
      criteria.performanceImpact * 0.10 +
      criteria.backwardCompatibility * 0.10
    );
  }
}
```

### 3.6 DES-FIX-006: Patch Applier

**Trace**: REQ-FIX-004

```typescript
// packages/security/src/autofix/patch/patch-applier.ts

/**
 * パッチ適用オプション
 */
export interface PatchOptions {
  /** バックアップを作成 */
  backup?: boolean;
  /** 適用後にビルド検証 */
  verifyBuild?: boolean;
  /** 適用後にテスト実行 */
  runTests?: boolean;
  /** Git コミット自動作成 */
  gitCommit?: boolean;
}

/**
 * パッチ適用結果
 */
export interface PatchResult {
  success: boolean;
  filePath: string;
  backupPath?: string;
  buildPassed?: boolean;
  testsPassed?: boolean;
  gitCommitHash?: string;
  error?: string;
}

/**
 * パッチ適用エンジン
 */
export class PatchApplier {
  private backupManager: BackupManager;
  
  constructor();
  
  /**
   * パッチを適用（人間承認後）
   */
  async apply(
    filePath: string,
    diff: string,
    options?: PatchOptions
  ): Promise<PatchResult> {
    // 1. バックアップ作成
    const backupPath = options?.backup 
      ? await this.backupManager.create(filePath)
      : undefined;
    
    try {
      // 2. diff 適用
      await this.applyDiff(filePath, diff);
      
      // 3. ビルド検証
      const buildPassed = options?.verifyBuild
        ? await this.verifyBuild(filePath)
        : undefined;
      
      // 4. テスト実行
      const testsPassed = options?.runTests
        ? await this.runTests(filePath)
        : undefined;
      
      // 5. Git コミット
      const gitCommitHash = options?.gitCommit
        ? await this.createCommit(filePath, diff)
        : undefined;
      
      return {
        success: true,
        filePath,
        backupPath,
        buildPassed,
        testsPassed,
        gitCommitHash,
      };
    } catch (error) {
      // ロールバック
      if (backupPath) {
        await this.backupManager.restore(backupPath, filePath);
      }
      return {
        success: false,
        filePath,
        error: error instanceof Error ? error.message : String(error),
      };
    }
  }
  
  /**
   * ロールバック
   */
  async rollback(patchResult: PatchResult): Promise<void>;
}
```

### 3.7 DES-FIX-007: Feedback Collector

**Trace**: REQ-FIX-005

```typescript
// packages/security/src/autofix/learning/feedback-collector.ts

/**
 * フィードバック種別
 */
export type FeedbackType = 'accepted' | 'rejected' | 'modified';

/**
 * 修正フィードバック
 */
export interface FixFeedback {
  id: string;
  timestamp: Date;
  finding: RuleFinding;
  suggestion: FixSuggestion;
  feedback: FeedbackType;
  modifiedCode?: string;  // 修正された場合
  reason?: string;
}

/**
 * フィードバック収集
 */
export class FeedbackCollector {
  private storage: FeedbackStorage;
  
  constructor(storagePath: string);
  
  /**
   * フィードバックを記録
   */
  async record(feedback: FixFeedback): Promise<void>;
  
  /**
   * 類似脆弱性のフィードバックを取得
   */
  async getSimilarFeedback(finding: RuleFinding): Promise<FixFeedback[]>;
  
  /**
   * 統計を取得
   */
  async getStats(): Promise<FeedbackStats>;
}

/**
 * パターン学習
 */
export class PatternLearner {
  /**
   * フィードバックからパターンを抽出
   */
  async learnFromFeedback(feedbacks: FixFeedback[]): Promise<FixPattern[]>;
  
  /**
   * 学習済みパターンを適用
   */
  async applyLearnedPatterns(finding: RuleFinding): Promise<FixSuggestion | null>;
}
```

---

## 4. データフロー

```
┌─────────────────┐
│  RuleFinding    │
│  (From EPIC-3)  │
└────────┬────────┘
         │
         ▼
┌─────────────────┐     ┌─────────────────┐
│  Prompt Builder │────▶│  VS Code LM API │
│                 │     │  (Copilot)      │
└─────────────────┘     └────────┬────────┘
                                 │ FixSuggestion[]
                                 ▼
┌─────────────────┐     ┌─────────────────┐
│  Z3 Adapter     │◀────│  Semantic       │
│                 │     │  Verifier       │
└─────────────────┘     └────────┬────────┘
                                 │ VerificationReport
                                 ▼
                        ┌─────────────────┐
                        │  Safety Scorer  │
                        └────────┬────────┘
                                 │ SafetyScore
                                 ▼
                        ┌─────────────────┐
                        │  Human Review   │◀── User Decision
                        │  (VS Code UI)   │
                        └────────┬────────┘
                                 │ Approved
                                 ▼
                        ┌─────────────────┐
                        │  Patch Applier  │────▶ Fixed Code
                        └────────┬────────┘
                                 │
                                 ▼
                        ┌─────────────────┐
                        │  Feedback       │
                        │  Collector      │
                        └─────────────────┘
```

---

## 5. VS Code 統合

### 5.1 コマンド

| コマンド | 説明 |
|---------|------|
| `musubix.security.suggestFix` | 選択範囲の脆弱性に対して修正提案 |
| `musubix.security.applyFix` | 修正を適用 |
| `musubix.security.previewFix` | 修正をプレビュー |

### 5.2 CodeAction

```typescript
// VS Code CodeActionProvider
class SecurityFixProvider implements vscode.CodeActionProvider {
  provideCodeActions(
    document: vscode.TextDocument,
    range: vscode.Range,
    context: vscode.CodeActionContext
  ): vscode.CodeAction[] {
    // Diagnostics から脆弱性を取得
    const findings = context.diagnostics.filter(d => 
      d.source === 'musubix-security'
    );
    
    return findings.map(f => {
      const action = new vscode.CodeAction(
        `Fix ${f.code}: ${f.message}`,
        vscode.CodeActionKind.QuickFix
      );
      action.command = {
        command: 'musubix.security.suggestFix',
        arguments: [f],
      };
      return action;
    });
  }
}
```

---

## 6. タスク → 設計 トレーサビリティ

| タスク | 設計 |
|--------|------|
| TSK-FIX-001 | DES-FIX-001 (VS Code LM API Adapter) |
| TSK-FIX-002 | DES-FIX-002 (Prompt Builder) |
| TSK-FIX-003 | DES-FIX-001, DES-FIX-002 (LLM Fix Generator) |
| TSK-FIX-004 | DES-FIX-003 (Z3 Adapter) |
| TSK-FIX-005 | DES-FIX-004 (Semantic Verifier) |
| TSK-FIX-006 | DES-FIX-005 (Safety Scorer) |
| TSK-FIX-007 | DES-FIX-006 (Patch Applier) |
| TSK-FIX-008 | DES-FIX-007 (Feedback Collector) |

---

## 7. 承認

- [x] VS Code LM API 統合方針
- [x] Z3/formal-verify 連携
- [x] 安全性スコアリング基準
- [x] Human-in-the-loop 設計
- [x] ユーザー承認 (2026-01-08)
