# MUSUBIX 自己学習レポート: Project 11-12

**日時**: 2026-01-04
**バージョン**: v1.0.20
**対象プロジェクト**: 
- Project 11: ペット健康管理システム (PetCare)
- Project 12: コワーキングスペース予約システム (SpaceHub)

---

## 📊 プロジェクト概要

| 項目 | Project 11 | Project 12 |
|------|------------|------------|
| **ドメイン** | ヘルスケア | 予約管理 |
| **要件数** | 10 EARS | 12 EARS |
| **テスト数** | 22 | 24 |
| **コード行数** | ~550 | ~870 |
| **主要パターン** | StatusWorkflow, IdGenerator | TimeSlot, BillingService, StatusWorkflow |

---

## 🔍 抽出された学習パターン

### パターン1: TimeSlotService（NEW！）

**概要**: 時間帯ベースの予約システムで必須のユーティリティ

**適用コンテキスト**:
- 時間枠（スロット）ベースの予約
- 連続予約間のバッファ管理
- 時間制約の検証

**コード例**:
```typescript
class TimeSlotService {
  private slotMinutes: number;
  private bufferMinutes: number;

  validateDuration(startTime: Date, endTime: Date): void {
    const durationMinutes = (endTime.getTime() - startTime.getTime()) / (1000 * 60);
    if (durationMinutes % this.slotMinutes !== 0) {
      throw new Error(`Duration must be in ${this.slotMinutes} minute increments`);
    }
  }

  hasConflict(existingStart: Date, existingEnd: Date, newStart: Date, newEnd: Date): boolean {
    const bufferedEnd = new Date(existingEnd.getTime() + this.bufferMinutes * 60 * 1000);
    return newStart < bufferedEnd && newEnd > existingStart;
  }

  generateSlots(date: Date, startHour: number, endHour: number): TimeSlot[] {
    // 15分単位でスロット生成
  }
}
```

**信頼度**: 0.85
**出現回数**: 1回（Project 12）
**推奨度**: 高（予約システムで頻出）

---

### パターン2: BillingService（NEW！）

**概要**: 料金計算・返金ポリシーを管理するサービス

**適用コンテキスト**:
- 時間ベースの料金計算
- キャンセル・変更時の返金ポリシー
- 延長料金の計算

**コード例**:
```typescript
class BillingService {
  calculateFee(hourlyRate: number, minutes: number): number {
    const slots = Math.ceil(minutes / SLOT_MINUTES);
    const ratePerSlot = hourlyRate / (60 / SLOT_MINUTES);
    return Math.round(slots * ratePerSlot);
  }

  calculateRefund(
    originalAmount: number,
    reservationStart: Date,
    cancelTime: Date
  ): { amount: number; percentage: number } {
    const hoursUntilStart = (reservationStart.getTime() - cancelTime.getTime()) / (1000 * 60 * 60);
    
    if (hoursUntilStart >= FULL_REFUND_HOURS) {
      return { amount: originalAmount, percentage: 100 };
    } else if (hoursUntilStart > 0) {
      return { amount: Math.round(originalAmount * 0.5), percentage: 50 };
    }
    return { amount: 0, percentage: 0 };
  }
}
```

**信頼度**: 0.80
**出現回数**: 1回（Project 12）
**推奨度**: 高（SaaSシステムで頻出）

---

### パターン3: StatusWorkflow（既存パターンの強化）

**概要**: 状態遷移を管理するジェネリックなワークフローエンジン

**Project 11での使用**:
- Appointment: tentative → confirmed → active → completed

**Project 12での使用**:
- Reservation: pending → confirmed → checked_in → completed/cancelled/no_show

**改善点**: 
- 複数の終端状態（completed, cancelled, no_show）のサポート
- アクション名に基づく遷移（confirm, check_in, cancel等）

**コード例**:
```typescript
interface StatusTransition<T extends string> {
  from: T;
  to: T;
  action: string;
}

class StatusWorkflow<T extends string> {
  constructor(private transitions: StatusTransition<T>[]) {}

  canTransition(from: T, action: string): boolean {
    return this.transitions.some((t) => t.from === from && t.action === action);
  }

  transition(from: T, action: string): T {
    const found = this.transitions.find((t) => t.from === from && t.action === action);
    if (!found) throw new Error(`Invalid transition: ${from} -> ${action}`);
    return found.to;
  }

  getAvailableActions(status: T): string[] {
    return this.transitions.filter((t) => t.from === status).map((t) => t.action);
  }
}
```

**信頼度**: 0.92（2プロジェクトで検証）
**出現回数**: 2回（Project 10, 11, 12）
**推奨度**: 高（ビジネスロジックで必須）

---

### パターン4: ThresholdAlert（既存パターンの強化）

**概要**: 閾値ベースのアラート・通知パターン

**Project 11での使用**:
- WeightAlert: 体重変化が10%超でアラート

**コード例**:
```typescript
interface AlertResult {
  triggered: boolean;
  changePercent: number;
  previousValue: number;
  currentValue: number;
}

function checkThreshold(
  previousValue: number,
  currentValue: number,
  thresholdPercent: number
): AlertResult {
  const changePercent = Math.abs((currentValue - previousValue) / previousValue) * 100;
  return {
    triggered: changePercent > thresholdPercent,
    changePercent,
    previousValue,
    currentValue,
  };
}
```

**信頼度**: 0.85
**出現回数**: 2回（Project 10, 11）
**推奨度**: 中（モニタリング系で有用）

---

### パターン5: TimeWindowValidator（NEW！）

**概要**: 時間枠内の操作を検証するパターン

**適用コンテキスト**:
- チェックイン可能時間（開始15分前〜15分後）
- 変更可能期限（開始1時間前まで）
- キャンセル可能期限（開始2時間前まで）

**コード例**:
```typescript
class TimeWindowValidator {
  isWithinWindow(
    referenceTime: Date,
    checkTime: Date,
    windowMinutesBefore: number,
    windowMinutesAfter: number
  ): boolean {
    const windowStart = new Date(referenceTime.getTime() - windowMinutesBefore * 60 * 1000);
    const windowEnd = new Date(referenceTime.getTime() + windowMinutesAfter * 60 * 1000);
    return checkTime >= windowStart && checkTime <= windowEnd;
  }

  hoursUntil(targetTime: Date, currentTime: Date): number {
    return (targetTime.getTime() - currentTime.getTime()) / (1000 * 60 * 60);
  }
}
```

**信頼度**: 0.80
**出現回数**: 1回（Project 12）
**推奨度**: 高（予約系で必須）

---

## 📈 パターン適用マトリクス

| パターン | P11 | P12 | 累積出現 | 推奨追加 |
|---------|-----|-----|---------|---------|
| IdGenerator | ✅ | ✅ | 12回 | - (既存) |
| StatusWorkflow | ✅ | ✅ | 3回 | - (既存) |
| Repository | ✅ | ✅ | 12回 | - (既存) |
| ThresholdAlert | ✅ | - | 2回 | 検討中 |
| TimeSlotService | - | ✅ | 1回 | **推奨** |
| BillingService | - | ✅ | 1回 | **推奨** |
| TimeWindowValidator | - | ✅ | 1回 | **推奨** |

---

## 🎯 MUSUBIXへの改善提案

### 即時改善（v1.0.21向け）

1. **TimeSlotServiceユーティリティの追加**
   - `packages/core/src/utils/time-slot.ts`
   - 設定可能なスロット長、バッファ時間
   - 重複検出アルゴリズム

2. **BillingCalculatorユーティリティの追加**
   - `packages/core/src/utils/billing.ts`
   - 時間ベース料金計算
   - 返金ポリシー計算

3. **TimeWindowValidatorユーティリティの追加**
   - `packages/core/src/utils/time-window.ts`
   - 時間枠検証
   - 期限チェック

### 中期改善（v1.1.0向け）

1. **予約システムテンプレートの追加**
   - `templates/reservation-system/`
   - TimeSlot, Billing, StatusWorkflow統合
   - C4設計テンプレート

2. **ThresholdAlertユーティリティの追加**
   - `packages/core/src/utils/threshold-alert.ts`
   - 閾値ベースのアラートパターン

---

## 📋 EARS要件パターン分析

### よく使用されたEARSパターン

| パターン | P11 | P12 | 合計 |
|---------|-----|-----|------|
| Ubiquitous | 4 | 4 | 8 |
| Event-driven | 3 | 5 | 8 |
| State-driven | 2 | 2 | 4 |
| Unwanted | 1 | 1 | 2 |
| Optional | 0 | 0 | 0 |

### 要件記述の改善ポイント

1. **時間制約はEvent-drivenで明確に**
   ```
   ✓ WHEN [event happens], THE system SHALL [action within time]
   ✓ WHEN user attempts check-in within 15 minutes of start time,
     THE system SHALL allow check-in
   ```

2. **料金ルールはUbiquitousで定義**
   ```
   ✓ THE system SHALL calculate fees in 15-minute increments
   ✓ THE system SHALL apply 50% refund for cancellations within 2 hours
   ```

---

## 🔧 テスト戦略の改善

### テストカテゴリ分布

| カテゴリ | P11 | P12 |
|---------|-----|-----|
| CRUD操作 | 8 | 6 |
| バリデーション | 6 | 8 |
| 状態遷移 | 4 | 6 |
| 計算ロジック | 2 | 4 |
| エラーケース | 2 | 0 |

### 学習ポイント

1. **時間ベースのテストは固定時間を使用**
   - `new Date('2026-01-04T10:00:00')` のような固定値
   - 相対時間（`Date.now() + offset`）は避ける

2. **バッファ・ウィンドウは境界値テスト必須**
   - バッファ期間内/外
   - ウィンドウ開始/終了境界

---

## 📊 累積学習データ

### 全12プロジェクトの統計

| 指標 | 値 |
|------|-----|
| 総プロジェクト数 | 12 |
| 総要件数 | 108 |
| 総テスト数 | 232 |
| 平均要件/プロジェクト | 9 |
| 平均テスト/プロジェクト | 19.3 |
| テスト合格率 | 100% |

### 最頻出パターン（Top 5）

1. **Repository Pattern** - 12/12 プロジェクト
2. **IdGenerator** - 12/12 プロジェクト
3. **StatusWorkflow** - 3/12 プロジェクト
4. **ThresholdAlert** - 2/12 プロジェクト
5. **TimeSlotService** - 1/12 プロジェクト（NEW）

---

## 🚀 次のアクション

1. [x] Project 11 完了（22 tests）
2. [x] Project 12 完了（24 tests）
3. [ ] TimeSlotService を core に追加
4. [ ] BillingCalculator を core に追加
5. [ ] TimeWindowValidator を core に追加
6. [ ] v1.0.21 リリース

---

**Author**: MUSUBIX Learning System
**Generated**: 2026-01-04
