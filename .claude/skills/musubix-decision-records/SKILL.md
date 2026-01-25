# MUSUBIX Decision Records スキル

> ADR（Architecture Decision Records）の作成・管理

## WHEN/DO トリガー

| WHEN | DO |
|------|-----|
| 設計判断の記録が必要 | `manager.create()` でADR作成 |
| 承認待ちADRの確認 | `manager.list({ status: 'proposed' })` |
| 決定を承認 | `manager.accept(id)` |
| 古いADRを置き換え | `manager.deprecate(oldId, newId)` |

## クイック使用法

```typescript
import { createDecisionManager } from '@musubix/decisions';

const manager = createDecisionManager('docs/decisions');

// ADR作成
const adr = await manager.create({
  title: 'JWT認証の採用',
  context: 'ユーザー認証の仕組みが必要',
  decision: 'JWTトークンベースの認証を採用',
  rationale: 'ステートレスでスケーラブル',
  alternatives: ['セッションベース', 'OAuth2のみ'],
  consequences: ['トークン失効の仕組みが必要'],
  relatedRequirements: ['REQ-AUTH-001'],
  decider: 'Tech Lead',
});

// 操作
await manager.accept('0001');                  // 承認
await manager.deprecate('0001', '0005');       // 置き換え
const adrs = await manager.search('認証');     // 検索
await manager.generateIndex();                 // index.md生成
```

## ADRステータス

| ステータス | 説明 |
|-----------|------|
| `proposed` | 提案中（レビュー待ち） |
| `accepted` | 承認済み（有効） |
| `deprecated` | 非推奨 |
| `superseded` | 別のADRに置き換え済み |

## ストレージ

```
docs/decisions/
├── index.md              # ADRインデックス（自動生成）
├── 0001-jwt-auth.md      # ADR #1
└── 0002-adopt-ddd.md     # ADR #2
```

## 出力フォーマット

```
┌─────────────────────────────────────────┐
│ ADR-0001: JWT認証の採用                  │
├─────────────────────────────────────────┤
│ Status: Proposed | Date: 2026-01-12     │
│ Decider: Tech Lead                      │
│ Related: REQ-AUTH-001                   │
├─────────────────────────────────────────┤
│ Context: ユーザー認証の仕組みが必要      │
│ Decision: JWTトークンベースの認証を採用  │
│ Rationale: ステートレスでスケーラブル    │
└─────────────────────────────────────────┘
```
