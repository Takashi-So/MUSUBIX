# MUSUBIX Decision Records スキル

このスキルを使用して、`@musubix/decisions` パッケージによるArchitecture Decision Records (ADR) を管理します。

## 概要

ADRはプロジェクトのアーキテクチャ決定を記録・追跡するためのドキュメントです。

## 基本的な使い方

### Decision Managerの初期化

```typescript
import { createDecisionManager } from '@musubix/decisions';

const manager = createDecisionManager('docs/decisions');
```

### ADRの作成

```typescript
const adr = await manager.create({
  title: 'JWT認証の採用',
  context: 'ユーザー認証の仕組みが必要。セッション管理のオーバーヘッドを避けたい。',
  decision: 'JWTトークンベースの認証を採用する。',
  rationale: 'ステートレスでスケーラブル。マイクロサービス間でも利用可能。',
  alternatives: ['セッションベース認証', 'OAuth2のみ'],
  consequences: ['トークン失効の仕組みが必要', 'トークンサイズに注意'],
  relatedRequirements: ['REQ-AUTH-001'],
  decider: 'Tech Lead',
});

console.log(`ADR-${adr.id} created: ${adr.title}`);
// => ADR-0001 created: JWT認証の採用
```

### ADRの取得

```typescript
const adr = await manager.get('0001');
if (adr) {
  console.log(adr.title);    // => 'JWT認証の採用'
  console.log(adr.status);   // => 'proposed'
}
```

### ADR一覧

```typescript
// 全ADR
const all = await manager.list();

// 承認済みのみ
const accepted = await manager.list({ status: 'accepted' });

// キーワード検索
const authRelated = await manager.list({ keyword: '認証' });
```

### ADRの承認

```typescript
const adr = await manager.accept('0001');
console.log(adr.status); // => 'accepted'
```

### ADRの非推奨化

```typescript
// 単純な非推奨
await manager.deprecate('0001');

// 別のADRに置き換え
await manager.deprecate('0001', '0005');
// 0001のステータスは 'superseded' になる
```

### ADR検索

```typescript
// キーワード検索
const results = await manager.search('認証');

// 要件に関連するADR
const adrs = await manager.findByRequirement('REQ-AUTH-001');
```

### インデックス生成

```typescript
await manager.generateIndex();
// docs/decisions/index.md が生成される
```

## ADRステータス

| ステータス | 説明 |
|-----------|------|
| `proposed` | 提案中（レビュー待ち） |
| `accepted` | 承認済み（有効） |
| `deprecated` | 非推奨（使用しないことを推奨） |
| `superseded` | 置き換え済み（別のADRに置き換わった） |

## ストレージ構造

```
docs/decisions/
├── index.md              # ADRインデックス（自動生成）
├── 0001-jwt-auth.md      # ADR #1
├── 0002-adopt-ddd.md     # ADR #2
└── ...
```

## ADRフォーマット

生成されるADRは以下の形式です：

```markdown
# ADR-0001: JWT認証の採用

| 項目 | 内容 |
|------|------|
| **ステータス** | Proposed |
| **日付** | 2026-01-12 |
| **決定者** | Tech Lead |
| **関連要件** | REQ-AUTH-001 |

## コンテキスト

ユーザー認証の仕組みが必要。セッション管理のオーバーヘッドを避けたい。

## 決定

JWTトークンベースの認証を採用する。

## 理由

ステートレスでスケーラブル。マイクロサービス間でも利用可能。

## 代替案

- セッションベース認証
- OAuth2のみ

## 影響

- トークン失効の仕組みが必要
- トークンサイズに注意
```

## 知識グラフとの連携

ADRを要件にリンクする場合、`@musubix/knowledge` と組み合わせて使用します：

```typescript
import { createKnowledgeStore } from '@musubix/knowledge';
import { createDecisionManager } from '@musubix/decisions';

const store = createKnowledgeStore('.knowledge');
const manager = createDecisionManager('docs/decisions');

// ADR作成
const adr = await manager.create({
  title: 'JWT認証の採用',
  context: '...',
  decision: '...',
  relatedRequirements: ['REQ-AUTH-001'],
  decider: 'Tech Lead',
});

// 知識グラフにADRエンティティを追加
await store.putEntity({
  id: `ADR-${adr.id}`,
  type: 'decision',
  name: adr.title,
  properties: { status: adr.status },
  tags: ['architecture', 'decision'],
});

// 要件との関連を記録
await store.addRelation({
  source: `ADR-${adr.id}`,
  target: 'REQ-AUTH-001',
  type: 'decides',
});

await store.save();
```

## 参照

- [ユーザーガイド](docs/MUSUBIX-v3.0-User-Guide.md)
- [ADRテンプレート](docs/adr/template.md)
