# MUSUBIX Decisions パッケージ

**パッケージ名**: `@musubix/decisions`  
**バージョン**: 3.0.1  
**最終更新**: 2026-01-12

---

## 1. 概要

`@musubix/decisions` は、MUSUBIX v3.0で導入されたArchitecture Decision Records（ADR）管理システムです。アーキテクチャ決定を構造化されたMarkdownファイルで記録・追跡し、チーム間の知識共有と意思決定の透明性を実現します。

### 1.1 特徴

| 特徴 | 説明 |
|------|------|
| **Markdown形式** | 人間が読みやすく、Gitでdiff可能 |
| **ライフサイクル管理** | proposed → accepted → deprecated/superseded |
| **要件との紐付け** | REQ-* IDとの関連付けをサポート |
| **検索・フィルタ** | キーワード検索、ステータスフィルタ |
| **インデックス生成** | ADR一覧の自動生成 |

### 1.2 ADRステータス

```
proposed → accepted → deprecated
              ↓
          superseded (by newer ADR)
```

| ステータス | 説明 |
|-----------|------|
| `proposed` | 提案中（レビュー待ち） |
| `accepted` | 承認済み（適用中） |
| `deprecated` | 非推奨（使用しない） |
| `superseded` | 置き換え済み（新ADRあり） |

### 1.3 ストレージ構造

```
docs/decisions/
├── ADR-0001-jwt-authentication.md
├── ADR-0002-monorepo-structure.md
├── ADR-0003-testing-strategy.md
└── index.md  # 自動生成
```

---

## 2. インストール

```bash
# 単体インストール
npm install @musubix/decisions

# または musubix パッケージ経由
npm install musubix
```

---

## 3. 基本的な使い方

### 3.1 Decision Managerの初期化

```typescript
import { createDecisionManager } from '@musubix/decisions';

// docs/decisions/ にADRを保存
const manager = createDecisionManager('docs/decisions');
```

### 3.2 ADRの作成

```typescript
const adr = await manager.create({
  title: 'JWT認証の採用',
  context: `
ユーザー認証の仕組みが必要。
セッション管理のオーバーヘッドを避けたい。
マイクロサービス間での認証情報共有が必要。
  `,
  decision: 'JWTトークンベースの認証を採用する。',
  rationale: `
- ステートレスでスケーラブル
- マイクロサービス間でも利用可能
- 業界標準で豊富なライブラリがある
  `,
  alternatives: [
    'セッションベース認証',
    'OAuth2のみ',
    'API Key認証',
  ],
  consequences: [
    'トークン失効の仕組みが必要',
    'トークンサイズに注意（ペイロードが大きくなりがち）',
    'セキュアな署名鍵管理が必要',
  ],
  relatedRequirements: ['REQ-AUTH-001', 'REQ-SEC-002'],
  decider: 'Tech Lead',
});

console.log(`ADR-${adr.id} created: ${adr.title}`);
// => ADR-0001 created: JWT認証の採用
```

### 3.3 生成されるMarkdownファイル

```markdown
# ADR-0001: JWT認証の採用

## Status

proposed

## Context

ユーザー認証の仕組みが必要。
セッション管理のオーバーヘッドを避けたい。
マイクロサービス間での認証情報共有が必要。

## Decision

JWTトークンベースの認証を採用する。

## Rationale

- ステートレスでスケーラブル
- マイクロサービス間でも利用可能
- 業界標準で豊富なライブラリがある

## Alternatives Considered

1. セッションベース認証
2. OAuth2のみ
3. API Key認証

## Consequences

- トークン失効の仕組みが必要
- トークンサイズに注意（ペイロードが大きくなりがち）
- セキュアな署名鍵管理が必要

## Related Requirements

- REQ-AUTH-001
- REQ-SEC-002

## Metadata

- **Decider**: Tech Lead
- **Date**: 2026-01-12
```

---

## 4. ADRの取得

### 4.1 IDで取得

```typescript
const adr = await manager.get('0001');

if (adr) {
  console.log(adr.title);     // => 'JWT認証の採用'
  console.log(adr.status);    // => 'proposed'
  console.log(adr.decision);  // => 'JWTトークンベースの認証を採用する。'
}
```

### 4.2 一覧取得

```typescript
// 全ADR
const all = await manager.list();

// ステータスでフィルタ
const accepted = await manager.list({ status: 'accepted' });
const proposed = await manager.list({ status: 'proposed' });

// キーワード検索
const authRelated = await manager.list({ keyword: '認証' });
```

---

## 5. ADRの状態遷移

### 5.1 承認（Accept）

```typescript
const adr = await manager.accept('0001');
console.log(adr.status); // => 'accepted'
```

### 5.2 非推奨化（Deprecate）

```typescript
// 単純な非推奨
await manager.deprecate('0001');

// 理由を記録
await manager.deprecate('0001', {
  reason: 'セキュリティ要件の変更により不採用',
});
```

### 5.3 置き換え（Supersede）

```typescript
// 新しいADRで置き換え
await manager.supersede('0001', '0005');

// 0001のステータスは 'superseded' になり、
// supersededBy: '0005' が記録される
```

---

## 6. ADR検索

### 6.1 キーワード検索

```typescript
const results = await manager.search('認証');

for (const adr of results) {
  console.log(`ADR-${adr.id}: ${adr.title}`);
}
```

### 6.2 要件からADR検索

```typescript
// 特定の要件に関連するADRを検索
const relatedADRs = await manager.findByRequirement('REQ-AUTH-001');

console.log(`REQ-AUTH-001 に関連するADR: ${relatedADRs.length}件`);
```

---

## 7. インデックス生成

```typescript
// docs/decisions/index.md を自動生成
await manager.generateIndex();
```

生成される `index.md`:

```markdown
# Architecture Decision Records

| ID | Title | Status | Date |
|----|-------|--------|------|
| [ADR-0001](./ADR-0001-jwt-authentication.md) | JWT認証の採用 | accepted | 2026-01-12 |
| [ADR-0002](./ADR-0002-monorepo-structure.md) | モノレポ構造の採用 | accepted | 2026-01-12 |
| [ADR-0003](./ADR-0003-testing-strategy.md) | テスト戦略 | proposed | 2026-01-12 |

## By Status

### Accepted (2)
- [ADR-0001](./ADR-0001-jwt-authentication.md): JWT認証の採用
- [ADR-0002](./ADR-0002-monorepo-structure.md): モノレポ構造の採用

### Proposed (1)
- [ADR-0003](./ADR-0003-testing-strategy.md): テスト戦略
```

---

## 8. ADRの更新と削除

### 8.1 更新

```typescript
const updated = await manager.update('0001', {
  consequences: [
    ...existingConsequences,
    'リフレッシュトークンの導入が必要になった',
  ],
});
```

### 8.2 削除

```typescript
// ⚠️ 通常は deprecate/supersede を使用
const deleted = await manager.delete('0003');
console.log(deleted); // => true
```

---

## 9. API リファレンス

### 9.1 DecisionManager インターフェース

```typescript
interface DecisionManager {
  // CRUD
  create(input: ADRInput): Promise<ADR>;
  get(id: string): Promise<ADR | null>;
  list(filter?: ADRFilter): Promise<ADR[]>;
  update(id: string, updates: Partial<ADRInput>): Promise<ADR>;
  delete(id: string): Promise<boolean>;
  
  // ステータス遷移
  accept(id: string): Promise<ADR>;
  deprecate(id: string, options?: DeprecateOptions): Promise<ADR>;
  supersede(oldId: string, newId: string): Promise<ADR>;
  
  // 検索
  search(keyword: string): Promise<ADR[]>;
  findByRequirement(requirementId: string): Promise<ADR[]>;
  
  // インデックス
  generateIndex(): Promise<void>;
}
```

### 9.2 ADR インターフェース

```typescript
interface ADR {
  id: string;              // 例: '0001'
  title: string;           // 決定タイトル
  status: ADRStatus;       // 'proposed' | 'accepted' | 'deprecated' | 'superseded'
  context: string;         // 背景・問題
  decision: string;        // 決定内容
  rationale: string;       // 理由・根拠
  alternatives: string[];  // 検討した代替案
  consequences: string[];  // 結果・影響
  relatedRequirements?: string[];  // 関連要件ID
  decider?: string;        // 決定者
  date: string;            // 作成日
  supersededBy?: string;   // 置き換え先ADR ID
}
```

### 9.3 ADRInput インターフェース

```typescript
interface ADRInput {
  title: string;
  context: string;
  decision: string;
  rationale: string;
  alternatives?: string[];
  consequences?: string[];
  relatedRequirements?: string[];
  decider?: string;
}
```

---

## 10. ユースケース

### 10.1 技術選定の記録

```typescript
const techDecision = await manager.create({
  title: 'フロントエンドフレームワークの選定',
  context: `
新規Webアプリケーションの開発において、
フロントエンドフレームワークを選定する必要がある。
チームのスキルセットとプロジェクト要件を考慮。
  `,
  decision: 'React + TypeScriptを採用する。',
  rationale: `
- チームの大半がReact経験者
- 豊富なエコシステムとコミュニティサポート
- TypeScriptとの親和性が高い
  `,
  alternatives: [
    'Vue.js',
    'Angular',
    'Svelte',
  ],
  consequences: [
    'React 18の新機能（Concurrent Mode等）の学習が必要',
    '状態管理ライブラリの選定が別途必要',
  ],
  relatedRequirements: ['REQ-UI-001'],
  decider: 'Frontend Lead',
});
```

### 10.2 アーキテクチャ変更の記録

```typescript
const archDecision = await manager.create({
  title: 'マイクロサービスへの移行',
  context: `
モノリシックアーキテクチャの限界に直面。
スケーラビリティとデプロイ頻度の向上が必要。
  `,
  decision: 'ドメイン駆動設計に基づくマイクロサービス化を段階的に進める。',
  rationale: `
- 各サービスの独立したスケーリング
- チーム間の独立性向上
- 技術スタックの柔軟性
  `,
  alternatives: [
    'モノリスの最適化継続',
    'サーバーレス完全移行',
  ],
  consequences: [
    '運用複雑性の増加',
    '分散トレーシングの導入が必要',
    'サービス間通信の設計が重要',
  ],
  relatedRequirements: ['REQ-SCALE-001', 'REQ-ARCH-002'],
  decider: 'CTO',
});
```

### 10.3 ADR駆動の開発フロー

```typescript
// 1. 新機能の設計時にADRを作成
const adr = await manager.create({
  title: 'キャッシュ戦略',
  // ...
});

// 2. チームレビュー後に承認
await manager.accept(adr.id);

// 3. 要件変更時に新ADRで置き換え
const newAdr = await manager.create({
  title: 'Redis分散キャッシュの導入',
  // ...
});
await manager.supersede(adr.id, newAdr.id);

// 4. インデックス更新
await manager.generateIndex();
```

---

## 11. ベストプラクティス

### 11.1 ADRを書くタイミング

- 重要な技術選定時
- アーキテクチャの変更時
- 標準・規約の制定時
- トレードオフのある決定時

### 11.2 ADRに含めるべき情報

- **十分なコンテキスト**: 後から読む人が背景を理解できるように
- **明確な決定**: 曖昧さを排除
- **検討した代替案**: なぜ他の選択肢を選ばなかったか
- **予想される影響**: 良い面も悪い面も

### 11.3 ADRのライフサイクル管理

```typescript
// ❌ 悪い例: ADRを削除
await manager.delete('0001');

// ✅ 良い例: 非推奨または置き換え
await manager.deprecate('0001', { 
  reason: '要件変更により不採用' 
});

// または
await manager.supersede('0001', '0005');
```

---

## 12. 関連パッケージ

| パッケージ | 説明 |
|------------|------|
| `@musubix/knowledge` | Git-Native知識グラフシステム |
| `@musubix/policy` | 9憲法条項に基づくポリシー検証 |
| `musubix` | 3パッケージを含むメインパッケージ |

---

## 13. 参照

- [MUSUBIX v3.0 User Guide](../MUSUBIX-v3.0-User-Guide.md)
- [ADR GitHub Organization](https://adr.github.io/)
- [Michael Nygard's Original ADR Post](https://cognitect.com/blog/2011/11/15/documenting-architecture-decisions)
- [GitHub Repository](https://github.com/nahisaho/MUSUBIX)
- [npm Package](https://www.npmjs.com/package/@musubix/decisions)
