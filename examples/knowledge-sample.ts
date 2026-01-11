/**
 * @musubix/knowledge サンプルコード
 *
 * 組織の共有知識（ベストプラクティス、ガイドライン、ドメイン用語）を
 * Git-friendlyなJSONファイルで管理するサンプル
 *
 * 実行方法:
 *   npx tsx examples/knowledge-sample.ts
 */

import { createKnowledgeStore } from '@musubix/knowledge';

async function main() {
  // 1. 知識ストアの初期化
  console.log('=== 1. 知識ストアの初期化 ===');
  const store = createKnowledgeStore('.knowledge-sample');
  await store.load();
  console.log('知識ストアを初期化しました: .knowledge-sample/graph.json\n');

  // 2. ベストプラクティスの登録
  console.log('=== 2. ベストプラクティスの登録 ===');

  await store.putEntity({
    id: 'pattern:BP-CODE-001',
    type: 'best-practice',
    name: 'Entity Input DTO',
    description: 'エンティティ作成時はInput DTOオブジェクトを使用する',
    properties: {
      category: 'code',
      confidence: 0.95,
      example: `
interface CreateUserInput {
  name: string;
  email: string;
}

function createUser(input: CreateUserInput): User {
  return { id: generateId(), ...input };
}
      `.trim(),
    },
    tags: ['typescript', 'design-pattern', 'dto'],
  });
  console.log('✅ pattern:BP-CODE-001 (Entity Input DTO) を登録');

  await store.putEntity({
    id: 'pattern:BP-CODE-005',
    type: 'best-practice',
    name: 'Result Type',
    description: '失敗可能な操作にはResult<T, E>型を使用する',
    properties: {
      category: 'code',
      confidence: 0.95,
      example: `
type Result<T, E> = { ok: true; value: T } | { ok: false; error: E };

function divide(a: number, b: number): Result<number, string> {
  if (b === 0) return { ok: false, error: 'Division by zero' };
  return { ok: true, value: a / b };
}
      `.trim(),
    },
    tags: ['typescript', 'error-handling', 'functional'],
  });
  console.log('✅ pattern:BP-CODE-005 (Result Type) を登録');

  await store.putEntity({
    id: 'pattern:BP-DESIGN-001',
    type: 'best-practice',
    name: 'Status Transition Map',
    description: '有効なステータス遷移をMapで定義する',
    properties: {
      category: 'design',
      confidence: 0.95,
      example: `
const validTransitions: Record<Status, Status[]> = {
  draft: ['active', 'cancelled'],
  active: ['completed', 'cancelled'],
  completed: [],
  cancelled: [],
};
      `.trim(),
    },
    tags: ['state-machine', 'design-pattern'],
  });
  console.log('✅ pattern:BP-DESIGN-001 (Status Transition Map) を登録\n');

  // 3. セキュリティガイドラインの登録
  console.log('=== 3. セキュリティガイドラインの登録 ===');

  await store.putEntity({
    id: 'guideline:SEC-001',
    type: 'security-guideline',
    name: 'パスワードハッシュ化ガイドライン',
    description: 'パスワードは必ずbcryptでハッシュ化して保存する',
    properties: {
      priority: 'critical',
      algorithm: 'bcrypt',
      minRounds: 10,
    },
    tags: ['security', 'authentication', 'password'],
  });
  console.log('✅ guideline:SEC-001 (パスワードハッシュ化) を登録');

  await store.putEntity({
    id: 'guideline:SEC-002',
    type: 'security-guideline',
    name: 'API認証ガイドライン',
    description: 'すべてのAPIエンドポイントはJWT認証を必須とする',
    properties: {
      priority: 'critical',
      tokenType: 'JWT',
      expirationHours: 24,
    },
    tags: ['security', 'api', 'jwt'],
  });
  console.log('✅ guideline:SEC-002 (API認証) を登録\n');

  // 4. ドメイン用語の登録
  console.log('=== 4. ドメイン用語の登録 ===');

  await store.putEntity({
    id: 'domain:EC-TERM-001',
    type: 'domain-term',
    name: 'SKU',
    description: 'Stock Keeping Unit - 在庫管理単位。商品の最小管理単位を表す',
    properties: {
      domain: 'e-commerce',
      fullName: 'Stock Keeping Unit',
    },
    tags: ['e-commerce', 'inventory', 'terminology'],
  });
  console.log('✅ domain:EC-TERM-001 (SKU) を登録');

  await store.putEntity({
    id: 'domain:EC-RULE-001',
    type: 'business-rule',
    name: '在庫引当ルール',
    description: '注文確定時に在庫を引き当てる。引当できない場合は注文を保留にする',
    properties: {
      domain: 'e-commerce',
      triggerEvent: 'order_confirmed',
    },
    tags: ['e-commerce', 'inventory', 'business-rule'],
  });
  console.log('✅ domain:EC-RULE-001 (在庫引当ルール) を登録\n');

  // 5. リレーションの追加
  console.log('=== 5. リレーションの追加 ===');

  await store.addRelation({
    source: 'guideline:SEC-001',
    target: 'pattern:BP-CODE-005',
    type: 'references',
    properties: {
      description: 'セキュリティガイドラインでResult型の使用を推奨',
    },
  });
  console.log('✅ SEC-001 → BP-CODE-005 (references) を追加');

  await store.addRelation({
    source: 'domain:EC-TERM-001',
    target: 'domain:EC-RULE-001',
    type: 'usedIn',
    properties: {
      description: 'SKUは在庫引当ルールで使用される',
    },
  });
  console.log('✅ EC-TERM-001 → EC-RULE-001 (usedIn) を追加');

  await store.addRelation({
    source: 'pattern:BP-CODE-001',
    target: 'pattern:BP-CODE-005',
    type: 'relatedTo',
    properties: {
      description: 'Input DTOとResult型は組み合わせて使うことが多い',
    },
  });
  console.log('✅ BP-CODE-001 → BP-CODE-005 (relatedTo) を追加\n');

  // 6. 保存
  console.log('=== 6. 知識の保存 ===');
  await store.save();
  console.log('✅ .knowledge-sample/graph.json に保存しました\n');

  // 7. クエリ実行
  console.log('=== 7. クエリ実行 ===');

  // タイプでフィルタリング
  const patterns = await store.query({ type: 'best-practice' });
  console.log(`ベストプラクティス: ${patterns.length}件`);
  for (const p of patterns) {
    console.log(`  - ${p.id}: ${p.name}`);
  }

  // タグでフィルタリング
  const securityKnowledge = await store.query({ tags: ['security'] });
  console.log(`\nセキュリティ関連: ${securityKnowledge.length}件`);
  for (const k of securityKnowledge) {
    console.log(`  - ${k.id}: ${k.name}`);
  }

  console.log('');

  // 8. グラフ走査
  console.log('=== 8. グラフ走査 ===');
  const related = await store.traverse('guideline:SEC-001', {
    direction: 'outgoing',
    maxDepth: 2,
  });
  console.log('guideline:SEC-001 から辿れる知識:');
  for (const entity of related) {
    console.log(`  - ${entity.id}: ${entity.name}`);
  }

  console.log('\n✨ サンプル完了！');
  console.log('生成されたファイル: .knowledge-sample/graph.json');
}

main().catch(console.error);
