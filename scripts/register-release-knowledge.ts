/**
 * Register release procedure knowledge to @musubix/knowledge
 */
import { createKnowledgeStore, type Entity, type Relation } from '@musubix/knowledge';

async function main() {
  const store = createKnowledgeStore('.knowledge');
  await store.load();

  const now = new Date().toISOString();

  // Knowledge: Release Procedure
  const releaseEntity: Entity = {
    id: 'PROC-RELEASE-001',
    type: 'pattern',
    name: 'バージョンリリース手順',
    description: '新しいバージョンの開発終了後のリリース手順。npm install musubixでインストール可能にするための標準プロセス。',
    properties: {
      category: 'release-procedure',
      steps: [
        {
          order: 1,
          name: 'リリース準備',
          description: 'CHANGELOG.mdの更新、READMEの確認、バージョン番号の更新',
          commands: [
            'npm version patch/minor/major',
          ],
        },
        {
          order: 2,
          name: 'pnpm互換性チェック',
          description: 'workspace:* などpnpm独自のプロトコルが残っていないか確認',
          commands: [
            'grep -r "workspace:" packages/*/package.json',
          ],
          note: 'workspace:*はnpmでサポートされないため、実バージョン（^x.y.z）に置換必須',
        },
        {
          order: 3,
          name: 'Gitコミット',
          description: '変更をコミット',
          commands: [
            'git add .',
            'git commit -m "chore: release vX.Y.Z"',
            'git tag vX.Y.Z',
          ],
        },
        {
          order: 4,
          name: 'GitHubプッシュ',
          description: 'コミットとタグをoriginにプッシュ',
          commands: [
            'git push origin main --tags',
          ],
        },
        {
          order: 5,
          name: 'npm publish',
          description: 'npmレジストリに公開',
          commands: [
            'npm publish --access public',
          ],
        },
      ],
      warnings: [
        'workspace:*を使用しているとnpm installで"EUNSUPPORTEDPROTOCOL"エラーが発生する',
        'タグをプッシュし忘れるとバージョン追跡ができなくなる',
      ],
      learnedFrom: 'v3.4.7リリース時の問題対応（2026-01-18）',
    },
    tags: ['release', 'npm', 'pnpm', 'workspace', 'procedure', 'best-practice'],
    createdAt: now,
    updatedAt: now,
  };

  // Knowledge: pnpm workspace:* issue
  const workspaceIssueEntity: Entity = {
    id: 'ISSUE-PNPM-001',
    type: 'constraint',
    name: 'pnpm workspace:* プロトコル非互換性',
    description: 'pnpmのworkspace:*プロトコルはnpmでサポートされていない。npm publishする前に実バージョンに置換が必要。',
    properties: {
      symptom: 'npm install時に"EUNSUPPORTEDPROTOCOL: Unsupported URL Type workspace:"エラー',
      cause: 'package.jsonにworkspace:*が残っている',
      solution: 'workspace:*を^X.Y.Z形式の実バージョンに置換',
      example: {
        before: '"@nahisaho/musubix-core": "workspace:*"',
        after: '"@nahisaho/musubix-core": "^3.4.6"',
      },
      affectedVersion: 'v3.4.5, v3.4.6',
      fixedVersion: 'v3.4.7',
    },
    tags: ['pnpm', 'npm', 'workspace', 'error', 'compatibility'],
    createdAt: now,
    updatedAt: now,
  };

  // Register entities
  await store.putEntity(releaseEntity);
  console.log(`✅ Registered: ${releaseEntity.id} - ${releaseEntity.name}`);

  await store.putEntity(workspaceIssueEntity);
  console.log(`✅ Registered: ${workspaceIssueEntity.id} - ${workspaceIssueEntity.name}`);

  // Add relation
  const relation: Relation = {
    id: 'REL-PROC-ISSUE-001',
    source: 'PROC-RELEASE-001',
    target: 'ISSUE-PNPM-001',
    type: 'related_to',
    properties: {
      reason: 'リリース手順のstep2でチェックすべき問題',
    },
  };
  await store.addRelation(relation);
  console.log(`✅ Registered relation: ${relation.source} --[${relation.type}]--> ${relation.target}`);

  // Save
  await store.save();
  console.log('\n📦 Knowledge saved to .knowledge/graph.json');

  // Show stats
  const stats = store.getStats();
  console.log(`\n📊 Stats: ${stats.entityCount} entities, ${stats.relationCount} relations`);
}

main().catch(console.error);
