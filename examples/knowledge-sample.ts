/**
 * @musubix/knowledge サンプルコード
 *
 * 組織の共有知識（ベストプラクティス、ガイドライン、ドメイン用語、開発ルール）を
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

  // ============================================
  // 2. ベストプラクティスの登録
  // ============================================
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

  // ============================================
  // 3. 会社・グループの開発ルール
  // ============================================
  console.log('=== 3. 会社・グループの開発ルール ===');

  // コーディング規約
  await store.putEntity({
    id: 'rule:CODE-STYLE-001',
    type: 'coding-standard',
    name: 'TypeScript命名規則',
    description: '変数・関数・クラスの命名規則を定義',
    properties: {
      rules: {
        variables: 'camelCase (例: userName, orderCount)',
        functions: 'camelCase (例: getUserById, calculateTotal)',
        classes: 'PascalCase (例: UserService, OrderRepository)',
        interfaces: 'PascalCase + 接頭辞なし (例: User, NOT IUser)',
        types: 'PascalCase (例: CreateUserInput, OrderStatus)',
        constants: 'UPPER_SNAKE_CASE (例: MAX_RETRY_COUNT, API_BASE_URL)',
        privateFields: '_prefix (例: _cache, _connection)',
        booleans: 'is/has/can prefix (例: isActive, hasPermission, canEdit)',
      },
      enforced: true,
      linter: 'eslint + @typescript-eslint',
    },
    tags: ['coding-standard', 'naming', 'typescript', 'mandatory'],
  });
  console.log('✅ rule:CODE-STYLE-001 (TypeScript命名規則) を登録');

  await store.putEntity({
    id: 'rule:CODE-STYLE-002',
    type: 'coding-standard',
    name: 'ファイル・ディレクトリ命名規則',
    description: 'ファイルとディレクトリの命名規則',
    properties: {
      rules: {
        sourceFiles: 'kebab-case (例: user-service.ts, order-repository.ts)',
        testFiles: '*.test.ts または *.spec.ts',
        directories: 'kebab-case (例: user-management/, order-processing/)',
        indexFiles: 'index.ts でバレルエクスポート',
      },
      exceptions: ['README.md', 'CHANGELOG.md', 'LICENSE'],
    },
    tags: ['coding-standard', 'naming', 'file-structure', 'mandatory'],
  });
  console.log('✅ rule:CODE-STYLE-002 (ファイル・ディレクトリ命名規則) を登録');

  await store.putEntity({
    id: 'rule:CODE-STYLE-003',
    type: 'coding-standard',
    name: 'コードフォーマット規約',
    description: 'Prettier設定に基づくコードフォーマット',
    properties: {
      prettier: {
        semi: true,
        singleQuote: true,
        tabWidth: 2,
        trailingComma: 'es5',
        printWidth: 100,
        bracketSpacing: true,
      },
      enforced: true,
      preCommitHook: true,
    },
    tags: ['coding-standard', 'formatting', 'prettier', 'mandatory'],
  });
  console.log('✅ rule:CODE-STYLE-003 (コードフォーマット規約) を登録');

  // Gitブランチ戦略
  await store.putEntity({
    id: 'rule:GIT-001',
    type: 'git-workflow',
    name: 'ブランチ戦略',
    description: 'Git-flowベースのブランチ管理ルール',
    properties: {
      mainBranch: 'main',
      developBranch: 'develop',
      featureBranches: {
        prefix: 'feature/',
        naming: 'feature/{issue-number}-{short-description}',
        example: 'feature/123-user-authentication',
      },
      bugfixBranches: {
        prefix: 'bugfix/',
        naming: 'bugfix/{issue-number}-{short-description}',
        example: 'bugfix/456-login-redirect-error',
      },
      hotfixBranches: {
        prefix: 'hotfix/',
        naming: 'hotfix/{version}-{short-description}',
        example: 'hotfix/1.2.1-security-patch',
      },
      releaseBranches: {
        prefix: 'release/',
        naming: 'release/{version}',
        example: 'release/1.3.0',
      },
      protectedBranches: ['main', 'develop'],
      requiredReviews: 2,
    },
    tags: ['git', 'workflow', 'branching', 'mandatory'],
  });
  console.log('✅ rule:GIT-001 (ブランチ戦略) を登録');

  await store.putEntity({
    id: 'rule:GIT-002',
    type: 'git-workflow',
    name: 'コミットメッセージ規約',
    description: 'Conventional Commitsに基づくコミットメッセージ形式',
    properties: {
      format: '<type>(<scope>): <subject>',
      types: {
        feat: '新機能の追加',
        fix: 'バグ修正',
        docs: 'ドキュメントのみの変更',
        style: 'コードの意味に影響しない変更（空白、フォーマット等）',
        refactor: 'バグ修正や機能追加を伴わないコード変更',
        perf: 'パフォーマンス改善',
        test: 'テストの追加・修正',
        chore: 'ビルドプロセスやツールの変更',
        ci: 'CI設定の変更',
        revert: '以前のコミットの取り消し',
      },
      examples: [
        'feat(auth): add JWT refresh token support',
        'fix(api): resolve null pointer in user endpoint',
        'docs(readme): update installation instructions',
        'refactor(order): extract validation logic to separate module',
      ],
      enforced: true,
      hook: 'commitlint',
    },
    tags: ['git', 'commit', 'conventional-commits', 'mandatory'],
  });
  console.log('✅ rule:GIT-002 (コミットメッセージ規約) を登録');

  // コードレビュー
  await store.putEntity({
    id: 'rule:REVIEW-001',
    type: 'code-review',
    name: 'コードレビューガイドライン',
    description: 'プルリクエストのレビュー基準と手順',
    properties: {
      checklist: [
        '機能要件を満たしているか',
        'テストが十分に書かれているか',
        'コーディング規約に準拠しているか',
        'セキュリティ上の問題がないか',
        'パフォーマンスに影響がないか',
        'ドキュメントが更新されているか',
        'エラーハンドリングが適切か',
        '命名が明確で一貫しているか',
      ],
      responseTime: {
        target: '24時間以内',
        priority: 'hotfixは4時間以内',
      },
      approvalRequired: 2,
      selfReview: 'PRを出す前に必ずセルフレビューを行う',
    },
    tags: ['code-review', 'pr', 'quality', 'mandatory'],
  });
  console.log('✅ rule:REVIEW-001 (コードレビューガイドライン) を登録');

  // テスト方針
  await store.putEntity({
    id: 'rule:TEST-001',
    type: 'testing-policy',
    name: 'テスト戦略',
    description: 'プロジェクトのテスト方針と基準',
    properties: {
      coverage: {
        minimum: 80,
        target: 90,
        critical: 100, // 決済・認証などのクリティカルパス
      },
      testTypes: {
        unit: {
          framework: 'Vitest',
          location: '*.test.ts (同一ディレクトリ)',
          required: true,
        },
        integration: {
          framework: 'Vitest',
          location: '__tests__/integration/',
          required: true,
        },
        e2e: {
          framework: 'Playwright',
          location: 'e2e/',
          required: 'リリース前',
        },
      },
      naming: {
        describe: 'テスト対象のクラス/関数名',
        it: '動詞で始める (should, returns, throws, etc.)',
        example: "describe('UserService') → it('should create user with valid input')",
      },
      principles: [
        'Arrange-Act-Assert (AAA) パターンを使用',
        'テストは独立して実行可能であること',
        'モックは最小限に抑える',
        'テスト名で何をテストしているか明確にする',
      ],
    },
    tags: ['testing', 'quality', 'vitest', 'mandatory'],
  });
  console.log('✅ rule:TEST-001 (テスト戦略) を登録');

  // ドキュメント規約
  await store.putEntity({
    id: 'rule:DOC-001',
    type: 'documentation',
    name: 'ドキュメント規約',
    description: 'コードとプロジェクトのドキュメント基準',
    properties: {
      codeComments: {
        publicAPI: 'JSDoc形式で必須',
        complexLogic: '処理の意図をコメントで説明',
        avoidObvious: '自明なコードにはコメント不要',
      },
      projectDocs: {
        readme: '各パッケージにREADME.mdを配置',
        adr: 'アーキテクチャ決定はADRで記録',
        changelog: 'CHANGELOG.mdを更新',
        api: 'OpenAPI/Swagger形式でAPI仕様を文書化',
      },
      language: {
        internal: '日本語',
        publicAPI: '英語',
        codeComments: '英語推奨',
      },
    },
    tags: ['documentation', 'jsdoc', 'adr', 'mandatory'],
  });
  console.log('✅ rule:DOC-001 (ドキュメント規約) を登録');

  // エラーハンドリング
  await store.putEntity({
    id: 'rule:ERROR-001',
    type: 'coding-standard',
    name: 'エラーハンドリング規約',
    description: 'エラー処理の標準パターン',
    properties: {
      principles: [
        '例外は回復可能な場合のみcatchする',
        '予期されるエラーはResult型で表現',
        'ログレベルを適切に使い分ける',
        'ユーザー向けエラーと開発者向けエラーを分離',
      ],
      logLevels: {
        error: '回復不能なエラー、即座の対応が必要',
        warn: '潜在的な問題、注意が必要',
        info: '重要なビジネスイベント',
        debug: '開発時のデバッグ情報',
      },
      customErrors: {
        baseClass: 'AppError extends Error',
        properties: ['code', 'message', 'statusCode', 'context'],
        example: "throw new ValidationError('Invalid email format', { field: 'email' })",
      },
    },
    tags: ['error-handling', 'logging', 'coding-standard', 'mandatory'],
  });
  console.log('✅ rule:ERROR-001 (エラーハンドリング規約) を登録');

  // 依存関係管理
  await store.putEntity({
    id: 'rule:DEP-001',
    type: 'dependency-management',
    name: '依存関係管理ポリシー',
    description: 'パッケージ依存関係の管理ルール',
    properties: {
      addingDependencies: [
        'セキュリティ脆弱性がないか確認 (npm audit)',
        'メンテナンス状況を確認 (最終更新日、Issue対応状況)',
        'ライセンスがMIT/Apache2.0互換か確認',
        'バンドルサイズへの影響を確認',
        'チームに事前相談（重要な依存の場合）',
      ],
      versionPolicy: {
        production: '^x.y.z (マイナーバージョンまで自動更新)',
        devDependencies: '^x.y.z',
        peerDependencies: '>=x.y.z',
      },
      lockFile: {
        packageLock: '必ずコミットする',
        update: '週次でdependabot PRをレビュー',
      },
      prohibited: [
        'moment.js → day.js または date-fns を使用',
        'lodash (全体) → lodash-es または個別関数',
        'request → node-fetch または axios',
      ],
    },
    tags: ['dependencies', 'npm', 'security', 'mandatory'],
  });
  console.log('✅ rule:DEP-001 (依存関係管理ポリシー) を登録\n');

  // ============================================
  // 4. セキュリティガイドライン
  // ============================================
  console.log('=== 4. セキュリティガイドラインの登録 ===');

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
      refreshToken: true,
    },
    tags: ['security', 'api', 'jwt'],
  });
  console.log('✅ guideline:SEC-002 (API認証) を登録');

  await store.putEntity({
    id: 'guideline:SEC-003',
    type: 'security-guideline',
    name: '機密情報管理ガイドライン',
    description: 'APIキー、パスワード等の機密情報の管理ルール',
    properties: {
      priority: 'critical',
      rules: [
        'シークレットをコードにハードコードしない',
        '環境変数または Secret Manager を使用',
        '.envファイルは.gitignoreに追加',
        'ログに機密情報を出力しない',
        '本番環境のシークレットは定期的にローテーション',
      ],
      tools: {
        local: '.env + dotenv',
        staging: 'AWS Secrets Manager / Azure Key Vault',
        production: 'AWS Secrets Manager / Azure Key Vault',
      },
    },
    tags: ['security', 'secrets', 'environment', 'critical'],
  });
  console.log('✅ guideline:SEC-003 (機密情報管理) を登録');

  await store.putEntity({
    id: 'guideline:SEC-004',
    type: 'security-guideline',
    name: '入力検証ガイドライン',
    description: 'すべての外部入力は検証・サニタイズを行う',
    properties: {
      priority: 'critical',
      validation: {
        library: 'zod',
        timing: 'APIの入口で即座に検証',
        principle: 'ホワイトリスト方式（許可された形式のみ受け入れ）',
      },
      sanitization: [
        'SQLインジェクション対策 (プリペアドステートメント使用)',
        'XSS対策 (HTMLエスケープ)',
        'パストラバーサル対策 (パス検証)',
      ],
      example: `
const UserInputSchema = z.object({
  name: z.string().min(1).max(100),
  email: z.string().email(),
  age: z.number().int().min(0).max(150),
});
      `.trim(),
    },
    tags: ['security', 'validation', 'zod', 'critical'],
  });
  console.log('✅ guideline:SEC-004 (入力検証) を登録\n');

  // ============================================
  // 5. ドメイン用語・ビジネスルール
  // ============================================
  console.log('=== 5. ドメイン用語・ビジネスルールの登録 ===');

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

  // ============================================
  // 6. アーキテクチャ決定
  // ============================================
  console.log('=== 6. アーキテクチャ決定の登録 ===');

  await store.putEntity({
    id: 'arch:ADR-001',
    type: 'architecture-decision',
    name: 'モノレポ採用',
    description: 'npm workspacesを使用したモノレポ構成を採用',
    properties: {
      status: 'accepted',
      date: '2025-01-01',
      context:
        '複数のパッケージ間で共通コードを共有し、一貫したバージョン管理を行いたい',
      decision: 'npm workspacesによるモノレポ構成を採用',
      consequences: {
        positive: [
          'パッケージ間の依存関係が明確になる',
          '共通コードの再利用が容易',
          'CI/CDの一元管理',
          'コードレビューが一箇所で完結',
        ],
        negative: [
          'リポジトリサイズが大きくなる',
          'ビルド時間が長くなる可能性',
          '個別パッケージのリリースが複雑',
        ],
      },
      alternatives: ['マルチレポ', 'Lerna', 'Nx', 'Turborepo'],
    },
    tags: ['architecture', 'monorepo', 'npm-workspaces'],
  });
  console.log('✅ arch:ADR-001 (モノレポ採用) を登録');

  await store.putEntity({
    id: 'arch:ADR-002',
    type: 'architecture-decision',
    name: 'TypeScript strict mode必須化',
    description: 'すべてのプロジェクトでTypeScript strict modeを有効にする',
    properties: {
      status: 'accepted',
      date: '2025-01-01',
      context: '型安全性を最大限に活かし、実行時エラーを減らしたい',
      decision: 'tsconfig.jsonでstrict: trueを必須とする',
      consequences: {
        positive: [
          'コンパイル時にバグを検出',
          'リファクタリングが安全に行える',
          'コードの意図が明確になる',
        ],
        negative: [
          '初期学習コストが高い',
          'サードパーティライブラリの型定義が不完全な場合がある',
        ],
      },
      tsconfig: {
        strict: true,
        noImplicitAny: true,
        strictNullChecks: true,
        strictFunctionTypes: true,
        noImplicitThis: true,
        alwaysStrict: true,
      },
    },
    tags: ['architecture', 'typescript', 'type-safety'],
  });
  console.log('✅ arch:ADR-002 (TypeScript strict mode必須化) を登録');

  await store.putEntity({
    id: 'arch:ADR-003',
    type: 'architecture-decision',
    name: 'レイヤードアーキテクチャ採用',
    description: 'ドメイン駆動設計に基づくレイヤードアーキテクチャを採用',
    properties: {
      status: 'accepted',
      date: '2025-02-01',
      context: 'ビジネスロジックとインフラストラクチャを分離し、テスト容易性を高めたい',
      decision: 'Domain / Application / Infrastructure の3層構造を採用',
      layers: {
        domain: {
          description: 'ビジネスロジック、エンティティ、値オブジェクト',
          dependencies: 'なし（純粋なビジネスロジック）',
        },
        application: {
          description: 'ユースケース、サービス、DTOs',
          dependencies: 'Domain層のみ',
        },
        infrastructure: {
          description: 'DB、外部API、フレームワーク',
          dependencies: 'Domain層、Application層',
        },
      },
      directoryStructure: `
src/
├── domain/           # エンティティ、値オブジェクト、リポジトリIF
├── application/      # ユースケース、サービス
├── infrastructure/   # DB実装、外部API
└── presentation/     # Controllers, CLI
      `.trim(),
    },
    tags: ['architecture', 'ddd', 'layered-architecture'],
  });
  console.log('✅ arch:ADR-003 (レイヤードアーキテクチャ採用) を登録\n');

  // ============================================
  // 7. リレーションの追加
  // ============================================
  console.log('=== 7. リレーションの追加 ===');

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
    source: 'guideline:SEC-004',
    target: 'rule:ERROR-001',
    type: 'relatedTo',
    properties: {
      description: '入力検証とエラーハンドリングは密接に関連',
    },
  });
  console.log('✅ SEC-004 → ERROR-001 (relatedTo) を追加');

  await store.addRelation({
    source: 'rule:CODE-STYLE-001',
    target: 'rule:CODE-STYLE-002',
    type: 'relatedTo',
    properties: {
      description: '命名規則は一貫性を保つために関連',
    },
  });
  console.log('✅ CODE-STYLE-001 → CODE-STYLE-002 (relatedTo) を追加');

  await store.addRelation({
    source: 'rule:GIT-002',
    target: 'rule:DOC-001',
    type: 'relatedTo',
    properties: {
      description: 'コミットメッセージとドキュメントの一貫性',
    },
  });
  console.log('✅ GIT-002 → DOC-001 (relatedTo) を追加');

  await store.addRelation({
    source: 'arch:ADR-003',
    target: 'pattern:BP-DESIGN-001',
    type: 'references',
    properties: {
      description: 'レイヤードアーキテクチャでStatus Transition Mapを活用',
    },
  });
  console.log('✅ ADR-003 → BP-DESIGN-001 (references) を追加');

  await store.addRelation({
    source: 'rule:TEST-001',
    target: 'pattern:BP-CODE-005',
    type: 'references',
    properties: {
      description: 'テストでResult型のテストパターンを適用',
    },
  });
  console.log('✅ TEST-001 → BP-CODE-005 (references) を追加');

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

  // ============================================
  // 8. 保存
  // ============================================
  console.log('=== 8. 知識の保存 ===');
  await store.save();
  console.log('✅ .knowledge-sample/graph.json に保存しました\n');

  // ============================================
  // 9. クエリ実行
  // ============================================
  console.log('=== 9. クエリ実行 ===');

  // タイプでフィルタリング
  const patterns = await store.query({ type: 'best-practice' });
  console.log(`ベストプラクティス: ${patterns.length}件`);
  for (const p of patterns) {
    console.log(`  - ${p.id}: ${p.name}`);
  }

  const codingStandards = await store.query({ type: 'coding-standard' });
  console.log(`\nコーディング規約: ${codingStandards.length}件`);
  for (const c of codingStandards) {
    console.log(`  - ${c.id}: ${c.name}`);
  }

  const architectureDecisions = await store.query({ type: 'architecture-decision' });
  console.log(`\nアーキテクチャ決定: ${architectureDecisions.length}件`);
  for (const a of architectureDecisions) {
    console.log(`  - ${a.id}: ${a.name}`);
  }

  // タグでフィルタリング
  const mandatoryRules = await store.query({ tags: ['mandatory'] });
  console.log(`\n必須ルール (mandatory): ${mandatoryRules.length}件`);
  for (const r of mandatoryRules) {
    console.log(`  - ${r.id}: ${r.name}`);
  }

  const securityKnowledge = await store.query({ tags: ['security'] });
  console.log(`\nセキュリティ関連: ${securityKnowledge.length}件`);
  for (const k of securityKnowledge) {
    console.log(`  - ${k.id}: ${k.name}`);
  }

  console.log('');

  // ============================================
  // 10. グラフ走査
  // ============================================
  console.log('=== 10. グラフ走査 ===');
  const related = await store.traverse('guideline:SEC-004', {
    direction: 'outgoing',
    maxDepth: 2,
  });
  console.log('guideline:SEC-004 (入力検証) から辿れる知識:');
  for (const entity of related) {
    console.log(`  - ${entity.id}: ${entity.name}`);
  }

  const archRelated = await store.traverse('arch:ADR-003', {
    direction: 'outgoing',
    maxDepth: 2,
  });
  console.log('\narch:ADR-003 (レイヤードアーキテクチャ) から辿れる知識:');
  for (const entity of archRelated) {
    console.log(`  - ${entity.id}: ${entity.name}`);
  }

  console.log('\n✨ サンプル完了！');
  console.log('生成されたファイル: .knowledge-sample/graph.json');
  console.log('\n📊 登録した知識の統計:');
  const allEntities = await store.query({});
  const typeCount: Record<string, number> = {};
  for (const e of allEntities) {
    typeCount[e.type] = (typeCount[e.type] || 0) + 1;
  }
  for (const [type, count] of Object.entries(typeCount).sort((a, b) => b[1] - a[1])) {
    console.log(`  ${type}: ${count}件`);
  }
}

main().catch(console.error);
