---
name: e2e-runner
description: |
  E2Eテスト実行スキル。Playwrightを使用してエンドツーエンドテストを
  生成・実行する。クリティカルユーザーフローの検証に使用。
  テスト結果のレポート生成とスクリーンショット管理を含む。
version: 1.0.0
license: MIT
author: MUSUBIX Team
tags:
  - testing
  - e2e
  - playwright
  - automation
triggers:
  - /e2e
  - /playwright
  - e2e test
  - end-to-end
---

# E2E Runner Skill

Playwrightを使用してエンドツーエンドテストを生成・実行するスキルです。

## 概要

このスキルは以下の機能を提供します：

1. **E2Eテスト生成** - ユーザーフローからPlaywrightテストを自動生成
2. **E2Eテスト実行** - 複数ブラウザでのテスト実行
3. **レポート生成** - テスト結果の詳細レポート

## 前提条件

```bash
# Playwrightのインストール
npm install -D @playwright/test

# ブラウザのインストール
npx playwright install
```

## コマンド

### `/e2e generate <flow>`

指定されたユーザーフローのE2Eテストを生成します。

```
/e2e generate login
/e2e generate checkout --steps "add-to-cart,payment,confirmation"
```

**オプション**:
- `--steps`: カンマ区切りのステップ名
- `--output`: 出力ディレクトリ（デフォルト: `tests/e2e/`）

### `/e2e run [flow]`

E2Eテストを実行します。

```
/e2e run                    # 全テスト実行
/e2e run login              # 特定フローのみ
/e2e run --headed           # ブラウザを表示
/e2e run --debug            # デバッグモード
```

**オプション**:
- `--headed`: ブラウザを表示して実行
- `--debug`: デバッグモードで実行
- `--trace`: トレースを記録
- `--browser`: ブラウザ指定（chromium, firefox, webkit）

### `/e2e report`

テスト結果レポートを表示します。

```
/e2e report [--open]
```

## 実行手順

### REQ-E2E-001: E2Eテスト生成

#### 1. テストファイル構造

```
tests/e2e/
├── <flow-name>.spec.ts     # テストファイル
├── fixtures/
│   └── <flow-name>.json    # テストデータ
├── pages/                  # Page Object Model
│   └── <page-name>.page.ts
└── playwright.config.ts    # 設定ファイル
```

#### 2. テストテンプレート

ユーザーフローから以下の形式でテストを生成してください：

```typescript
import { test, expect } from '@playwright/test';
import { loadFixture } from './fixtures';

test.describe('<Flow Name>', () => {
  test.beforeEach(async ({ page }) => {
    // 共通セットアップ
    await page.goto('/');
  });

  test('should complete the <flow-name> flow', async ({ page }) => {
    // Step 1: [ステップ説明]
    await page.locator('[data-testid="element"]').click();
    
    // Step 2: [ステップ説明]
    await page.fill('[name="input"]', 'value');
    
    // Step 3: [ステップ説明]
    await page.click('button[type="submit"]');
    
    // Assertion
    await expect(page.locator('.success-message')).toBeVisible();
  });

  test('should handle error case: <error-name>', async ({ page }) => {
    // エラーケースのテスト
  });
});
```

#### 3. Page Object Model (推奨)

複雑なページには Page Object を作成：

```typescript
// tests/e2e/pages/login.page.ts
import { Page, Locator } from '@playwright/test';

export class LoginPage {
  readonly page: Page;
  readonly emailInput: Locator;
  readonly passwordInput: Locator;
  readonly submitButton: Locator;

  constructor(page: Page) {
    this.page = page;
    this.emailInput = page.locator('[data-testid="email"]');
    this.passwordInput = page.locator('[data-testid="password"]');
    this.submitButton = page.locator('button[type="submit"]');
  }

  async goto() {
    await this.page.goto('/login');
  }

  async login(email: string, password: string) {
    await this.emailInput.fill(email);
    await this.passwordInput.fill(password);
    await this.submitButton.click();
  }
}
```

#### 4. フィクスチャファイル

テストデータを分離：

```json
// tests/e2e/fixtures/login.json
{
  "validUser": {
    "email": "test@example.com",
    "password": "securePassword123"
  },
  "invalidUser": {
    "email": "invalid@example.com",
    "password": "wrong"
  }
}
```

### REQ-E2E-002: E2Eテスト実行

#### 1. 基本実行

```bash
# 全テスト実行
npx playwright test

# 特定ファイル実行
npx playwright test tests/e2e/login.spec.ts

# 特定テスト実行
npx playwright test -g "should complete login"
```

#### 2. デバッグモード

```bash
# UIモードで実行（推奨）
npx playwright test --ui

# デバッガー付き実行
npx playwright test --debug

# ヘッド付き実行（ブラウザ表示）
npx playwright test --headed
```

#### 3. トレース記録

```bash
# トレース付き実行
npx playwright test --trace on

# 失敗時のみトレース
npx playwright test --trace retain-on-failure
```

#### 4. 並列実行制御

```bash
# ワーカー数指定
npx playwright test --workers 4

# シリアル実行
npx playwright test --workers 1
```

### REQ-E2E-003: レポート生成

#### 1. レポート形式

```
E2E TEST REPORT
===============

Date: [timestamp]
Duration: XX.XXs
Environment: [CI/Local]

Summary:
┌─────────────┬───────┐
│ Status      │ Count │
├─────────────┼───────┤
│ ✅ Passed   │   X   │
│ ❌ Failed   │   Y   │
│ ⏭️ Skipped  │   Z   │
│ Total       │   N   │
└─────────────┴───────┘

Browser Coverage:
- Chromium: ✅ X/Y passed
- Firefox:  ✅ X/Y passed
- WebKit:   ✅ X/Y passed

Failed Tests:
─────────────
1. [test-name]
   File: tests/e2e/login.spec.ts:42
   Error: Expected element to be visible
   
   Screenshot: playwright-report/screenshots/test-1.png
   Trace: playwright-report/traces/test-1.zip

2. [test-name]
   ...

Flaky Tests:
────────────
- [test-name]: 2/3 attempts passed

Slow Tests (>10s):
──────────────────
- [test-name]: 15.2s
- [test-name]: 12.8s
```

#### 2. HTMLレポート

```bash
# HTMLレポート生成・表示
npx playwright show-report

# カスタムレポーター
npx playwright test --reporter=html,json
```

#### 3. CI用出力

```bash
# JUnit形式（CI連携用）
npx playwright test --reporter=junit > test-results.xml

# GitHub Actions用
npx playwright test --reporter=github
```

## Playwright設定例

```typescript
// playwright.config.ts
import { defineConfig, devices } from '@playwright/test';

export default defineConfig({
  testDir: './tests/e2e',
  fullyParallel: true,
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? 2 : 0,
  workers: process.env.CI ? 1 : undefined,
  reporter: [
    ['html'],
    ['json', { outputFile: 'test-results.json' }],
  ],
  use: {
    baseURL: 'http://localhost:3000',
    trace: 'retain-on-failure',
    screenshot: 'only-on-failure',
  },
  projects: [
    {
      name: 'chromium',
      use: { ...devices['Desktop Chrome'] },
    },
    {
      name: 'firefox',
      use: { ...devices['Desktop Firefox'] },
    },
    {
      name: 'webkit',
      use: { ...devices['Desktop Safari'] },
    },
    // モバイルテスト
    {
      name: 'Mobile Chrome',
      use: { ...devices['Pixel 5'] },
    },
  ],
  webServer: {
    command: 'npm run dev',
    url: 'http://localhost:3000',
    reuseExistingServer: !process.env.CI,
  },
});
```

## よく使うテストパターン

### 認証フロー

```typescript
test('login flow', async ({ page }) => {
  await page.goto('/login');
  await page.fill('[name="email"]', 'user@example.com');
  await page.fill('[name="password"]', 'password');
  await page.click('button[type="submit"]');
  await expect(page).toHaveURL('/dashboard');
  await expect(page.locator('.user-name')).toContainText('User');
});
```

### フォーム送信

```typescript
test('form submission', async ({ page }) => {
  await page.goto('/contact');
  await page.fill('[name="name"]', 'Test User');
  await page.fill('[name="email"]', 'test@example.com');
  await page.fill('[name="message"]', 'Hello, this is a test message.');
  await page.click('button[type="submit"]');
  await expect(page.locator('.success')).toBeVisible();
});
```

### API呼び出しのモック

```typescript
test('with mocked API', async ({ page }) => {
  await page.route('**/api/users', async (route) => {
    await route.fulfill({
      status: 200,
      body: JSON.stringify([{ id: 1, name: 'Mock User' }]),
    });
  });
  
  await page.goto('/users');
  await expect(page.locator('.user-item')).toHaveCount(1);
});
```

### スクリーンショット比較

```typescript
test('visual regression', async ({ page }) => {
  await page.goto('/');
  await expect(page).toHaveScreenshot('homepage.png');
});
```

## MCPツール統合

このスキルはMUSUBIX MCPサーバーの以下のツールと連携します：

- `codegraph_analyze`: テスト対象コードの構造分析
- `sdd_validate_requirements`: 要件との整合性チェック

## ベストプラクティス

1. **セレクター戦略**: `data-testid` 属性を優先使用
2. **待機戦略**: 明示的な待機（`waitForSelector`）を使用
3. **アサーション**: 複数のアサーションで状態を確認
4. **独立性**: 各テストは独立して実行可能に
5. **クリーンアップ**: `afterEach` でテスト後の状態をリセット
6. **フレーキー対策**: リトライ設定とスクリーンショット活用

## 関連スキル

- `verification-loop`: テスト結果の検証ループへの統合
- `checkpoint`: テスト実行前のチェックポイント作成
- `codemap`: テスト対象コードの構造把握

---

**Traceability**: REQ-E2E-001, REQ-E2E-002, REQ-E2E-003
