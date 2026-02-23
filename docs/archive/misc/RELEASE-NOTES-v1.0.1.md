# Release v1.0.1

## 🚀 Sprint 6 - CLI コマンド完全実装

全22サブコマンドを実装し、AGENTS.mdおよびドキュメントの記載と完全に一致させました。

### ✨ 新機能

#### requirements コマンド
| サブコマンド | 説明 |
|-------------|------|
| `musubix requirements analyze <file>` | 自然言語からEARS要件への変換 |
| `musubix requirements validate <file>` | EARS構文検証 |
| `musubix requirements map <file>` | オントロジーマッピング |
| `musubix requirements search <query>` | 関連要件検索 |

#### design コマンド
| サブコマンド | 説明 |
|-------------|------|
| `musubix design generate <file>` | 要件から設計生成 |
| `musubix design patterns <context>` | デザインパターン検出 |
| `musubix design validate <file>` | SOLID準拠検証 |
| `musubix design c4 <file>` | C4ダイアグラム生成（Mermaid/PlantUML） |
| `musubix design adr <decision>` | ADRドキュメント生成 |

#### codegen コマンド
| サブコマンド | 説明 |
|-------------|------|
| `musubix codegen generate <file>` | 設計からコード生成 |
| `musubix codegen analyze <file>` | 静的コード解析 |
| `musubix codegen security <path>` | セキュリティスキャン（CWE対応） |

#### test コマンド
| サブコマンド | 説明 |
|-------------|------|
| `musubix test generate <file>` | テスト生成（vitest/jest/mocha/pytest対応） |
| `musubix test coverage <dir>` | カバレッジ測定・HTMLレポート |

#### trace コマンド
| サブコマンド | 説明 |
|-------------|------|
| `musubix trace matrix` | トレーサビリティマトリクス生成（HTML/CSV/Markdown） |
| `musubix trace impact <id>` | 変更影響分析 |
| `musubix trace validate` | トレーサビリティリンク検証 |

#### explain コマンド
| サブコマンド | 説明 |
|-------------|------|
| `musubix explain why <id>` | 決定理由の説明生成 |
| `musubix explain graph <id>` | 推論グラフ生成（Mermaid） |

### 📊 テスト結果

- **テストファイル**: 12ファイル
- **テスト数**: 260テスト（+27）
- **結果**: 全テスト通過 ✅

### 📦 パッケージ情報

| パッケージ | バージョン |
|-----------|-----------|
| musubix | 1.0.1 |
| @nahisaho/musubix-core | 1.0.1 |
| @nahisaho/musubix-mcp-server | 1.0.1 |
| @nahisaho/musubix-yata-client | 1.0.1 |

### 🔧 バグ修正

- TypeScript型エラー修正（未使用インポート、プロパティ名修正）

### 📄 ドキュメント更新

- CHANGELOG.md更新
- evolution-from-musubi-to-musubix.md 更新日を2026-01-03に更新
- TSK-MUSUBIX-001.md Sprint 6 成果物を完了ステータスに更新

---

## インストール

```bash
# npm
npm install musubix

# または npx で直接実行
npx musubix --help
```

## 完全なコマンドリスト

```bash
# ヘルプ
npx musubix --help
npx musubix requirements --help
npx musubix design --help
npx musubix codegen --help
npx musubix test --help
npx musubix trace --help
npx musubix explain --help
```

---

**Full Changelog**: https://github.com/nahisaho/MUSUBIX/compare/v1.0.0...v1.0.1
