# MUSUBIX - Fork リポジトリ

> このリポジトリは、[nahisaho/MUSUBIX](https://github.com/nahisaho/MUSUBIX) の**フォーク**です。本家プロジェクトへの貢献を目的としています。

**[English README](README.md)**

---

## このフォークについて

このフォークは、本家 [MUSUBIX](https://github.com/nahisaho/MUSUBIX) プロジェクトに対して、バグ修正・新機能・ドキュメント改善などを貢献するとともに、個人利用の独自拡張を開発するために存在しています。

**プロジェクトの完全なドキュメントは本家リポジトリをご覧ください：**
**https://github.com/nahisaho/MUSUBIX**

---

## 謝辞

MUSUBIX は [nahisaho](https://github.com/nahisaho) 氏によって開発・メンテナンスされています。この優れたニューロシンボリックAI統合システムをオープンソースとして公開してくださっていることに感謝いたします。

---

## ブランチ構成

| ブランチ | 目的 |
|---------|------|
| [`main`](https://github.com/Takashi-So/MUSUBIX/tree/main) | 本家の `main` のミラー（常に同期） |
| [`develop`](https://github.com/Takashi-So/MUSUBIX/tree/develop) | 個人利用の統合ブランチ（本家 + 独自改善） |
| `contrib/*` | 本家へのPR用の貢献ブランチ（一時的） |
| `feature/*` | 独自機能の作業ブランチ（`develop` へ統合） |
| `fork-home` | このブランチ — フォーク情報の表示用（デフォルトブランチ） |

---

## ワークフロー

### 貢献（本家へのPR）

1. `main` を本家と常に同期
2. `main` から貢献用ブランチ（`contrib/*`）を作成
3. [nahisaho/MUSUBIX](https://github.com/nahisaho/MUSUBIX) にプルリクエストを送信
4. マージ後、貢献ブランチを削除

### 独自機能（個人利用）

1. `develop` から機能ブランチ（`feature/*`）を作成
2. 完成後、`develop` に統合
3. 本家にはプルリクエストを送信しない

---

## 進行中の貢献

> このセクションは貢献の進捗に応じて更新されます。

| ブランチ | 状態 | 説明 |
|---------|------|------|
| `contrib/context-optimization` | 進行中 | サブエージェントアーキテクチャのコンテキスト管理最適化 |
| `contrib/docs-restructure` | 進行中 | ドキュメント構成の整理・再編 |

---

## リンク

- **本家リポジトリ**: https://github.com/nahisaho/MUSUBIX
- **npm**: https://www.npmjs.com/package/musubix
- **ライセンス**: [MIT](https://github.com/nahisaho/MUSUBIX/blob/main/LICENSE)
