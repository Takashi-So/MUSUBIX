# ADR-v3.7.0-001: Everything Claude Code知見の統合

**ステータス**: Proposed  
**日付**: 2026-01-25  
**決定者**: MUSUBIX Team

## コンテキスト

MUSUBIX v3.6.0でCursor FastRenderプロジェクトからの知見（トリアージシステム、非交渉事項エンジン、リソースリミッター等）を統合しました。

v3.7.0では、Anthropicハッカソン優勝者が公開している`affaan-m/everything-claude-code`リポジトリを分析し、Claude Codeの本格運用で必要とされる機能を特定しました。

## 問題

現在のMUSUBIXには以下の機能が不足しています：

1. **セッション永続性**: セッション間でコンテキストが失われる
2. **戦略的圧縮**: 自動圧縮が論理的な区切りを考慮しない
3. **継続学習フック**: セッション終了時のパターン自動抽出がない
4. **評価フレームワーク**: pass@k等の標準的AI評価メトリクスがない
5. **検証ループ**: 継続的な品質検証の仕組みがない
6. **チェックポイント**: 作業状態の保存・復元機能がない

## 決定

以下の9つの新パッケージを段階的に追加します：

### Phase 1: Core Session Management (v3.7.0)
| パッケージ | 優先度 | 機能 |
|-----------|--------|------|
| `session-manager` | P0 | セッション永続化、SessionStart/End/PreCompact Hook |
| `context-optimizer` | P1 | 戦略的圧縮提案、ツール呼び出しカウンター |
| `learning-hooks` | P1 | 継続学習、パターン自動抽出 |

### Phase 2: Evaluation Framework (v3.7.1)
| パッケージ | 優先度 | 機能 |
|-----------|--------|------|
| `eval-harness` | P1 | pass@k評価、Capability/Regression Eval |
| `verification-loop` | P2 | 6フェーズ検証、継続的検証 |
| `checkpoint` | P2 | 状態保存・復元、比較機能 |

### Phase 3: Code Intelligence (v3.7.2)
| パッケージ | 優先度 | 機能 |
|-----------|--------|------|
| `codemap` | P3 | リポジトリ構造分析、コードマップ生成 |
| `refactor-cleaner` | P3 | デッドコード検出・削除 |
| `context-injection` | P4 | 動的コンテキストモード |

## 理由

### everything-claude-codeを参照元に選んだ理由

1. **実績**: Anthropicハッカソン優勝者が10ヶ月以上の本番使用で検証
2. **網羅性**: エージェント、スキル、フック、コマンド、ルールを体系化
3. **ベストプラクティス**: Token最適化、Memory永続化、Eval手法を文書化
4. **コミュニティ採用**: GitHubスター数が多く、実用性が証明済み

### MUSUBIXとの差別化

everything-claude-codeは「設定ファイル集」であり、MUSUBIXは「プログラム可能なフレームワーク」です。

| 観点 | everything-claude-code | MUSUBIX v3.7.0 |
|------|----------------------|----------------|
| 形態 | Markdown設定ファイル | TypeScriptパッケージ |
| 拡張性 | 手動編集 | API経由でプログラム可能 |
| 統合 | Claude Code専用 | MCP標準で汎用 |
| 検証 | 手動 | 自動テスト5000+ |
| 方法論 | 暗黙的 | MUSUBI SDD明示的 |

## 代替案

### 案A: everything-claude-codeをそのまま採用
- **却下理由**: TypeScript統合不可、テスト自動化困難

### 案B: 別リポジトリとして分離
- **却下理由**: パッケージ間連携が困難、monorepoの利点喪失

### 案C: 段階的統合（採用）
- **理由**: 既存アーキテクチャとの整合性維持、段階的検証可能

## 影響

### ポジティブ
- Claude Code/Copilotとの親和性向上
- セッション間の継続性確保
- AI評価の標準化

### ネガティブ
- パッケージ数増加（28 → 37）
- 新しい概念の学習コスト
- ドキュメント更新負荷

## 関連決定

- ADR-v3.6.0-001: FastRender知見の統合
- ADR-v3.5.0-001: Assistant Axis導入
- ADR-v3.0.0-001: Git-Native Knowledge System

## 参考資料

- [REQ-v3.7.0-everything-claude-code-integration.md](storage/specs/REQ-v3.7.0-everything-claude-code-integration.md)
- [affaan-m/everything-claude-code](https://github.com/affaan-m/everything-claude-code)
