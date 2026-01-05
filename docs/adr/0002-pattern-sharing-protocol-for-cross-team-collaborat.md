# ADR-0002: Pattern Sharing Protocol for cross-team collaboration

- **Date**: 2026-01-05
- **Status**: accepted
- **Deciders**: Architecture Team
- **Categories**: Sharing, Security

## Context

チーム間で学習済みパターンを共有する要求がある。プライバシーとセキュリティを考慮したプロトコルが必要。

### 要件
- REQ-SHARE-001: JSON形式でエクスポート
- REQ-SHARE-003: インポート時のオントロジー検証
- REQ-SHARE-004: 機密データの除去
- REQ-SHARE-005: 競合解決戦略

### 検討した選択肢
1. **Git-based sharing**: Gitリポジトリでパターンを共有
2. **REST API**: 中央サーバー経由の共有
3. **File-based export/import**: JSONファイルの直接交換

## Decision

**選択肢 3: File-based export/import** を採用する。

### 理由
- インフラ不要で即座に利用可能
- オフライン環境でも利用可能
- 将来的にGit連携への拡張が容易

### ファイルフォーマット

```json
{
  "version": "1.0",
  "exportedAt": "2026-01-05T12:00:00Z",
  "patterns": [
    {
      "id": "PAT-001",
      "name": "Repository Pattern",
      "category": "design",
      "confidence": 0.95,
      "template": "...",
      "metadata": {
        "author": "[REDACTED]",
        "domain": "data-access"
      }
    }
  ],
  "checksum": "sha256:..."
}
```

### セキュリティ対策
| 対策 | 実装 |
|------|------|
| 機密データ除去 | DataSanitizerによる自動マスキング |
| 改ざん検出 | SHA-256チェックサム |
| スキーマ検証 | JSON Schemaによるバリデーション |

## Consequences

### Positive
- シンプルで即座に利用可能
- プライバシー保護が容易
- バージョン管理が明確

### Negative
- 自動同期機能なし（将来拡張）
- 大規模チームでの管理が煩雑になる可能性

## Related Requirements

- REQ-SHARE-001: JSON export format
- REQ-SHARE-002: External import
- REQ-SHARE-003: Ontology validation
- REQ-SHARE-004: Privacy protection
- REQ-SHARE-005: Conflict resolution
