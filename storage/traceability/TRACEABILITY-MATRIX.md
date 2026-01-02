# MUSUBIX トレーサビリティマトリクス

**文書ID**: TRA-MUSUBIX-001  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.1  
**作成日**: 2026-01-02  
**ステータス**: Active  
**準拠**: Article V (Traceability Mandate)

---

## 1. 概要

本文書は、MUSUBIXシステムにおける**要件 ↔ 設計 ↔ タスク ↔ 実装 ↔ テスト**の完全な双方向トレーサビリティを定義する。

### 1.1 トレーサビリティカバレッジ目標

| 項目 | 目標 | 現状 |
|------|------|------|
| 要件 → 設計 | 100% | 100% |
| 設計 → タスク | 100% | 100% |
| タスク → 実装 | 100% | 95% |
| 実装 → テスト | 100% | 30% |
| **全体カバレッジ** | **100%** | **81%** |

---

## 2. 要件 → 設計 → タスク → 実装 マトリクス

### 2.1 アーキテクチャ要件 (REQ-ARC-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-ARC-001 | DES-ARC-001 | TSK-001〜004 | `packages/*/` | - | ✅ 実装済 |
| REQ-ARC-002 | DES-ARC-002 | TSK-006〜008 | `packages/core/src/cli/` | - | ✅ 実装済 |

### 2.2 統合レイヤー要件 (REQ-INT-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-INT-001 | DES-INT-001 | TSK-020 | `packages/yata-client/src/reasoning/integrator.ts` | - | ✅ 実装済 |
| REQ-INT-002 | DES-INT-002 | TSK-021 | `packages/yata-client/src/reasoning/confidence.ts` | - | ✅ 実装済 |
| REQ-INT-003 | DES-INT-003 | TSK-022 | `packages/yata-client/src/reasoning/contradiction.ts` | - | ✅ 実装済 |
| REQ-INT-101 | DES-INT-101 | TSK-019 | `packages/mcp-server/src/platform/` | - | ✅ 実装済 |
| REQ-INT-102 | DES-INT-102 | TSK-015〜018 | `packages/mcp-server/src/server.ts` | - | ✅ 実装済 |

### 2.3 要求分析要件 (REQ-RA-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-RA-001 | DES-RA-001 | TSK-023 | `packages/core/src/validators/ears-validator.ts` | - | ✅ 実装済 |
| REQ-RA-002 | DES-RA-002 | TSK-014 | `packages/yata-client/src/knowledge/ontology.ts` | - | ✅ 実装済 |
| REQ-RA-003 | DES-RA-003 | TSK-042 | `packages/core/src/requirements/` | - | ⚠️ 部分実装 |
| REQ-RA-004 | DES-RA-004 | TSK-051 | `packages/core/src/requirements/` | - | ⚠️ 部分実装 |

### 2.4 設計生成要件 (REQ-DES-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-DES-001 | DES-DES-001 | TSK-026 | `packages/core/src/design/pattern-detector.ts` | - | ✅ 実装済 |
| REQ-DES-002 | DES-DES-002 | TSK-028 | `packages/core/src/design/framework-optimizer.ts` | - | ✅ 実装済 |
| REQ-DES-003 | DES-DES-003 | TSK-027 | `packages/core/src/design/solid-validator.ts` | - | ✅ 実装済 |
| REQ-DES-004 | DES-DES-004 | TSK-043 | `packages/core/src/design/c4-generator.ts` | - | ✅ 実装済 |
| REQ-DES-005 | DES-DES-005 | TSK-044 | `packages/core/src/design/adr-generator.ts` | - | ✅ 実装済 |

### 2.5 コード生成・検証要件 (REQ-COD-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-COD-001 | DES-COD-001 | TSK-029 | `packages/core/src/codegen/generator.ts` | - | ✅ 実装済 |
| REQ-COD-002 | DES-COD-002 | TSK-030 | `packages/core/src/codegen/static-analyzer.ts` | - | ✅ 実装済 |
| REQ-COD-003 | DES-COD-003 | TSK-033 | `packages/core/src/codegen/pattern-conformance.ts` | - | ✅ 実装済 |
| REQ-COD-004 | DES-COD-004 | TSK-034 | `packages/core/src/codegen/dependency-analyzer.ts` | - | ✅ 実装済 |
| REQ-COD-005 | DES-COD-005 | TSK-045 | `packages/core/src/codegen/coding-standards.ts` | - | ✅ 実装済 |
| REQ-COD-006 | DES-COD-006 | TSK-032 | `packages/core/src/codegen/security-scanner.ts` | - | ✅ 実装済 |

### 2.6 テスト生成要件 (REQ-TST-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-TST-001 | DES-TST-001 | TSK-035 | `packages/core/src/codegen/unit-test-generator.ts` | - | ✅ 実装済 |
| REQ-TST-002 | DES-TST-002 | TSK-036 | `packages/core/src/codegen/integration-test-generator.ts` | - | ✅ 実装済 |

### 2.7 説明生成要件 (REQ-EXP-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-EXP-001 | DES-EXP-001 | TSK-038 | `packages/core/src/explanation/` | - | ✅ 実装済 |
| REQ-EXP-002 | DES-EXP-002 | TSK-039 | `packages/core/src/explanation/` | - | ✅ 実装済 |
| REQ-EXP-003 | DES-EXP-003 | TSK-052 | `packages/core/src/explanation/` | - | ⚠️ 部分実装 |

### 2.8 トレーサビリティ要件 (REQ-TRA-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-TRA-001 | DES-TRA-001 | TSK-024 | `packages/core/src/traceability/manager.ts` | - | ✅ 実装済 |
| REQ-TRA-002 | DES-TRA-002 | TSK-025 | `packages/core/src/traceability/impact.ts` | - | ✅ 実装済 |

### 2.9 エラーリカバリ要件 (REQ-ERR-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-ERR-001 | DES-ERR-001 | TSK-040 | `packages/core/src/error/` | - | ✅ 実装済 |
| REQ-ERR-002 | DES-ERR-002 | TSK-041 | `packages/core/src/error/` | - | ✅ 実装済 |
| REQ-ERR-003 | DES-ERR-003 | TSK-046 | `packages/core/src/error/` | - | ⚠️ 部分実装 |

### 2.10 品質要件 (REQ-QUA-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-QUA-001 | DES-QUA-001 | TSK-031 | `packages/core/src/codegen/quality-metrics.ts` | - | ✅ 実装済 |
| REQ-QUA-002 | DES-QUA-002 | TSK-037 | `packages/core/src/codegen/coverage-reporter.ts` | - | ✅ 実装済 |

### 2.11 セキュリティ要件 (REQ-SEC-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-SEC-001 | DES-SEC-001 | TSK-011 | `packages/core/src/auth/` | - | ✅ 実装済 |
| REQ-SEC-002 | DES-SEC-002 | TSK-049 | `packages/core/src/auth/` | - | ⚠️ 部分実装 |

### 2.12 保守性要件 (REQ-MNT-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-MNT-001 | DES-MNT-001 | TSK-009 | `packages/core/src/utils/` | - | ✅ 実装済 |
| REQ-MNT-002 | DES-MNT-002 | TSK-010 | `packages/core/src/error/` | - | ✅ 実装済 |

### 2.13 パフォーマンス要件 (REQ-PER-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-PER-001 | DES-PER-001 | TSK-047 | - | - | ⏳ 未実装 |
| REQ-PER-002 | DES-PER-002 | TSK-048 | - | - | ⏳ 未実装 |

### 2.14 国際化要件 (REQ-I18N-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-I18N-001 | DES-I18N-001 | TSK-053 | - | - | ⏳ 未実装 |

### 2.15 Agent Skills要件 (REQ-SKL-*)

| 要件ID | 設計ID | タスクID | 実装ファイル | テストファイル | 状態 |
|--------|--------|----------|--------------|----------------|------|
| REQ-SKL-001 | DES-SKL-001 | TSK-054 | `.github/skills/` | - | ✅ 実装済 |
| REQ-SKL-002 | DES-SKL-002 | TSK-054 | `.github/skills/*/SKILL.md` | - | ✅ 実装済 |
| REQ-SKL-003 | DES-SKL-003 | TSK-054 | `.github/skills/*/SKILL.md` | - | ✅ 実装済 |
| REQ-SKL-004 | DES-SKL-004 | TSK-054 | `.github/skills/musubix-*/SKILL.md` | - | ✅ 実装済 |

---

## 3. 実装ファイル → 要件 逆引きマトリクス

### 3.1 packages/core/src/

| ファイルパス | 要件ID | 設計ID |
|-------------|--------|--------|
| `cli/` | REQ-ARC-002 | DES-ARC-002 |
| `cli/commands/help.ts` | REQ-ARC-002 | DES-ARC-002 |
| `validators/ears-validator.ts` | REQ-RA-001 | DES-RA-001 |
| `design/pattern-detector.ts` | REQ-DES-001 | DES-DES-001 |
| `design/framework-optimizer.ts` | REQ-DES-002 | DES-DES-002 |
| `design/solid-validator.ts` | REQ-DES-003 | DES-DES-003 |
| `design/c4-generator.ts` | REQ-DES-004 | DES-DES-004 |
| `design/adr-generator.ts` | REQ-DES-005 | DES-DES-005 |
| `codegen/generator.ts` | REQ-COD-001 | DES-COD-001 |
| `codegen/static-analyzer.ts` | REQ-COD-002 | DES-COD-002 |
| `codegen/pattern-conformance.ts` | REQ-COD-003 | DES-COD-003 |
| `codegen/dependency-analyzer.ts` | REQ-COD-004 | DES-COD-004 |
| `codegen/coding-standards.ts` | REQ-COD-005 | DES-COD-005 |
| `codegen/security-scanner.ts` | REQ-COD-006 | DES-COD-006 |
| `codegen/unit-test-generator.ts` | REQ-TST-001 | DES-TST-001 |
| `codegen/integration-test-generator.ts` | REQ-TST-002 | DES-TST-002 |
| `codegen/quality-metrics.ts` | REQ-QUA-001 | DES-QUA-001 |
| `codegen/coverage-reporter.ts` | REQ-QUA-002 | DES-QUA-002 |
| `traceability/manager.ts` | REQ-TRA-001 | DES-TRA-001 |
| `traceability/impact.ts` | REQ-TRA-002 | DES-TRA-002 |
| `explanation/` | REQ-EXP-001, REQ-EXP-002 | DES-EXP-001, DES-EXP-002 |
| `error/` | REQ-ERR-001, REQ-ERR-002, REQ-MNT-002 | DES-ERR-001, DES-ERR-002, DES-MNT-002 |
| `auth/` | REQ-SEC-001, REQ-SEC-002 | DES-SEC-001, DES-SEC-002 |
| `utils/` | REQ-MNT-001 | DES-MNT-001 |

### 3.2 packages/mcp-server/src/

| ファイルパス | 要件ID | 設計ID |
|-------------|--------|--------|
| `server.ts` | REQ-INT-102 | DES-INT-102 |
| `tools/sdd-tools.ts` | REQ-INT-102 | DES-INT-102 |
| `prompts/sdd-prompts.ts` | REQ-INT-102 | DES-INT-102 |
| `resources/sdd-resources.ts` | REQ-INT-102 | DES-INT-102 |
| `platform/` | REQ-INT-101 | DES-INT-101 |

### 3.3 packages/yata-client/src/

| ファイルパス | 要件ID | 設計ID |
|-------------|--------|--------|
| `reasoning/integrator.ts` | REQ-INT-001 | DES-INT-001 |
| `reasoning/confidence.ts` | REQ-INT-002 | DES-INT-002 |
| `reasoning/contradiction.ts` | REQ-INT-003 | DES-INT-003 |
| `knowledge/ontology.ts` | REQ-RA-002 | DES-RA-002 |
| `knowledge/query.ts` | REQ-INT-001 | DES-INT-001 |
| `mcp/client.ts` | REQ-INT-102 | DES-INT-102 |

### 3.4 .github/skills/

| ファイルパス | 要件ID | 設計ID |
|-------------|--------|--------|
| `musubix-sdd-workflow/SKILL.md` | REQ-SKL-001, REQ-SKL-002, REQ-SKL-003, REQ-SKL-004 | DES-SKL-001, DES-SKL-002, DES-SKL-003, DES-SKL-004 |
| `musubix-ears-validation/SKILL.md` | REQ-SKL-001, REQ-SKL-002, REQ-SKL-003, REQ-SKL-004 | DES-SKL-001, DES-SKL-002, DES-SKL-003, DES-SKL-004 |
| `musubix-code-generation/SKILL.md` | REQ-SKL-001, REQ-SKL-002, REQ-SKL-003, REQ-SKL-004 | DES-SKL-001, DES-SKL-002, DES-SKL-003, DES-SKL-004 |

---

## 4. テストカバレッジマトリクス

### 4.1 現在のテスト状況

| パッケージ | ユニットテスト | 統合テスト | E2Eテスト | カバレッジ |
|-----------|--------------|-----------|----------|----------|
| core | ❌ なし | ❌ なし | ✅ 1ファイル | 〜20% |
| mcp-server | ⚠️ 基本のみ | ❌ なし | ❌ なし | 〜10% |
| yata-client | ⚠️ 基本のみ | ❌ なし | ❌ なし | 〜10% |

### 4.2 テストファイル必要一覧

| 要件ID | 必要なテストファイル | 状態 |
|--------|---------------------|------|
| REQ-ARC-001 | `packages/core/__tests__/unit/architecture.test.ts` | ❌ 未作成 |
| REQ-ARC-002 | `packages/core/__tests__/unit/cli.test.ts` | ❌ 未作成 |
| REQ-INT-001 | `packages/yata-client/__tests__/unit/integrator.test.ts` | ❌ 未作成 |
| REQ-INT-002 | `packages/yata-client/__tests__/unit/confidence.test.ts` | ❌ 未作成 |
| REQ-INT-003 | `packages/yata-client/__tests__/unit/contradiction.test.ts` | ❌ 未作成 |
| REQ-RA-001 | `packages/core/__tests__/unit/ears-validator.test.ts` | ❌ 未作成 |
| REQ-DES-001 | `packages/core/__tests__/unit/pattern-detector.test.ts` | ❌ 未作成 |
| REQ-DES-002 | `packages/core/__tests__/unit/framework-optimizer.test.ts` | ❌ 未作成 |
| REQ-DES-003 | `packages/core/__tests__/unit/solid-validator.test.ts` | ❌ 未作成 |
| REQ-COD-001 | `packages/core/__tests__/unit/generator.test.ts` | ❌ 未作成 |
| REQ-COD-002 | `packages/core/__tests__/unit/static-analyzer.test.ts` | ❌ 未作成 |
| REQ-COD-006 | `packages/core/__tests__/unit/security-scanner.test.ts` | ❌ 未作成 |
| REQ-TRA-001 | `packages/core/__tests__/unit/traceability.test.ts` | ❌ 未作成 |
| REQ-INT-102 | `packages/mcp-server/__tests__/unit/server.test.ts` | ❌ 未作成 |

---

## 5. ギャップ分析

### 5.1 未実装要件

| 要件ID | 説明 | 優先度 | 理由 |
|--------|------|--------|------|
| REQ-PER-001 | 応答時間パフォーマンス | P1 | パフォーマンステスト基盤未整備 |
| REQ-PER-002 | スケーラビリティ | P1 | 負荷テスト基盤未整備 |
| REQ-I18N-001 | 多言語対応 | P2 | P2のため後回し |

### 5.2 テスト未作成

| カテゴリ | 件数 | 対応タスク |
|---------|------|-----------|
| ユニットテスト | 14件 | タスク2で対応 |
| 統合テスト | 10件 | タスク3で対応 |

### 5.3 要件ID正規化必要

| 現在のID | 問題 | 修正案 |
|---------|------|--------|
| REQ-NS-101 | REQ定義書に存在しない | REQ-INT-001に統合 |
| REQ-NS-103 | REQ定義書に存在しない | REQ-INT-002に統合 |
| REQ-NS-104 | REQ定義書に存在しない | REQ-INT-003に統合 |
| REQ-INT-101 | コード内で未参照 | 実装ファイルに追記 |
| REQ-CORE-101 | REQ定義書に存在しない | REQ-INT-102に統合 |

---

## 6. 更新履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|---------|--------|
| 1.0 | 2026-01-02 | 初版作成 | AI Agent |
| 1.1 | 2026-01-02 | Agent Skills要件追加: REQ-SKL-001〜004、要件数41→45 | AI Agent |

---

**文書ID**: TRA-MUSUBIX-001  
**バージョン**: 1.1  
**最終更新**: 2026-01-02
