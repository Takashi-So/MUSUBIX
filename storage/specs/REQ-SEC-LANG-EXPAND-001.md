# 要件定義書: 追加言語セキュリティスキャナー

**ID**: REQ-SEC-LANG-EXPAND-001  
**Version**: 1.0.0  
**Created**: 2026-01-12  
**Author**: AI Agent (GitHub Copilot)  
**Status**: Draft  
**Priority**: P1 (重要)

---

## 概要

musubix-securityパッケージに**Go, Java, Rust**の3言語向けセキュリティスキャナーを追加し、マルチ言語脆弱性検出機能を拡張する。

---

## 背景・動機

### 現状

| 言語 | 対応状況 | 備考 |
|------|----------|------|
| TypeScript | ✅ 対応済み | VulnerabilityScanner |
| JavaScript | ✅ 対応済み | VulnerabilityScanner |
| Python | ✅ 対応済み | PythonScanner |
| PHP | ✅ 対応済み | PhpScanner |
| **Go** | ❌ 未対応 | extractor存在、スキャナーなし |
| **Java** | ❌ 未対応 | extractor存在、スキャナーなし |
| **Rust** | ❌ 未対応 | tree-sitter依存あり、実装なし |

### 競合製品との比較

| 製品 | Go | Java | Rust |
|------|-----|------|------|
| CodeQL | ✅ | ✅ | ✅ |
| Semgrep | ✅ | ✅ | ✅ |
| Snyk Code | ✅ | ✅ | ✅ |
| **MUSUBIX** | ❌ | ❌ | ❌ |

→ 追加言語サポートはMUSUBIXの競争力向上に必須

---

## 要件一覧

### 機能要件

#### REQ-SEC-GO-001: Goセキュリティスキャナー

> **WHEN** ユーザーが`.go`ファイルをスキャン対象に指定した場合,  
> **THE** GoScannerモジュール **SHALL** 以下の脆弱性カテゴリを検出する:
> - SQL Injection (CWE-89)
> - Command Injection (CWE-78)
> - Path Traversal (CWE-22)
> - Insecure Deserialization (CWE-502)
> - Hardcoded Credentials (CWE-798)
> - Weak Cryptography (CWE-327)
> - Unsafe HTTP Client (CWE-295)
> - Race Condition (CWE-362)

#### REQ-SEC-GO-002: Go言語固有パターン

> **WHILE** GoScannerがファイルを解析している状態,  
> **THE** GoScanner **SHALL** Go言語固有の脆弱性パターンを検出する:
> - `database/sql`未使用の文字列連結クエリ
> - `os/exec`のシェル展開
> - `unsafe`パッケージの使用
> - Goroutine競合状態
> - defer/recoverのエラー無視

#### REQ-SEC-JAVA-001: Javaセキュリティスキャナー

> **WHEN** ユーザーが`.java`ファイルをスキャン対象に指定した場合,  
> **THE** JavaScannerモジュール **SHALL** 以下の脆弱性カテゴリを検出する:
> - SQL Injection (CWE-89)
> - Command Injection (CWE-78)
> - LDAP Injection (CWE-90)
> - XPath Injection (CWE-643)
> - XXE (CWE-611)
> - Insecure Deserialization (CWE-502)
> - Hardcoded Credentials (CWE-798)
> - Weak Cryptography (CWE-327)
> - Path Traversal (CWE-22)

#### REQ-SEC-JAVA-002: Java言語固有パターン

> **WHILE** JavaScannerがファイルを解析している状態,  
> **THE** JavaScanner **SHALL** Java言語固有の脆弱性パターンを検出する:
> - JDBC PreparedStatement未使用
> - Runtime.exec()のシェルコマンド実行
> - ObjectInputStream.readObject()の安全でない使用
> - DocumentBuilderのXXE設定
> - Spring Framework固有の脆弱性パターン

#### REQ-SEC-RUST-001: Rustセキュリティスキャナー

> **WHEN** ユーザーが`.rs`ファイルをスキャン対象に指定した場合,  
> **THE** RustScannerモジュール **SHALL** 以下の脆弱性カテゴリを検出する:
> - Command Injection (CWE-78)
> - SQL Injection (CWE-89)
> - Path Traversal (CWE-22)
> - Unsafe Block Misuse (CWE-119)
> - Hardcoded Credentials (CWE-798)
> - Panic in Production (CWE-248)

#### REQ-SEC-RUST-002: Rust言語固有パターン

> **WHILE** RustScannerがファイルを解析している状態,  
> **THE** RustScanner **SHALL** Rust言語固有の脆弱性パターンを検出する:
> - `unsafe`ブロック内の危険な操作
> - `unwrap()`/`expect()`の過剰使用
> - 生ポインタ操作
> - 外部FFI呼び出しの安全性
> - std::process::Command のシェル展開

#### REQ-SEC-MULTI-002: マルチ言語スキャナー拡張

> **WHEN** MultiLanguageScannerがディレクトリをスキャンする場合,  
> **THE** MultiLanguageScanner **SHALL** Go, Java, Rustファイルを自動検出し、適切なスキャナーにディスパッチする。

#### REQ-SEC-MULTI-003: サポート言語リスト拡張

> **THE** getSupportedLanguages()メソッド **SHALL** 以下の言語を返す:
> - typescript, javascript, python, php, **go, java, rust**

### 非機能要件

#### REQ-SEC-PERF-001: スキャン性能

> **THE** 追加スキャナー **SHALL** 1ファイルあたり500ms以内でスキャンを完了する。

#### REQ-SEC-COMPAT-001: 後方互換性

> **THE** 実装 **SHALL NOT** 既存のTypeScript/JavaScript/Python/PHPスキャナーの動作を変更する。

#### REQ-SEC-TREE-001: tree-sitter依存

> **THE** 実装 **SHALL** 既存のtree-sitter依存（tree-sitter-go@0.23.0, tree-sitter-java@0.23.0, tree-sitter-rust@0.23.0）を使用する。

---

## 成果物

| 成果物 | ファイルパス | 説明 |
|--------|-------------|------|
| GoScanner | `packages/security/src/analysis/go-scanner.ts` | Goセキュリティスキャナー |
| JavaScanner | `packages/security/src/analysis/java-scanner.ts` | Javaセキュリティスキャナー |
| RustScanner | `packages/security/src/analysis/rust-scanner.ts` | Rustセキュリティスキャナー |
| テスト | `packages/security/src/analysis/__tests__/` | 各スキャナーのユニットテスト |
| 統合 | `packages/security/src/analysis/multi-language-scanner.ts` | MultiLanguageScanner拡張 |

---

## 受入基準

1. ✅ GoScanner: 8種類の脆弱性パターンを検出
2. ✅ JavaScanner: 9種類の脆弱性パターンを検出
3. ✅ RustScanner: 6種類の脆弱性パターンを検出
4. ✅ MultiLanguageScanner: `.go`, `.java`, `.rs`ファイルを自動検出
5. ✅ 各スキャナーに10件以上のテストケース
6. ✅ 既存テスト（2249件）が全て合格
7. ✅ ドキュメント更新（CHANGELOG.md）

---

## トレーサビリティ

| 要件ID | 設計ID | タスクID |
|--------|--------|---------|
| REQ-SEC-GO-001 | DES-SEC-GO-001 | TSK-SEC-GO-001 |
| REQ-SEC-GO-002 | DES-SEC-GO-001 | TSK-SEC-GO-002 |
| REQ-SEC-JAVA-001 | DES-SEC-JAVA-001 | TSK-SEC-JAVA-001 |
| REQ-SEC-JAVA-002 | DES-SEC-JAVA-001 | TSK-SEC-JAVA-002 |
| REQ-SEC-RUST-001 | DES-SEC-RUST-001 | TSK-SEC-RUST-001 |
| REQ-SEC-RUST-002 | DES-SEC-RUST-001 | TSK-SEC-RUST-002 |
| REQ-SEC-MULTI-002 | DES-SEC-MULTI-002 | TSK-SEC-MULTI-002 |
| REQ-SEC-MULTI-003 | DES-SEC-MULTI-002 | TSK-SEC-MULTI-002 |

---

## リスク

| リスク | 影響 | 軽減策 |
|--------|------|--------|
| tree-sitter互換性 | 高 | 既存依存を使用、ランタイムでのダイナミックimport |
| パターン検出精度 | 中 | 実際の脆弱性サンプルでテスト |
| 性能劣化 | 低 | 並列スキャン、早期終了の実装 |

---

## 参考資料

- [CWE Top 25](https://cwe.mitre.org/top25/)
- [OWASP Top 10](https://owasp.org/Top10/)
- [Go Security Guidelines](https://go.dev/doc/security)
- [OWASP Java Security Cheat Sheet](https://cheatsheetseries.owasp.org/cheatsheets/Java_Security_Cheat_Sheet.html)
- [Rust Security Guidelines](https://anssi-fr.github.io/rust-guide/)
