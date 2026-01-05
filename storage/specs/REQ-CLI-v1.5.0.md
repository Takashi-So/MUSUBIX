# MUSUBIX v1.5.0 Interactive CLI Mode Requirements

**Document ID**: REQ-CLI-v1.5.0  
**Version**: 1.0.0  
**Created**: 2026-01-05  
**Based On**: ROADMAP-v1.5.md  

---

## 1. Overview

Interactive CLI Mode は、MUSUBIXの対話的なコマンドラインインターフェースを提供し、
開発者がREPLモードでSDDワークフローを効率的に実行できるようにする。

---

## 2. Requirements

### 2.1 REPL Mode (REQ-CLI-001)

**EARS Pattern**: Event-Driven

```
WHEN the user executes 'musubix repl' command,
THE system SHALL start an interactive REPL session
that accepts commands and displays results in real-time.
```

**Acceptance Criteria**:
- [ ] `musubix repl` コマンドでREPLセッションを開始
- [ ] プロンプト表示 (`musubix> `)
- [ ] コマンド入力と実行結果の表示
- [ ] `exit` または `quit` でセッション終了
- [ ] Ctrl+C でセッション終了

**Priority**: P0  
**Trace**: REQ-CLI-010

---

### 2.2 Command Auto-Completion (REQ-CLI-002)

**EARS Pattern**: Event-Driven

```
WHEN the user presses TAB key during command input,
THE system SHALL display available command completions
based on the current input context.
```

**Acceptance Criteria**:
- [ ] TABキーでコマンド補完
- [ ] サブコマンドの補完（例: `requirements` → `analyze`, `validate`）
- [ ] ファイルパスの補完
- [ ] オプションの補完（`--`で始まるオプション）
- [ ] 複数候補がある場合は一覧表示

**Priority**: P0  
**Trace**: REQ-CLI-010

---

### 2.3 Command History (REQ-CLI-003)

**EARS Pattern**: Event-Driven

```
WHEN the user presses UP/DOWN arrow keys,
THE system SHALL navigate through previously executed commands.
```

**Acceptance Criteria**:
- [ ] UP/DOWNキーでコマンド履歴をナビゲート
- [ ] 履歴は永続化（`~/.musubix/history`に保存）
- [ ] 最大1000件の履歴を保持
- [ ] Ctrl+R で履歴検索
- [ ] `history` コマンドで履歴一覧表示

**Priority**: P1  
**Trace**: REQ-CLI-010

---

### 2.4 Context-Aware Prompts (REQ-CLI-004)

**EARS Pattern**: State-Driven

```
WHILE in a REPL session with an active project,
THE system SHALL display the current project context in the prompt.
```

**Acceptance Criteria**:
- [ ] プロジェクト名をプロンプトに表示 (`project-name> `)
- [ ] 現在のフェーズ（requirements/design/implementation）を表示
- [ ] エラー状態を色で示す（赤: エラー、緑: 正常）

**Priority**: P2  
**Trace**: REQ-CLI-010

---

### 2.5 Inline Help (REQ-CLI-005)

**EARS Pattern**: Event-Driven

```
WHEN the user types '?' or 'help' followed by a command name,
THE system SHALL display detailed help for that command.
```

**Acceptance Criteria**:
- [ ] `?` で現在のコンテキストのヘルプ表示
- [ ] `help <command>` でコマンド詳細表示
- [ ] コマンド例を含むヘルプ
- [ ] 関連コマンドのサジェスト

**Priority**: P1  
**Trace**: REQ-CLI-010

---

### 2.6 Multi-line Input (REQ-CLI-006)

**EARS Pattern**: Event-Driven

```
WHEN the user enters an incomplete command (e.g., unclosed quotes),
THE system SHALL continue accepting input on the next line.
```

**Acceptance Criteria**:
- [ ] 継続行のプロンプト変更 (`... `)
- [ ] 複数行のJSONやMarkdown入力をサポート
- [ ] Ctrl+D で入力完了

**Priority**: P2  
**Trace**: REQ-CLI-010

---

### 2.7 Session State Persistence (REQ-CLI-007)

**EARS Pattern**: Ubiquitous

```
THE system SHALL persist session variables and state
across REPL commands within the same session.
```

**Acceptance Criteria**:
- [ ] セッション変数の設定 (`set VAR=value`)
- [ ] 変数の参照 (`$VAR`)
- [ ] 最後のコマンド結果を `$_` で参照可能
- [ ] `env` コマンドで環境表示

**Priority**: P1  
**Trace**: REQ-CLI-010

---

### 2.8 Output Formatting (REQ-CLI-008)

**EARS Pattern**: Optional

```
IF the user specifies '--format' option,
THEN THE system SHALL format output accordingly (json, table, yaml).
```

**Acceptance Criteria**:
- [ ] `--format json` でJSON出力
- [ ] `--format table` でテーブル出力
- [ ] `--format yaml` でYAML出力
- [ ] デフォルトはテーブル形式
- [ ] ページング機能（長い出力時）

**Priority**: P2  
**Trace**: REQ-CLI-010

---

## 3. Non-Functional Requirements

### 3.1 Performance (REQ-CLI-NFR-001)

```
THE system SHALL respond to user input within 100ms
for command completion and history navigation.
```

### 3.2 Usability (REQ-CLI-NFR-002)

```
THE system SHALL provide clear error messages
with suggestions for correction when invalid commands are entered.
```

### 3.3 Compatibility (REQ-CLI-NFR-003)

```
THE system SHALL work on macOS, Linux, and Windows terminals
with support for common terminal emulators.
```

---

## 4. Traceability Matrix

| Requirement | Priority | Design | Test | Status |
|-------------|----------|--------|------|--------|
| REQ-CLI-001 | P0 | DES-CLI-001 | TST-CLI-001 | Planned |
| REQ-CLI-002 | P0 | DES-CLI-002 | TST-CLI-002 | Planned |
| REQ-CLI-003 | P1 | DES-CLI-003 | TST-CLI-003 | Planned |
| REQ-CLI-004 | P2 | DES-CLI-004 | TST-CLI-004 | Planned |
| REQ-CLI-005 | P1 | DES-CLI-005 | TST-CLI-005 | Planned |
| REQ-CLI-006 | P2 | DES-CLI-006 | TST-CLI-006 | Planned |
| REQ-CLI-007 | P1 | DES-CLI-007 | TST-CLI-007 | Planned |
| REQ-CLI-008 | P2 | DES-CLI-008 | TST-CLI-008 | Planned |

---

## 5. Dependencies

| Dependency | Purpose | Version |
|------------|---------|---------|
| readline | Node.js組み込みのreadlineモジュール | Built-in |
| chalk | ターミナル色付け | ^5.0.0 |
| ora | スピナー表示 | ^8.0.0 |
| table | テーブル表示 | ^6.8.0 |

---

**Document Version History**:
| Version | Date | Changes |
|---------|------|---------|
| 1.0.0 | 2026-01-05 | Initial requirements |
