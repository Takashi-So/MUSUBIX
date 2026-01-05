# REQ-REPL-v1.6.0: REPL Test Implementation & CLI Enhancement

**Version**: 1.6.0
**Created**: 2026-01-06
**Status**: Draft
**Author**: AI Agent

---

## Overview

v1.6.0では、Interactive CLI Mode（REPL）の22個のスケルトンテストを完全実装し、
CLI統合を強化することで、実用的な対話型シェル環境を完成させる。

---

## Requirements

### REQ-REPL-001: ReplEngine Tests Implementation

**Type**: Event-driven
**Priority**: P0
**Pattern**: EARS Event-driven

> WHEN the ReplEngine is initialized, THE system SHALL start REPL session and display prompt within 100ms.

**Acceptance Criteria**:
- [ ] `start()` - REPLセッション開始テスト
- [ ] `execute()` - コマンド実行テスト
- [ ] `stop()` - グレースフル終了テスト
- [ ] History loading on start
- [ ] Command completion registration

**Traces**: repl.test.ts lines 27-93

---

### REQ-REPL-002: CommandCompleter Tests Implementation

**Type**: Event-driven
**Priority**: P0
**Pattern**: EARS Event-driven

> WHEN the user types a partial command, THE system SHALL provide relevant completions within 50ms.

**Acceptance Criteria**:
- [ ] Partial command name completion
- [ ] Subcommand completion after space
- [ ] Options completion (--option)
- [ ] File path completion
- [ ] Empty input shows all commands

**Traces**: repl.test.ts lines 99-148

---

### REQ-REPL-003: HistoryManager Tests Implementation

**Type**: State-driven
**Priority**: P0
**Pattern**: EARS State-driven

> WHILE the REPL session is active, THE system SHALL maintain command history with load/save persistence.

**Acceptance Criteria**:
- [ ] Load history from file
- [ ] Save history to file
- [ ] History size limit (max 1000)
- [ ] No duplicate consecutive commands
- [ ] Previous/Next navigation
- [ ] History search

**Traces**: repl.test.ts lines 154-258

---

### REQ-REPL-004: SessionState Tests Implementation

**Type**: Ubiquitous
**Priority**: P0
**Pattern**: EARS Ubiquitous

> THE system SHALL maintain session state with variable storage and last result tracking.

**Acceptance Criteria**:
- [ ] Set/Get session variables
- [ ] Last result storage ($_)
- [ ] Session clear functionality
- [ ] Variable overwrite support

**Traces**: repl.test.ts lines 264-325

---

### REQ-REPL-005: OutputFormatter Tests Implementation

**Type**: Event-driven
**Priority**: P0
**Pattern**: EARS Event-driven

> WHEN output is generated, THE system SHALL format it according to specified format (JSON/Table/YAML).

**Acceptance Criteria**:
- [ ] JSON format with pretty print
- [ ] Table format with borders
- [ ] YAML format
- [ ] Auto-detect best format

**Traces**: repl.test.ts lines 331-395

---

### REQ-REPL-006: PromptRenderer Tests Implementation

**Type**: State-driven
**Priority**: P0
**Pattern**: EARS State-driven

> WHILE in REPL mode, THE system SHALL render context-aware prompts showing project name and phase.

**Acceptance Criteria**:
- [ ] Default prompt rendering
- [ ] Project name in prompt
- [ ] Phase indicator in prompt
- [ ] Error state color change

**Traces**: repl.test.ts lines 401-440

---

### REQ-REPL-007: CLI Integration

**Type**: Event-driven
**Priority**: P0
**Pattern**: EARS Event-driven

> WHEN a command is executed in REPL, THE system SHALL delegate to actual CLI command handlers.

**Acceptance Criteria**:
- [ ] Help command execution
- [ ] Requirements analyze command
- [ ] Output format option handling
- [ ] Error handling for invalid commands

**Traces**: repl-engine.ts line 318

---

### REQ-REPL-008: Pattern Compression

**Type**: Optional
**Priority**: P1
**Pattern**: EARS Optional

> IF pattern export is requested with compression, THEN THE system SHALL apply zlib compression.

**Acceptance Criteria**:
- [ ] zlib compression support
- [ ] Compression level option
- [ ] Decompression on import

**Traces**: pattern-serializer.ts line 337

---

### REQ-REPL-009: Wake-Sleep Pattern Integration

**Type**: Event-driven
**Priority**: P1
**Pattern**: EARS Event-driven

> WHEN wake-sleep cycle runs, THE system SHALL retrieve pattern count from pattern library.

**Acceptance Criteria**:
- [ ] Pattern library integration
- [ ] Pattern count retrieval
- [ ] Cycle status reporting

**Traces**: cycle-manager.ts line 97

---

## Test Count Estimate

| Category | Test Count |
|----------|-----------|
| ReplEngine | 9 |
| CommandCompleter | 7 |
| HistoryManager | 10 |
| SessionState | 6 |
| OutputFormatter | 6 |
| PromptRenderer | 4 |
| Integration | 4 |
| Compression | 3 |
| Wake-Sleep | 3 |
| **Total** | **52** |

---

## Dependencies

- `packages/core/src/cli/repl/` - REPL components
- `packages/core/src/learning/sharing/` - Pattern serializer
- `packages/wake-sleep/src/cycle/` - Cycle manager

---

## Definition of Done

1. All 22 skeleton tests in repl.test.ts fully implemented
2. CLI integration in repl-engine.ts completed
3. zlib compression in pattern-serializer.ts added
4. Pattern library integration in cycle-manager.ts completed
5. All new tests passing
6. Documentation updated
7. npm publish successful

---

## Changelog Reference

This requirement will be documented in CHANGELOG.md under:
```markdown
## [1.6.0] - 2026-01-XX

### Added - REPL Test Implementation & CLI Enhancement

- REQ-REPL-001: ReplEngine tests
- REQ-REPL-002: CommandCompleter tests
- REQ-REPL-003: HistoryManager tests
- REQ-REPL-004: SessionState tests
- REQ-REPL-005: OutputFormatter tests
- REQ-REPL-006: PromptRenderer tests
- REQ-REPL-007: CLI integration
- REQ-REPL-008: Pattern compression
- REQ-REPL-009: Wake-Sleep integration
```
