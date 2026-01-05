# MUSUBIX v1.5.0 Interactive CLI Mode Design

**Document ID**: DES-CLI-v1.5.0  
**Version**: 1.0.0  
**Created**: 2026-01-05  
**Based On**: REQ-CLI-v1.5.0.md  

---

## 1. Context Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                         MUSUBIX CLI                             │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                    REPL Engine                           │   │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐               │   │
│  │  │ Readline │  │Completer │  │ History  │               │   │
│  │  │ Interface│  │ Service  │  │ Manager  │               │   │
│  │  └────┬─────┘  └────┬─────┘  └────┬─────┘               │   │
│  │       │             │             │                      │   │
│  │       └─────────────┴─────────────┘                      │   │
│  │                     │                                    │   │
│  │              ┌──────▼──────┐                             │   │
│  │              │   Command   │                             │   │
│  │              │  Executor   │                             │   │
│  │              └──────┬──────┘                             │   │
│  └─────────────────────┼───────────────────────────────────┘   │
│                        │                                        │
│  ┌─────────────────────▼───────────────────────────────────┐   │
│  │                 Existing CLI Commands                    │   │
│  │  requirements │ design │ codegen │ test │ trace │ learn │   │
│  └──────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. Container Diagram

```
┌──────────────────────────────────────────────────────────────────┐
│                        packages/core                             │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │                     src/cli/repl/                          │ │
│  │  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐          │ │
│  │  │  repl.ts    │ │ completer.ts│ │  history.ts │          │ │
│  │  │             │ │             │ │             │          │ │
│  │  │ - start()   │ │ - complete()│ │ - load()    │          │ │
│  │  │ - execute() │ │ - suggest() │ │ - save()    │          │ │
│  │  │ - stop()    │ │ - files()   │ │ - search()  │          │ │
│  │  └─────────────┘ └─────────────┘ └─────────────┘          │ │
│  │                                                            │ │
│  │  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐          │ │
│  │  │ formatter.ts│ │  session.ts │ │  prompt.ts  │          │ │
│  │  │             │ │             │ │             │          │ │
│  │  │ - json()    │ │ - get()     │ │ - render()  │          │ │
│  │  │ - table()   │ │ - set()     │ │ - context() │          │ │
│  │  │ - yaml()    │ │ - clear()   │ │ - color()   │          │ │
│  │  └─────────────┘ └─────────────┘ └─────────────┘          │ │
│  └────────────────────────────────────────────────────────────┘ │
└──────────────────────────────────────────────────────────────────┘
```

---

## 3. Component Design

### 3.1 ReplEngine (DES-CLI-001)

**Traces**: REQ-CLI-001

```typescript
/**
 * REPL Engine - Interactive command-line interface
 * 
 * @pattern Facade - Provides unified interface to REPL subsystems
 * @responsibility Start/stop REPL session, route commands
 */
interface ReplEngine {
  /**
   * Start REPL session
   * @returns Promise that resolves when session ends
   */
  start(): Promise<void>;
  
  /**
   * Execute a command string
   * @param command - The command to execute
   * @returns Command result
   */
  execute(command: string): Promise<CommandResult>;
  
  /**
   * Stop REPL session gracefully
   */
  stop(): void;
  
  /**
   * Check if REPL is running
   */
  isRunning(): boolean;
}

interface CommandResult {
  success: boolean;
  output: string;
  error?: Error;
  exitCode: number;
}
```

### 3.2 CommandCompleter (DES-CLI-002)

**Traces**: REQ-CLI-002

```typescript
/**
 * Command Completer - Provides auto-completion for commands
 * 
 * @pattern Strategy - Different completion strategies for different contexts
 * @responsibility Suggest completions based on input context
 */
interface CommandCompleter {
  /**
   * Get completions for partial input
   * @param line - Current input line
   * @param cursor - Cursor position
   * @returns Array of completion suggestions
   */
  complete(line: string, cursor: number): CompletionResult;
  
  /**
   * Register command definitions for completion
   * @param commands - Command definitions
   */
  registerCommands(commands: CommandDefinition[]): void;
}

interface CompletionResult {
  completions: string[];
  prefix: string;
}

interface CommandDefinition {
  name: string;
  subcommands?: string[];
  options?: string[];
  description: string;
}
```

### 3.3 HistoryManager (DES-CLI-003)

**Traces**: REQ-CLI-003

```typescript
/**
 * History Manager - Manages command history persistence
 * 
 * @pattern Repository - Abstracts history storage
 * @responsibility Load, save, and navigate command history
 */
interface HistoryManager {
  /**
   * Load history from persistent storage
   */
  load(): Promise<void>;
  
  /**
   * Save current history to persistent storage
   */
  save(): Promise<void>;
  
  /**
   * Add command to history
   * @param command - The command to add
   */
  add(command: string): void;
  
  /**
   * Get previous command (UP arrow)
   */
  previous(): string | undefined;
  
  /**
   * Get next command (DOWN arrow)
   */
  next(): string | undefined;
  
  /**
   * Search history for matching commands
   * @param query - Search query
   */
  search(query: string): string[];
  
  /**
   * Get all history entries
   */
  getAll(): string[];
  
  /**
   * Clear all history
   */
  clear(): void;
}
```

### 3.4 SessionState (DES-CLI-007)

**Traces**: REQ-CLI-007

```typescript
/**
 * Session State - Manages REPL session variables
 * 
 * @pattern State - Encapsulates session state
 * @responsibility Manage variables and last command result
 */
interface SessionState {
  /**
   * Set a session variable
   * @param key - Variable name
   * @param value - Variable value
   */
  set(key: string, value: string): void;
  
  /**
   * Get a session variable
   * @param key - Variable name
   */
  get(key: string): string | undefined;
  
  /**
   * Get all variables
   */
  getAll(): Record<string, string>;
  
  /**
   * Set last command result
   * @param result - Command result
   */
  setLastResult(result: CommandResult): void;
  
  /**
   * Get last command result
   */
  getLastResult(): CommandResult | undefined;
  
  /**
   * Clear all session state
   */
  clear(): void;
}
```

### 3.5 OutputFormatter (DES-CLI-008)

**Traces**: REQ-CLI-008

```typescript
/**
 * Output Formatter - Formats command output
 * 
 * @pattern Strategy - Different formatting strategies
 * @responsibility Convert data to various output formats
 */
interface OutputFormatter {
  /**
   * Format data as JSON
   */
  formatJson(data: unknown): string;
  
  /**
   * Format data as table
   */
  formatTable(data: unknown[]): string;
  
  /**
   * Format data as YAML
   */
  formatYaml(data: unknown): string;
  
  /**
   * Auto-detect best format
   */
  autoFormat(data: unknown): string;
}
```

### 3.6 PromptRenderer (DES-CLI-004)

**Traces**: REQ-CLI-004

```typescript
/**
 * Prompt Renderer - Renders context-aware prompts
 * 
 * @pattern Template Method - Base prompt with customizable parts
 * @responsibility Render prompt with project context and status
 */
interface PromptRenderer {
  /**
   * Render the prompt string
   */
  render(): string;
  
  /**
   * Set project context
   * @param context - Current project context
   */
  setContext(context: ProjectContext): void;
  
  /**
   * Set error state
   * @param hasError - Whether there's an error
   */
  setErrorState(hasError: boolean): void;
}

interface ProjectContext {
  name?: string;
  phase?: 'requirements' | 'design' | 'implementation' | 'test';
  path?: string;
}
```

---

## 4. Sequence Diagrams

### 4.1 REPL Start Sequence

```
User          ReplEngine     HistoryManager    Completer       Prompt
  │               │               │               │               │
  │  musubix repl │               │               │               │
  │──────────────▶│               │               │               │
  │               │    load()     │               │               │
  │               │──────────────▶│               │               │
  │               │   history[]   │               │               │
  │               │◀──────────────│               │               │
  │               │               │ register()    │               │
  │               │──────────────────────────────▶│               │
  │               │               │               │  render()     │
  │               │──────────────────────────────────────────────▶│
  │               │               │               │    prompt     │
  │  musubix>     │◀──────────────────────────────────────────────│
  │◀──────────────│               │               │               │
```

### 4.2 Command Completion Sequence

```
User          Readline      Completer      CommandDefs
  │               │               │               │
  │  req<TAB>     │               │               │
  │──────────────▶│               │               │
  │               │  complete()   │               │
  │               │──────────────▶│               │
  │               │               │    match()    │
  │               │               │──────────────▶│
  │               │               │  candidates   │
  │               │               │◀──────────────│
  │               │ ["requirements"]              │
  │               │◀──────────────│               │
  │ requirements  │               │               │
  │◀──────────────│               │               │
```

---

## 5. File Structure

```
packages/core/src/cli/
├── commands/
│   └── repl.ts              # REPL command entry point
├── repl/
│   ├── index.ts             # Exports
│   ├── types.ts             # Type definitions
│   ├── repl-engine.ts       # Main REPL engine
│   ├── command-completer.ts # Auto-completion
│   ├── history-manager.ts   # History persistence
│   ├── session-state.ts     # Session variables
│   ├── output-formatter.ts  # Output formatting
│   ├── prompt-renderer.ts   # Prompt rendering
│   └── __tests__/
│       ├── repl-engine.test.ts
│       ├── command-completer.test.ts
│       ├── history-manager.test.ts
│       ├── session-state.test.ts
│       ├── output-formatter.test.ts
│       └── prompt-renderer.test.ts
```

---

## 6. Configuration

### 6.1 History File Location

```
~/.musubix/history          # Command history
~/.musubix/repl.config.json # REPL configuration
```

### 6.2 Default Configuration

```json
{
  "historySize": 1000,
  "prompt": {
    "showProject": true,
    "showPhase": true,
    "useColor": true
  },
  "completion": {
    "enabled": true,
    "maxSuggestions": 10
  },
  "output": {
    "defaultFormat": "table",
    "paging": true,
    "pageSize": 50
  }
}
```

---

## 7. Design Decisions

### ADR-CLI-001: Use Node.js readline

**Decision**: Use built-in `readline` module instead of third-party libraries.

**Rationale**:
- Zero additional dependencies
- Well-tested and stable
- Sufficient for our needs

**Alternatives Considered**:
- inquirer.js - Too heavy, designed for prompts not REPL
- vorpal - Abandoned project

### ADR-CLI-002: History Storage Format

**Decision**: Store history as plain text, one command per line.

**Rationale**:
- Simple and portable
- Easy to edit manually
- Compatible with shell history format

---

## 8. Traceability Matrix

| Design | Requirement | Component | Test |
|--------|-------------|-----------|------|
| DES-CLI-001 | REQ-CLI-001 | ReplEngine | TST-CLI-001 |
| DES-CLI-002 | REQ-CLI-002 | CommandCompleter | TST-CLI-002 |
| DES-CLI-003 | REQ-CLI-003 | HistoryManager | TST-CLI-003 |
| DES-CLI-004 | REQ-CLI-004 | PromptRenderer | TST-CLI-004 |
| DES-CLI-005 | REQ-CLI-005 | InlineHelp | TST-CLI-005 |
| DES-CLI-006 | REQ-CLI-006 | MultiLineInput | TST-CLI-006 |
| DES-CLI-007 | REQ-CLI-007 | SessionState | TST-CLI-007 |
| DES-CLI-008 | REQ-CLI-008 | OutputFormatter | TST-CLI-008 |

---

**Document Version History**:
| Version | Date | Changes |
|---------|------|---------|
| 1.0.0 | 2026-01-05 | Initial design |
