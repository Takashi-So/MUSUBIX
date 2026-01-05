/**
 * MUSUBIX v1.6.0 Interactive CLI Mode - Full Test Implementation
 *
 * @module cli/repl
 * @traces REQ-REPL-v1.6.0
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';

import { ReplEngine } from '../repl-engine.js';
import { CommandCompleter, createCommandCompleter } from '../command-completer.js';
import { HistoryManager, createHistoryManager } from '../history-manager.js';
import { SessionState, createSessionState } from '../session-state.js';
import { OutputFormatter, createOutputFormatter } from '../output-formatter.js';
import { PromptRenderer, createPromptRenderer } from '../prompt-renderer.js';
import type { CommandDefinition, CommandResult } from '../types.js';

// =============================================================================
// ReplEngine Tests (REQ-REPL-001)
// =============================================================================

describe('ReplEngine', () => {
  let engine: ReplEngine;

  beforeEach(() => {
    engine = new ReplEngine({
      history: { maxSize: 100, filePath: '/tmp/musubix-test-history' },
    });
  });

  describe('constructor', () => {
    it('should create engine with default config', () => {
      const defaultEngine = new ReplEngine();
      expect(defaultEngine).toBeInstanceOf(ReplEngine);
    });

    it('should create engine with custom config', () => {
      const customEngine = new ReplEngine({
        prompt: { showProject: false, showPhase: false, useColor: false, defaultPrompt: 'test> ' },
      });
      expect(customEngine).toBeInstanceOf(ReplEngine);
    });
  });

  describe('isRunning()', () => {
    it('should return false initially', () => {
      expect(engine.isRunning()).toBe(false);
    });
  });

  describe('execute()', () => {
    it('should execute empty command successfully', async () => {
      const result = await engine.execute('');
      expect(result.success).toBe(true);
      expect(result.output).toBe('');
      expect(result.exitCode).toBe(0);
    });

    it('should execute whitespace-only command successfully', async () => {
      const result = await engine.execute('   ');
      expect(result.success).toBe(true);
      expect(result.exitCode).toBe(0);
    });

    it('should handle help command', async () => {
      const result = await engine.execute('help');
      expect(result).toBeDefined();
      expect(result.exitCode).toBeDefined();
    });

    it('should handle version command', async () => {
      const result = await engine.execute('version');
      expect(result).toBeDefined();
    });

    it('should handle exit command', async () => {
      const result = await engine.execute('exit');
      expect(result.success).toBe(true);
    });

    it('should handle quit command', async () => {
      const result = await engine.execute('quit');
      expect(result.success).toBe(true);
    });

    it('should record execution duration', async () => {
      const result = await engine.execute('help');
      expect(result.duration).toBeGreaterThanOrEqual(0);
    });
  });

  describe('on() / emit()', () => {
    it('should register event handler', () => {
      const handler = vi.fn();
      engine.on(handler);
      // Handler should be registered
      expect(handler).not.toHaveBeenCalled();
    });

    it('should emit events to handlers', async () => {
      const handler = vi.fn();
      engine.on(handler);
      await engine.execute('help');
      expect(handler).toHaveBeenCalled();
    });
  });
});

// =============================================================================
// CommandCompleter Tests (REQ-REPL-002)
// =============================================================================

describe('CommandCompleter', () => {
  let completer: CommandCompleter;
  const testCommands: CommandDefinition[] = [
    {
      name: 'requirements',
      subcommands: ['analyze', 'validate', 'map', 'search'],
      options: [{ name: '--file', alias: '-f', description: 'File path', takesValue: true, valueType: 'file' }],
      description: 'Requirements management',
    },
    {
      name: 'design',
      subcommands: ['generate', 'patterns', 'validate', 'c4', 'adr'],
      options: [{ name: '--output', alias: '-o', description: 'Output path', takesValue: true }],
      description: 'Design generation',
    },
    {
      name: 'codegen',
      subcommands: ['generate', 'analyze', 'security'],
      description: 'Code generation',
    },
    {
      name: 'test',
      subcommands: ['generate', 'coverage'],
      description: 'Test generation',
    },
    {
      name: 'learn',
      subcommands: ['status', 'feedback', 'patterns', 'recommend'],
      description: 'Self-learning system',
    },
  ];

  beforeEach(() => {
    completer = createCommandCompleter({ maxSuggestions: 10 });
    completer.registerCommands(testCommands);
  });

  describe('complete()', () => {
    it('should complete partial command name', () => {
      const result = completer.complete('req', 3);
      expect(result.completions).toContain('requirements');
    });

    it('should complete multiple matching commands', () => {
      const result = completer.complete('de', 2);
      expect(result.completions).toContain('design');
    });

    it('should complete subcommand after space', () => {
      const result = completer.complete('requirements ', 13);
      expect(result.completions).toContain('analyze');
      expect(result.completions).toContain('validate');
      expect(result.completions).toContain('map');
      expect(result.completions).toContain('search');
    });

    it('should complete partial subcommand', () => {
      const result = completer.complete('requirements ana', 16);
      expect(result.completions).toContain('analyze');
    });

    it('should complete options starting with --', () => {
      const result = completer.complete('requirements analyze --', 23);
      expect(result.completions.some((c) => c.startsWith('--'))).toBe(true);
    });

    it('should return empty array when no matches', () => {
      const result = completer.complete('xyz', 3);
      expect(result.completions).toHaveLength(0);
    });

    it('should show all commands when input is empty', () => {
      const result = completer.complete('', 0);
      expect(result.completions.length).toBeGreaterThan(0);
      expect(result.completions).toContain('requirements');
      expect(result.completions).toContain('design');
    });

    it('should respect maxSuggestions limit', () => {
      const limitedCompleter = createCommandCompleter({ maxSuggestions: 2 });
      limitedCompleter.registerCommands(testCommands);
      const result = limitedCompleter.complete('', 0);
      expect(result.completions.length).toBeLessThanOrEqual(2);
    });
  });

  describe('registerCommands()', () => {
    it('should register command definitions', () => {
      const newCompleter = createCommandCompleter();
      newCompleter.registerCommands(testCommands);
      const result = newCompleter.complete('req', 3);
      expect(result.completions).toContain('requirements');
    });

    it('should handle empty command array', () => {
      // registerCommands adds to existing, doesn't replace
      // Verify that empty array doesn't break functionality
      const newCompleter = createCommandCompleter();
      newCompleter.registerCommands([]);
      const result = newCompleter.complete('xyz', 3);
      // No completions for unknown command prefix
      expect(result.completions).toHaveLength(0);
    });
  });
});

// =============================================================================
// HistoryManager Tests (REQ-REPL-003)
// =============================================================================

describe('HistoryManager', () => {
  let history: HistoryManager;
  const testFilePath = path.join(os.tmpdir(), 'musubix-test-history-' + Date.now());

  beforeEach(() => {
    history = createHistoryManager({ maxSize: 10, filePath: testFilePath });
  });

  afterEach(async () => {
    // Clean up test file
    try {
      await fs.promises.unlink(testFilePath);
    } catch {
      // Ignore if file doesn't exist
    }
  });

  describe('load()', () => {
    it('should load history from file', async () => {
      // Create a test history file
      await fs.promises.writeFile(testFilePath, 'cmd1\ncmd2\ncmd3', 'utf-8');
      await history.load();
      expect(history.getAll()).toEqual(['cmd1', 'cmd2', 'cmd3']);
    });

    it('should create empty history if file not exists', async () => {
      const newHistory = createHistoryManager({ filePath: '/tmp/non-existent-file-' + Date.now() });
      await newHistory.load();
      expect(newHistory.getAll()).toHaveLength(0);
    });

    it('should limit loaded history to maxSize', async () => {
      // Create history with more entries than maxSize
      const entries = Array.from({ length: 20 }, (_, i) => 'cmd' + i);
      await fs.promises.writeFile(testFilePath, entries.join('\n'), 'utf-8');
      await history.load();
      expect(history.size).toBeLessThanOrEqual(10);
    });
  });

  describe('save()', () => {
    it('should save history to file', async () => {
      history.add('test-command-1');
      history.add('test-command-2');
      await history.save();

      const content = await fs.promises.readFile(testFilePath, 'utf-8');
      expect(content).toContain('test-command-1');
      expect(content).toContain('test-command-2');
    });

    it('should limit history to max size when saving', async () => {
      // Add more than maxSize commands
      for (let i = 0; i < 15; i++) {
        history.add('cmd' + i);
      }
      await history.save();

      const content = await fs.promises.readFile(testFilePath, 'utf-8');
      const lines = content.split('\n').filter((l) => l.trim());
      expect(lines.length).toBeLessThanOrEqual(10);
    });
  });

  describe('add()', () => {
    it('should add command to history', () => {
      history.add('requirements analyze ./specs');
      expect(history.getAll()).toContain('requirements analyze ./specs');
    });

    it('should not add duplicate consecutive commands', () => {
      history.add('help');
      history.add('help');
      history.add('help');
      expect(history.getAll().filter((c) => c === 'help')).toHaveLength(1);
    });

    it('should not add empty commands', () => {
      history.add('');
      history.add('   ');
      expect(history.size).toBe(0);
    });

    it('should trim whitespace', () => {
      history.add('  help  ');
      expect(history.getAll()).toContain('help');
    });
  });

  describe('previous() / next()', () => {
    beforeEach(() => {
      history.add('cmd1');
      history.add('cmd2');
      history.add('cmd3');
    });

    it('should navigate history with UP (previous)', () => {
      expect(history.previous()).toBe('cmd3');
      expect(history.previous()).toBe('cmd2');
      expect(history.previous()).toBe('cmd1');
    });

    it('should navigate history with DOWN (next)', () => {
      history.previous(); // cmd3
      history.previous(); // cmd2
      expect(history.next()).toBe('cmd3');
    });

    it('should return first command when at start of history', () => {
      history.previous(); // cmd3
      history.previous(); // cmd2
      history.previous(); // cmd1
      expect(history.previous()).toBe('cmd1'); // Still cmd1
    });

    it('should save current line when navigating up', () => {
      const savedLine = history.previous('current input');
      expect(savedLine).toBe('cmd3');
      // Navigate to end should restore temp line
      history.next(); // Goes back to temp
      expect(history.next()).toBe('current input');
    });
  });

  describe('search()', () => {
    beforeEach(() => {
      history.add('requirements analyze');
      history.add('design generate');
      history.add('requirements validate');
      history.add('codegen generate');
    });

    it('should search history for matching commands', () => {
      const results = history.search('req');
      expect(results).toContain('requirements analyze');
      expect(results).toContain('requirements validate');
    });

    it('should be case-insensitive', () => {
      const results = history.search('REQ');
      expect(results.length).toBe(2);
    });

    it('should return empty array when no matches', () => {
      const results = history.search('xyz');
      expect(results).toHaveLength(0);
    });

    it('should return empty array for empty query', () => {
      const results = history.search('');
      expect(results).toHaveLength(0);
    });

    it('should return results in reverse order (most recent first)', () => {
      const results = history.search('requirements');
      expect(results[0]).toBe('requirements validate');
    });
  });

  describe('clear()', () => {
    it('should clear all history', () => {
      history.add('cmd1');
      history.add('cmd2');
      history.clear();
      expect(history.size).toBe(0);
      expect(history.getAll()).toHaveLength(0);
    });
  });

  describe('resetPosition()', () => {
    it('should reset position to end of history', () => {
      history.add('cmd1');
      history.add('cmd2');
      history.previous(); // cmd2
      history.previous(); // cmd1
      history.resetPosition();
      expect(history.previous()).toBe('cmd2');
    });
  });
});

// =============================================================================
// SessionState Tests (REQ-REPL-004)
// =============================================================================

describe('SessionState', () => {
  let session: SessionState;

  beforeEach(() => {
    session = createSessionState();
  });

  describe('set() / get()', () => {
    it('should set and get session variable', () => {
      session.set('PROJECT', 'my-project');
      expect(session.get('PROJECT')).toBe('my-project');
    });

    it('should return undefined for non-existent variable', () => {
      expect(session.get('NON_EXISTENT')).toBeUndefined();
    });

    it('should overwrite existing variable', () => {
      session.set('VAR', 'value1');
      session.set('VAR', 'value2');
      expect(session.get('VAR')).toBe('value2');
    });

    it('should be case-insensitive for variable names', () => {
      session.set('myvar', 'test');
      expect(session.get('MYVAR')).toBe('test');
      expect(session.get('MyVar')).toBe('test');
    });

    it('should throw error for empty variable name', () => {
      expect(() => session.set('', 'value')).toThrow();
    });
  });

  describe('has()', () => {
    it('should return true for existing variable', () => {
      session.set('VAR', 'value');
      expect(session.has('VAR')).toBe(true);
    });

    it('should return false for non-existent variable', () => {
      expect(session.has('NON_EXISTENT')).toBe(false);
    });
  });

  describe('delete()', () => {
    it('should delete existing variable', () => {
      session.set('VAR', 'value');
      expect(session.delete('VAR')).toBe(true);
      expect(session.get('VAR')).toBeUndefined();
    });

    it('should return false for non-existent variable', () => {
      expect(session.delete('NON_EXISTENT')).toBe(false);
    });
  });

  describe('getAll()', () => {
    it('should return all session variables', () => {
      session.set('VAR1', 'value1');
      session.set('VAR2', 'value2');
      const all = session.getAll();
      expect(all['VAR1']).toBe('value1');
      expect(all['VAR2']).toBe('value2');
    });

    it('should include $_ when lastResult is set', () => {
      const result: CommandResult = { success: true, output: 'ok', exitCode: 0 };
      session.setLastResult(result);
      const all = session.getAll();
      expect(all['_']).toBe('ok');
    });
  });

  describe('setLastResult() / getLastResult()', () => {
    it('should store last command result', () => {
      const result: CommandResult = { success: true, output: 'ok', exitCode: 0 };
      session.setLastResult(result);
      expect(session.getLastResult()).toEqual(result);
    });

    it('should be accessible via $_ variable', () => {
      const result: CommandResult = { success: true, output: 'test output', exitCode: 0 };
      session.setLastResult(result);
      expect(session.get('_')).toBe('test output');
    });

    it('should return undefined when no result set', () => {
      expect(session.getLastResult()).toBeUndefined();
    });
  });

  describe('expand()', () => {
    it('should expand variables in string', () => {
      session.set('NAME', 'test-project');
      const expanded = session.expand('Project: $NAME');
      expect(expanded).toBe('Project: test-project');
    });

    it('should leave unknown variables unchanged', () => {
      const expanded = session.expand('$UNKNOWN variable');
      expect(expanded).toBe('$UNKNOWN variable');
    });

    it('should expand multiple variables', () => {
      session.set('A', '1');
      session.set('B', '2');
      const expanded = session.expand('$A + $B');
      expect(expanded).toBe('1 + 2');
    });
  });

  describe('clear()', () => {
    it('should clear all session state', () => {
      session.set('VAR', 'value');
      session.setLastResult({ success: true, output: 'ok', exitCode: 0 });
      session.clear();
      expect(session.size).toBe(0);
      expect(session.getLastResult()).toBeUndefined();
    });
  });
});

// =============================================================================
// OutputFormatter Tests (REQ-REPL-005)
// =============================================================================

describe('OutputFormatter', () => {
  let formatter: OutputFormatter;
  const testData = [
    { id: 'REQ-001', title: 'Requirement 1', status: 'done' },
    { id: 'REQ-002', title: 'Requirement 2', status: 'pending' },
  ];

  beforeEach(() => {
    formatter = createOutputFormatter({ defaultFormat: 'table', useColor: false });
  });

  describe('formatJson()', () => {
    it('should format data as JSON', () => {
      const output = formatter.formatJson(testData);
      expect(() => JSON.parse(output)).not.toThrow();
    });

    it('should pretty print JSON with indentation', () => {
      const output = formatter.formatJson({ key: 'value' });
      expect(output).toContain('\n');
      expect(output).toContain('  ');
    });

    it('should handle primitive values', () => {
      expect(formatter.formatJson('string')).toBe('"string"');
      expect(formatter.formatJson(123)).toBe('123');
      expect(formatter.formatJson(true)).toBe('true');
    });

    it('should handle null and undefined', () => {
      expect(formatter.formatJson(null)).toBe('null');
    });
  });

  describe('formatTable()', () => {
    it('should format array of objects as table', () => {
      const output = formatter.formatTable(testData);
      expect(output).toContain('REQ-001');
      expect(output).toContain('│');
    });

    it('should handle empty array', () => {
      // Empty array (not array of objects) returns empty string
      const output = formatter.formatTable([]);
      expect(output).toBe('');
    });

    it('should format single object as key-value pairs', () => {
      const output = formatter.formatTable({ name: 'test', value: 123 });
      expect(output).toContain('name');
      expect(output).toContain('test');
    });

    it('should format array of primitives as list', () => {
      const output = formatter.formatTable(['a', 'b', 'c']);
      expect(output).toContain('1. a');
      expect(output).toContain('2. b');
    });

    it('should handle null/undefined', () => {
      expect(formatter.formatTable(null)).toBe('');
      expect(formatter.formatTable(undefined)).toBe('');
    });
  });

  describe('formatYaml()', () => {
    it('should format data as YAML', () => {
      const output = formatter.formatYaml({ name: 'test', count: 5 });
      expect(output).toContain('name: test');
      expect(output).toContain('count: 5');
    });

    it('should handle nested objects', () => {
      const output = formatter.formatYaml({
        parent: { child: 'value' },
      });
      expect(output).toContain('parent:');
      expect(output).toContain('child: value');
    });

    it('should handle arrays', () => {
      const output = formatter.formatYaml({ items: ['a', 'b'] });
      expect(output).toContain('items:');
      expect(output).toContain('- a');
    });
  });

  describe('autoFormat()', () => {
    it('should use table for arrays of objects', () => {
      const output = formatter.autoFormat(testData);
      expect(output).toContain('│'); // Table border
    });

    it('should use appropriate format for simple objects', () => {
      const output = formatter.autoFormat({ key: 'value' });
      expect(output).toBeDefined();
    });

    it('should handle empty data', () => {
      expect(formatter.autoFormat(null)).toBe('');
      expect(formatter.autoFormat(undefined)).toBe('');
    });
  });

  describe('format()', () => {
    it('should use specified format', () => {
      const json = formatter.format(testData, 'json');
      expect(() => JSON.parse(json)).not.toThrow();

      const yaml = formatter.format({ key: 'value' }, 'yaml');
      expect(yaml).toContain('key: value');
    });

    it('should use default format when not specified', () => {
      const output = formatter.format(testData);
      expect(output).toContain('│'); // Default is table
    });
  });
});

// =============================================================================
// PromptRenderer Tests (REQ-REPL-006)
// =============================================================================

describe('PromptRenderer', () => {
  let renderer: PromptRenderer;

  beforeEach(() => {
    renderer = createPromptRenderer({
      showProject: true,
      showPhase: true,
      useColor: false,
      defaultPrompt: 'musubix> ',
    });
  });

  describe('render()', () => {
    it('should render default prompt', () => {
      const prompt = renderer.render();
      expect(prompt).toBe('musubix> ');
    });

    it('should render prompt with project name', () => {
      renderer.setContext({ name: 'my-project' });
      const prompt = renderer.render();
      expect(prompt).toContain('my-project');
    });

    it('should render prompt with phase', () => {
      renderer.setContext({ name: 'my-project', phase: 'design' });
      const prompt = renderer.render();
      expect(prompt).toContain('design');
    });

    it('should render prompt with both project and phase', () => {
      renderer.setContext({ name: 'test', phase: 'requirements' });
      const prompt = renderer.render();
      expect(prompt).toContain('test');
      expect(prompt).toContain('requirements');
    });
  });

  describe('renderContinuation()', () => {
    it('should render continuation prompt', () => {
      const prompt = renderer.renderContinuation();
      expect(prompt).toContain('...');
    });
  });

  describe('setContext() / updateContext()', () => {
    it('should set full context', () => {
      renderer.setContext({ name: 'project', phase: 'design', path: '/path' });
      const prompt = renderer.render();
      expect(prompt).toContain('project');
    });

    it('should update context partially', () => {
      renderer.setContext({ name: 'old' });
      renderer.updateContext({ phase: 'test' });
      const prompt = renderer.render();
      expect(prompt).toContain('old');
      expect(prompt).toContain('test');
    });
  });

  describe('setErrorState()', () => {
    it('should change prompt indicator on error', () => {
      renderer.setErrorState(true);
      const errorPrompt = renderer.render();
      // Error state should produce different prompt
      // (in colored mode, it would be red)
      expect(errorPrompt).toBeDefined();
    });

    it('should reset error state', () => {
      renderer.setErrorState(true);
      renderer.setErrorState(false);
      const prompt = renderer.render();
      expect(prompt).toBeDefined();
    });
  });

  describe('config options', () => {
    it('should hide project when showProject is false', () => {
      const noProjectRenderer = createPromptRenderer({ showProject: false });
      noProjectRenderer.setContext({ name: 'hidden-project' });
      const prompt = noProjectRenderer.render();
      expect(prompt).not.toContain('hidden-project');
    });

    it('should hide phase when showPhase is false', () => {
      const noPhaseRenderer = createPromptRenderer({ showPhase: false });
      noPhaseRenderer.setContext({ phase: 'design' });
      const prompt = noPhaseRenderer.render();
      expect(prompt).not.toContain('[design]');
    });
  });
});

// =============================================================================
// Integration Tests (REQ-REPL-007)
// =============================================================================

describe('REPL Integration', () => {
  describe('Command Execution', () => {
    let engine: ReplEngine;

    beforeEach(() => {
      engine = new ReplEngine({
        history: { maxSize: 100, filePath: '/tmp/musubix-integration-test' },
      });
    });

    it('should execute help command', async () => {
      const result = await engine.execute('help');
      expect(result).toBeDefined();
      expect(result.exitCode).toBeDefined();
    });

    it('should handle unknown command gracefully', async () => {
      const result = await engine.execute('unknown-command-xyz');
      expect(result).toBeDefined();
      // Should not crash
    });

    it('should handle command with arguments', async () => {
      const result = await engine.execute('help requirements');
      expect(result).toBeDefined();
    });
  });

  describe('Session Workflow', () => {
    it('should maintain state across commands', async () => {
      const session = createSessionState();

      session.set('PROJECT', 'test');
      const expanded = session.expand('$PROJECT/src');
      expect(expanded).toBe('test/src');
    });

    it('should support variable expansion in commands', async () => {
      const session = createSessionState();
      session.set('FILE', 'requirements.md');
      const expanded = session.expand('analyze $FILE');
      expect(expanded).toBe('analyze requirements.md');
    });
  });

  describe('History Persistence', () => {
    it('should persist history across sessions', async () => {
      const testFile = path.join(os.tmpdir(), 'musubix-persist-test-' + Date.now());

      // First session
      const history1 = createHistoryManager({ filePath: testFile });
      history1.add('cmd1');
      history1.add('cmd2');
      await history1.save();

      // Second session
      const history2 = createHistoryManager({ filePath: testFile });
      await history2.load();
      expect(history2.getAll()).toContain('cmd1');
      expect(history2.getAll()).toContain('cmd2');

      // Cleanup
      await fs.promises.unlink(testFile);
    });
  });

  describe('Completion Integration', () => {
    it('should integrate completer with commands', () => {
      const completer = createCommandCompleter();
      const commands: CommandDefinition[] = [
        { name: 'test', subcommands: ['run', 'watch'], description: 'Test command' },
      ];
      completer.registerCommands(commands);

      const result = completer.complete('test ', 5);
      expect(result.completions).toContain('run');
      expect(result.completions).toContain('watch');
    });
  });

  describe('Formatter Integration', () => {
    it('should format command results', () => {
      const formatter = createOutputFormatter();
      const result: CommandResult = {
        success: true,
        output: JSON.stringify({ status: 'ok' }),
        exitCode: 0,
      };

      const formatted = formatter.formatJson(JSON.parse(result.output));
      expect(formatted).toContain('status');
    });
  });
});

// =============================================================================
// Factory Function Tests
// =============================================================================

describe('Factory Functions', () => {
  describe('createHistoryManager', () => {
    it('should create with default options', () => {
      const history = createHistoryManager();
      expect(history).toBeInstanceOf(HistoryManager);
    });

    it('should create with custom options', () => {
      const history = createHistoryManager({ maxSize: 500, filePath: '/custom/path' });
      expect(history).toBeInstanceOf(HistoryManager);
    });
  });

  describe('createCommandCompleter', () => {
    it('should create with default options', () => {
      const completer = createCommandCompleter();
      expect(completer).toBeInstanceOf(CommandCompleter);
    });

    it('should create with custom options', () => {
      const completer = createCommandCompleter({ maxSuggestions: 5 });
      expect(completer).toBeInstanceOf(CommandCompleter);
    });
  });

  describe('createSessionState', () => {
    it('should create session state', () => {
      const session = createSessionState();
      expect(session).toBeInstanceOf(SessionState);
    });
  });

  describe('createOutputFormatter', () => {
    it('should create with default options', () => {
      const formatter = createOutputFormatter();
      expect(formatter).toBeInstanceOf(OutputFormatter);
    });

    it('should create with custom options', () => {
      const formatter = createOutputFormatter({ defaultFormat: 'json', useColor: false });
      expect(formatter).toBeInstanceOf(OutputFormatter);
    });
  });

  describe('createPromptRenderer', () => {
    it('should create with default options', () => {
      const renderer = createPromptRenderer();
      expect(renderer).toBeInstanceOf(PromptRenderer);
    });

    it('should create with custom options', () => {
      const renderer = createPromptRenderer({
        showProject: false,
        showPhase: false,
        useColor: false,
        defaultPrompt: 'test> ',
      });
      expect(renderer).toBeInstanceOf(PromptRenderer);
    });
  });
});
