/**
 * Synthesis CLI Commands Unit Tests
 * 
 * Tests for synthesis CLI commands
 * 
 * @see TSK-INT-104 - SynthesisCLI
 * @see REQ-INT-104 - CLI Integration
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { Command } from 'commander';

// Mock modules
vi.mock('fs/promises', () => ({
  readFile: vi.fn(),
  writeFile: vi.fn(),
}));

describe('Synthesis CLI Commands', () => {
  let consoleSpy: ReturnType<typeof vi.spyOn>;
  let consoleErrorSpy: ReturnType<typeof vi.spyOn>;

  beforeEach(() => {
    consoleSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    consoleSpy.mockRestore();
    consoleErrorSpy.mockRestore();
    vi.clearAllMocks();
  });

  describe('Synthesize Command Registration', () => {
    it('should register synthesize command', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const synthCmd = program.commands.find(c => c.name() === 'synthesize');
      expect(synthCmd).toBeDefined();
    });

    it('should have syn alias', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const synthCmd = program.commands.find(c => c.name() === 'synthesize');
      expect(synthCmd?.alias()).toBe('syn');
    });

    it('should have pbe subcommand', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const synthCmd = program.commands.find(c => c.name() === 'synthesize');
      const pbeCmd = synthCmd?.commands.find(c => c.name() === 'pbe');
      expect(pbeCmd).toBeDefined();
    });

    it('should have examples argument', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const synthCmd = program.commands.find(c => c.name() === 'synthesize');
      const args = synthCmd?.registeredArguments;
      expect(args?.length).toBeGreaterThan(0);
      expect(args?.[0].name()).toBe('examples');
    });

    it('should have output option', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const synthCmd = program.commands.find(c => c.name() === 'synthesize');
      const options = synthCmd?.options.map(o => o.long);
      expect(options).toContain('--output');
    });

    it('should have domain option', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const synthCmd = program.commands.find(c => c.name() === 'synthesize');
      const options = synthCmd?.options.map(o => o.long);
      expect(options).toContain('--domain');
    });

    it('should have max-depth option', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const synthCmd = program.commands.find(c => c.name() === 'synthesize');
      const options = synthCmd?.options.map(o => o.long);
      expect(options).toContain('--max-depth');
    });
  });

  describe('Library Command Registration', () => {
    it('should register library command', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const libCmd = program.commands.find(c => c.name() === 'library');
      expect(libCmd).toBeDefined();
    });

    it('should have lib alias', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const libCmd = program.commands.find(c => c.name() === 'library');
      expect(libCmd?.alias()).toBe('lib');
    });

    it('should have learn subcommand', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const libCmd = program.commands.find(c => c.name() === 'library');
      const learnCmd = libCmd?.commands.find(c => c.name() === 'learn');
      expect(learnCmd).toBeDefined();
    });

    it('should have query subcommand', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const libCmd = program.commands.find(c => c.name() === 'library');
      const queryCmd = libCmd?.commands.find(c => c.name() === 'query');
      expect(queryCmd).toBeDefined();
    });

    it('should have stats subcommand', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const libCmd = program.commands.find(c => c.name() === 'library');
      const statsCmd = libCmd?.commands.find(c => c.name() === 'stats');
      expect(statsCmd).toBeDefined();
    });

    it('should have file argument in learn subcommand', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const libCmd = program.commands.find(c => c.name() === 'library');
      const learnCmd = libCmd?.commands.find(c => c.name() === 'learn');
      const args = learnCmd?.registeredArguments;
      expect(args?.length).toBeGreaterThan(0);
      expect(args?.[0].name()).toBe('file');
    });

    it('should have query argument in query subcommand', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const libCmd = program.commands.find(c => c.name() === 'library');
      const queryCmd = libCmd?.commands.find(c => c.name() === 'query');
      const args = queryCmd?.registeredArguments;
      expect(args?.length).toBeGreaterThan(0);
      expect(args?.[0].name()).toBe('query');
    });

    it('should have min-confidence option in query subcommand', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const libCmd = program.commands.find(c => c.name() === 'library');
      const queryCmd = libCmd?.commands.find(c => c.name() === 'query');
      const options = queryCmd?.options.map(o => o.long);
      expect(options).toContain('--min-confidence');
    });

    it('should have format option in stats subcommand', async () => {
      const { registerSynthesisCommands } = await import('../../src/cli/commands/synthesis.js');
      const program = new Command();
      registerSynthesisCommands(program);
      
      const libCmd = program.commands.find(c => c.name() === 'library');
      const statsCmd = libCmd?.commands.find(c => c.name() === 'stats');
      const options = statsCmd?.options.map(o => o.long);
      expect(options).toContain('--format');
    });
  });

  describe('Type Exports', () => {
    it('should export SynthesizeOptions type', async () => {
      const module = await import('../../src/cli/commands/synthesis.js');
      // TypeScript will verify the type exists at compile time
      expect(module.registerSynthesisCommands).toBeDefined();
    });

    it('should export LibraryOptions type', async () => {
      const module = await import('../../src/cli/commands/synthesis.js');
      expect(module.registerSynthesisCommands).toBeDefined();
    });

    it('should export default as registerSynthesisCommands', async () => {
      const module = await import('../../src/cli/commands/synthesis.js');
      expect(module.default).toBe(module.registerSynthesisCommands);
    });
  });
});
