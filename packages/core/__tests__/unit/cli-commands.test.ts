/**
 * CLI Commands Unit Tests
 * Tests for Sprint 6 CLI command implementations
 * TSK-062~080
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { Command } from 'commander';

// Mock modules
vi.mock('fs/promises', () => ({
  readFile: vi.fn(),
  writeFile: vi.fn(),
  mkdir: vi.fn(),
  readdir: vi.fn(),
}));

vi.mock('../../src/validators/ears-validator.js', () => ({
  EARSValidator: vi.fn().mockImplementation(() => ({
    validate: vi.fn().mockReturnValue({
      valid: true,
      pattern: 'event-driven',
      errors: [],
      warnings: [],
    }),
    validateAll: vi.fn().mockReturnValue([]),
  })),
}));

describe('CLI Commands', () => {
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

  describe('Requirements Command', () => {
    it('should have analyze subcommand', async () => {
      const { registerRequirementsCommand } = await import('../../src/cli/commands/requirements.js');
      const program = new Command();
      registerRequirementsCommand(program);
      
      const reqCmd = program.commands.find(c => c.name() === 'requirements');
      expect(reqCmd).toBeDefined();
      
      const analyzeCmd = reqCmd?.commands.find(c => c.name() === 'analyze');
      expect(analyzeCmd).toBeDefined();
    });

    it('should have validate subcommand', async () => {
      const { registerRequirementsCommand } = await import('../../src/cli/commands/requirements.js');
      const program = new Command();
      registerRequirementsCommand(program);
      
      const reqCmd = program.commands.find(c => c.name() === 'requirements');
      const validateCmd = reqCmd?.commands.find(c => c.name() === 'validate');
      expect(validateCmd).toBeDefined();
    });

    it('should have map subcommand', async () => {
      const { registerRequirementsCommand } = await import('../../src/cli/commands/requirements.js');
      const program = new Command();
      registerRequirementsCommand(program);
      
      const reqCmd = program.commands.find(c => c.name() === 'requirements');
      const mapCmd = reqCmd?.commands.find(c => c.name() === 'map');
      expect(mapCmd).toBeDefined();
    });

    it('should have search subcommand', async () => {
      const { registerRequirementsCommand } = await import('../../src/cli/commands/requirements.js');
      const program = new Command();
      registerRequirementsCommand(program);
      
      const reqCmd = program.commands.find(c => c.name() === 'requirements');
      const searchCmd = reqCmd?.commands.find(c => c.name() === 'search');
      expect(searchCmd).toBeDefined();
    });
  });

  describe('Design Command', () => {
    it('should have generate subcommand', async () => {
      const { registerDesignCommand } = await import('../../src/cli/commands/design.js');
      const program = new Command();
      registerDesignCommand(program);
      
      const designCmd = program.commands.find(c => c.name() === 'design');
      expect(designCmd).toBeDefined();
      
      const generateCmd = designCmd?.commands.find(c => c.name() === 'generate');
      expect(generateCmd).toBeDefined();
    });

    it('should have patterns subcommand', async () => {
      const { registerDesignCommand } = await import('../../src/cli/commands/design.js');
      const program = new Command();
      registerDesignCommand(program);
      
      const designCmd = program.commands.find(c => c.name() === 'design');
      const patternsCmd = designCmd?.commands.find(c => c.name() === 'patterns');
      expect(patternsCmd).toBeDefined();
    });

    it('should have validate subcommand', async () => {
      const { registerDesignCommand } = await import('../../src/cli/commands/design.js');
      const program = new Command();
      registerDesignCommand(program);
      
      const designCmd = program.commands.find(c => c.name() === 'design');
      const validateCmd = designCmd?.commands.find(c => c.name() === 'validate');
      expect(validateCmd).toBeDefined();
    });

    it('should have c4 subcommand', async () => {
      const { registerDesignCommand } = await import('../../src/cli/commands/design.js');
      const program = new Command();
      registerDesignCommand(program);
      
      const designCmd = program.commands.find(c => c.name() === 'design');
      const c4Cmd = designCmd?.commands.find(c => c.name() === 'c4');
      expect(c4Cmd).toBeDefined();
    });

    it('should have adr subcommand', async () => {
      const { registerDesignCommand } = await import('../../src/cli/commands/design.js');
      const program = new Command();
      registerDesignCommand(program);
      
      const designCmd = program.commands.find(c => c.name() === 'design');
      const adrCmd = designCmd?.commands.find(c => c.name() === 'adr');
      expect(adrCmd).toBeDefined();
    });
  });

  describe('Codegen Command', () => {
    it('should have generate subcommand', async () => {
      const { registerCodegenCommand } = await import('../../src/cli/commands/codegen.js');
      const program = new Command();
      registerCodegenCommand(program);
      
      const codegenCmd = program.commands.find(c => c.name() === 'codegen');
      expect(codegenCmd).toBeDefined();
      
      const generateCmd = codegenCmd?.commands.find(c => c.name() === 'generate');
      expect(generateCmd).toBeDefined();
    });

    it('should have analyze subcommand', async () => {
      const { registerCodegenCommand } = await import('../../src/cli/commands/codegen.js');
      const program = new Command();
      registerCodegenCommand(program);
      
      const codegenCmd = program.commands.find(c => c.name() === 'codegen');
      const analyzeCmd = codegenCmd?.commands.find(c => c.name() === 'analyze');
      expect(analyzeCmd).toBeDefined();
    });

    it('should have security subcommand', async () => {
      const { registerCodegenCommand } = await import('../../src/cli/commands/codegen.js');
      const program = new Command();
      registerCodegenCommand(program);
      
      const codegenCmd = program.commands.find(c => c.name() === 'codegen');
      const securityCmd = codegenCmd?.commands.find(c => c.name() === 'security');
      expect(securityCmd).toBeDefined();
    });
  });

  describe('Test Command', () => {
    it('should have generate subcommand', async () => {
      const { registerTestCommand } = await import('../../src/cli/commands/test.js');
      const program = new Command();
      registerTestCommand(program);
      
      const testCmd = program.commands.find(c => c.name() === 'test');
      expect(testCmd).toBeDefined();
      
      const generateCmd = testCmd?.commands.find(c => c.name() === 'generate');
      expect(generateCmd).toBeDefined();
    });

    it('should have coverage subcommand', async () => {
      const { registerTestCommand } = await import('../../src/cli/commands/test.js');
      const program = new Command();
      registerTestCommand(program);
      
      const testCmd = program.commands.find(c => c.name() === 'test');
      const coverageCmd = testCmd?.commands.find(c => c.name() === 'coverage');
      expect(coverageCmd).toBeDefined();
    });
  });

  describe('Trace Command', () => {
    it('should have matrix subcommand', async () => {
      const { registerTraceCommand } = await import('../../src/cli/commands/trace.js');
      const program = new Command();
      registerTraceCommand(program);
      
      const traceCmd = program.commands.find(c => c.name() === 'trace');
      expect(traceCmd).toBeDefined();
      
      const matrixCmd = traceCmd?.commands.find(c => c.name() === 'matrix');
      expect(matrixCmd).toBeDefined();
    });

    it('should have impact subcommand', async () => {
      const { registerTraceCommand } = await import('../../src/cli/commands/trace.js');
      const program = new Command();
      registerTraceCommand(program);
      
      const traceCmd = program.commands.find(c => c.name() === 'trace');
      const impactCmd = traceCmd?.commands.find(c => c.name() === 'impact');
      expect(impactCmd).toBeDefined();
    });

    it('should have validate subcommand', async () => {
      const { registerTraceCommand } = await import('../../src/cli/commands/trace.js');
      const program = new Command();
      registerTraceCommand(program);
      
      const traceCmd = program.commands.find(c => c.name() === 'trace');
      const validateCmd = traceCmd?.commands.find(c => c.name() === 'validate');
      expect(validateCmd).toBeDefined();
    });
  });

  describe('Explain Command', () => {
    it('should have why subcommand', async () => {
      const { registerExplainCommand } = await import('../../src/cli/commands/explain.js');
      const program = new Command();
      registerExplainCommand(program);
      
      const explainCmd = program.commands.find(c => c.name() === 'explain');
      expect(explainCmd).toBeDefined();
      
      const whyCmd = explainCmd?.commands.find(c => c.name() === 'why');
      expect(whyCmd).toBeDefined();
    });

    it('should have graph subcommand', async () => {
      const { registerExplainCommand } = await import('../../src/cli/commands/explain.js');
      const program = new Command();
      registerExplainCommand(program);
      
      const explainCmd = program.commands.find(c => c.name() === 'explain');
      const graphCmd = explainCmd?.commands.find(c => c.name() === 'graph');
      expect(graphCmd).toBeDefined();
    });
  });

  describe('Command Registration', () => {
    it('should register all commands to program', async () => {
      const { registerCommands } = await import('../../src/cli/commands/index.js');
      const program = new Command();
      registerCommands(program);
      
      const commandNames = program.commands.map(c => c.name());
      
      // All main commands should be registered
      expect(commandNames).toContain('init');
      expect(commandNames).toContain('requirements');
      expect(commandNames).toContain('design');
      expect(commandNames).toContain('codegen');
      expect(commandNames).toContain('test');
      expect(commandNames).toContain('trace');
      expect(commandNames).toContain('explain');
      expect(commandNames).toContain('skills');
    }, 30000);

    it('should have correct command count', async () => {
      const { registerCommands } = await import('../../src/cli/commands/index.js');
      const program = new Command();
      registerCommands(program);
      
      // 8 main commands + help command
      expect(program.commands.length).toBeGreaterThanOrEqual(8);
    });
  });

  describe('Requirements Command Structure', () => {
    it('should register requirements with 4 subcommands', async () => {
      const { registerRequirementsCommand } = await import('../../src/cli/commands/requirements.js');
      const program = new Command();
      registerRequirementsCommand(program);
      
      const reqCmd = program.commands.find(c => c.name() === 'requirements');
      expect(reqCmd).toBeDefined();
      
      // 5 subcommands: new, analyze, validate, map, search
      const subcommands = reqCmd?.commands.filter(c => c.name() !== 'help');
      expect(subcommands?.length).toBe(5);
    });
  });

  describe('Design Command Structure', () => {
    it('should register design with 6 subcommands', async () => {
      const { registerDesignCommand } = await import('../../src/cli/commands/design.js');
      const program = new Command();
      registerDesignCommand(program);
      
      const designCmd = program.commands.find(c => c.name() === 'design');
      expect(designCmd).toBeDefined();
      
      // 6 subcommands (generate, patterns, validate, c4, adr, traceability) + help
      const subcommands = designCmd?.commands.filter(c => c.name() !== 'help');
      expect(subcommands?.length).toBe(6);
    });
  });

  describe('Codegen Command Structure', () => {
    it('should register codegen with 3 subcommands', async () => {
      const { registerCodegenCommand } = await import('../../src/cli/commands/codegen.js');
      const program = new Command();
      registerCodegenCommand(program);
      
      const codegenCmd = program.commands.find(c => c.name() === 'codegen');
      expect(codegenCmd).toBeDefined();
      
      // 4 subcommands (generate, analyze, security, status) + help
      const subcommands = codegenCmd?.commands.filter(c => c.name() !== 'help');
      expect(subcommands?.length).toBe(4);
    });
  });

  describe('Test Command Structure', () => {
    it('should register test with 2 subcommands', async () => {
      const { registerTestCommand } = await import('../../src/cli/commands/test.js');
      const program = new Command();
      registerTestCommand(program);
      
      const testCmd = program.commands.find(c => c.name() === 'test');
      expect(testCmd).toBeDefined();
      
      // 2 subcommands + help
      const subcommands = testCmd?.commands.filter(c => c.name() !== 'help');
      expect(subcommands?.length).toBe(2);
    });
  });

  describe('Trace Command Structure', () => {
    it('should register trace with 3 subcommands', async () => {
      const { registerTraceCommand } = await import('../../src/cli/commands/trace.js');
      const program = new Command();
      registerTraceCommand(program);
      
      const traceCmd = program.commands.find(c => c.name() === 'trace');
      expect(traceCmd).toBeDefined();
      
      // 4 subcommands (matrix, impact, validate, sync) + help
      const subcommands = traceCmd?.commands.filter(c => c.name() !== 'help');
      expect(subcommands?.length).toBe(4);
    });
  });

  describe('Explain Command Structure', () => {
    it('should register explain with 2 subcommands', async () => {
      const { registerExplainCommand } = await import('../../src/cli/commands/explain.js');
      const program = new Command();
      registerExplainCommand(program);
      
      const explainCmd = program.commands.find(c => c.name() === 'explain');
      expect(explainCmd).toBeDefined();
      
      // 2 subcommands + help
      const subcommands = explainCmd?.commands.filter(c => c.name() !== 'help');
      expect(subcommands?.length).toBe(2);
    });
  });
});
