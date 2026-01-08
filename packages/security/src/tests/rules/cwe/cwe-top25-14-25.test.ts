/**
 * CWE Top 25 (14-25) テスト
 * TSK-RULE-006: CWE Top 25 Most Dangerous Software Weaknesses
 */
import { describe, it, expect } from 'vitest';
import {
  cwe190IntegerOverflow,
  cwe502Deserialization,
  cwe77CommandInjection,
  cwe119BufferOverflow,
  cwe798HardcodedCredentials,
  cwe918SSRF,
  cwe306MissingAuthCritical,
  cwe362RaceCondition,
  cwe269ImproperPrivilege,
  cwe94CodeInjection,
  cwe863IncorrectAuth,
  cwe276DefaultPermissions,
  cweTop25Rules14to25,
} from '../../../rules/cwe/index.js';
import type { RuleContext } from '../../../rules/types.js';

function createContext(code: string, filePath = 'test.ts'): RuleContext {
  return { sourceCode: code, filePath, options: {}, report: () => {} };
}

describe('CWE Top 25 (14-25) Rules', () => {
  describe('CWE-190: Integer Overflow', () => {
    it('should detect large bit shift', async () => {
      const code = `const val = x << 32;`;
      const result = await cwe190IntegerOverflow.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-190-integer-overflow');
    });
  });

  describe('CWE-502: Deserialization', () => {
    it('should detect JSON.parse on request', async () => {
      const code = `const data = JSON.parse(req.body);`;
      const result = await cwe502Deserialization.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-502-deserialization');
    });
  });

  describe('CWE-77: Command Injection', () => {
    it('should detect child_process exec', async () => {
      const code = `const { exec } = require('child_process'); exec(cmd);`;
      const result = await cwe77CommandInjection.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-77-command-injection');
    });
  });

  describe('CWE-119: Buffer Overflow', () => {
    it('should detect Buffer copy', async () => {
      const code = `Buffer.from(data).copy(target);`;
      const result = await cwe119BufferOverflow.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-119-buffer-overflow');
    });
  });

  describe('CWE-798: Hardcoded Credentials', () => {
    it('should detect hardcoded password', async () => {
      const code = `const password = 'secret123';`;
      const result = await cwe798HardcodedCredentials.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-798-hardcoded-credentials');
    });
  });

  describe('CWE-918: SSRF', () => {
    it('should detect fetch with request URL', async () => {
      const code = `fetch(req.body.url);`;
      const result = await cwe918SSRF.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-918-ssrf');
    });
  });

  describe('CWE-306: Missing Auth Critical', () => {
    it('should detect admin route', async () => {
      const code = `app.post('/admin/delete', handler);`;
      const result = await cwe306MissingAuthCritical.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-306-missing-auth-critical');
    });
  });

  describe('CWE-362: Race Condition', () => {
    it('should detect global state modification', async () => {
      const code = `global.counter = 0;`;
      const result = await cwe362RaceCondition.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-362-race-condition');
    });
  });

  describe('CWE-269: Improper Privilege', () => {
    it('should detect direct admin role', async () => {
      const code = `user.role = 'admin';`;
      const result = await cwe269ImproperPrivilege.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-269-improper-privilege');
    });
  });

  describe('CWE-94: Code Injection', () => {
    it('should detect eval', async () => {
      const code = `eval(userCode);`;
      const result = await cwe94CodeInjection.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-94-code-injection');
    });
  });

  describe('CWE-863: Incorrect Authorization', () => {
    it('should detect findById with params', async () => {
      const code = `const user = await User.findById(req.params.id);`;
      const result = await cwe863IncorrectAuth.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-863-incorrect-auth');
    });
  });

  describe('CWE-276: Default Permissions', () => {
    it('should detect chmod 777', async () => {
      const code = `fs.chmod(file, 0o777);`;
      const result = await cwe276DefaultPermissions.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-276-default-permissions');
    });
  });

  describe('cweTop25Rules14to25 array', () => {
    it('should contain exactly 12 rules', () => {
      expect(cweTop25Rules14to25).toHaveLength(12);
    });

    it('should have all rules with valid structure', () => {
      for (const rule of cweTop25Rules14to25) {
        expect(rule).toHaveProperty('id');
        expect(rule).toHaveProperty('name');
        expect(rule).toHaveProperty('analyze');
        expect(typeof rule.analyze).toBe('function');
      }
    });
  });
});
