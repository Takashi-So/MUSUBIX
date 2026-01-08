/**
 * CWE Top 25 (1-13) テスト
 * TSK-RULE-005: CWE Top 25 Most Dangerous Software Weaknesses
 */
import { describe, it, expect } from 'vitest';
import {
  cwe787OutOfBoundsWrite,
  cwe79XSS,
  cwe89SQLInjection,
  cwe416UseAfterFree,
  cwe78CommandInjection,
  cwe20InputValidation,
  cwe125OutOfBoundsRead,
  cwe22PathTraversal,
  cwe352CSRF,
  cwe434FileUpload,
  cwe862MissingAuth,
  cwe476NullDeref,
  cwe287ImproperAuth,
  cweTop25Rules1to13,
} from '../../../rules/cwe/index.js';
import type { RuleContext } from '../../../rules/types.js';

// Helper to create RuleContext for testing
function createContext(code: string, filePath = 'test.ts'): RuleContext {
  return {
    sourceCode: code,
    filePath,
    options: {},
    report: () => {},
  };
}

describe('CWE Top 25 (1-13) Rules', () => {
  describe('CWE-787: Out-of-bounds Write', () => {
    it('should detect Buffer.allocUnsafe', async () => {
      const code = `const buf = Buffer.allocUnsafe(userSize);`;
      const result = await cwe787OutOfBoundsWrite.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-787-oob-write');
    });

    it('should have required properties', () => {
      expect(cwe787OutOfBoundsWrite).toHaveProperty('id', 'cwe-787-oob-write');
      expect(cwe787OutOfBoundsWrite).toHaveProperty('name');
      expect(cwe787OutOfBoundsWrite).toHaveProperty('description');
      expect(cwe787OutOfBoundsWrite).toHaveProperty('analyze');
    });
  });

  describe('CWE-79: XSS', () => {
    it('should detect innerHTML assignment', async () => {
      const code = `element.innerHTML = userInput;`;
      const result = await cwe79XSS.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-79-xss');
    });

    it('should detect document.write', async () => {
      const code = `document.write(data);`;
      const result = await cwe79XSS.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
    });
  });

  describe('CWE-89: SQL Injection', () => {
    it('should detect string concatenation in SQL', async () => {
      const code = `const query = "SELECT * FROM users WHERE id = " + userId;`;
      const result = await cwe89SQLInjection.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-89-sql-injection');
    });
  });

  describe('CWE-416: Use After Free', () => {
    it('should detect stream usage after end', async () => {
      const code = `stream.end(); stream.write(data);`;
      const result = await cwe416UseAfterFree.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-416-use-after-free');
    });
  });

  describe('CWE-78: Command Injection', () => {
    it('should detect exec with user input', async () => {
      const code = `exec("ls " + userInput);`;
      const result = await cwe78CommandInjection.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-78-command-injection');
    });
  });

  describe('CWE-20: Input Validation', () => {
    it('should detect direct body access', async () => {
      const code = `const name = req.body.name;`;
      const result = await cwe20InputValidation.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-20-input-validation');
    });
  });

  describe('CWE-125: Out-of-bounds Read', () => {
    it('should detect array access patterns', async () => {
      const code = `const val = buffer.readUInt32LE(offset);`;
      const result = await cwe125OutOfBoundsRead.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-125-oob-read');
    });
  });

  describe('CWE-22: Path Traversal', () => {
    it('should detect path.join with user input', async () => {
      const code = `const filePath = path.join(uploadDir, req.params.filename);`;
      const result = await cwe22PathTraversal.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-22-path-traversal');
    });
  });

  describe('CWE-352: CSRF', () => {
    it('should detect POST endpoint without CSRF', async () => {
      const code = `app.post('/transfer', (req, res) => { transfer(req.body); });`;
      const result = await cwe352CSRF.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-352-csrf');
    });
  });

  describe('CWE-434: Unrestricted File Upload', () => {
    it('should detect missing file type validation', async () => {
      const code = `const filename = req.file.originalname; fs.writeFileSync(filename, data);`;
      const result = await cwe434FileUpload.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-434-file-upload');
    });
  });

  describe('CWE-862: Missing Authorization', () => {
    it('should detect missing auth middleware', async () => {
      const code = `app.delete('/admin/user/:id', (req, res) => { deleteUser(req.params.id); });`;
      const result = await cwe862MissingAuth.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-862-missing-auth');
    });
  });

  describe('CWE-476: NULL Pointer Dereference', () => {
    it('should detect chained call after find', async () => {
      const code = `const name = db.findOne(query).name;`;
      const result = await cwe476NullDeref.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-476-null-deref');
    });
  });

  describe('CWE-287: Improper Authentication', () => {
    it('should detect hardcoded password check', async () => {
      const code = `if (password === 'admin123') { login(); }`;
      const result = await cwe287ImproperAuth.analyze(createContext(code));
      expect(result.length).toBeGreaterThan(0);
      expect(result[0].ruleId).toBe('cwe-287-improper-auth');
    });
  });

  describe('cweTop25Rules1to13 array', () => {
    it('should contain exactly 13 rules', () => {
      expect(cweTop25Rules1to13).toHaveLength(13);
    });

    it('should have all rules with valid structure', () => {
      for (const rule of cweTop25Rules1to13) {
        expect(rule).toHaveProperty('id');
        expect(rule).toHaveProperty('name');
        expect(rule).toHaveProperty('description');
        expect(rule).toHaveProperty('defaultSeverity');
        expect(rule).toHaveProperty('category');
        expect(rule).toHaveProperty('analyze');
        expect(typeof rule.analyze).toBe('function');
      }
    });

    it('should have CWE in tags for all rules', () => {
      for (const rule of cweTop25Rules1to13) {
        expect(rule.tags).toContain('cwe');
      }
    });
  });
});
