/**
 * @fileoverview OWASP A01-A05 Rules Tests
 * @module @nahisaho/musubix-security/tests/rules/owasp
 * @trace TSK-RULE-003
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { Project } from 'ts-morph';
import {
  owaspA01BrokenAccessControl,
  owaspA02CryptographicFailures,
  owaspA03Injection,
  owaspA04InsecureDesign,
  owaspA05SecurityMisconfiguration,
  owaspRulesA01A05,
  DEFAULT_RULE_CONFIG,
  RuleContextBuilder,
} from '../../../src/rules/index.js';
import type { RuleContext, RuleConfig } from '../../../src/rules/types.js';

describe('OWASP A01-A05 Rules', () => {
  let project: Project;
  
  beforeEach(() => {
    project = new Project({
      useInMemoryFileSystem: true,
      compilerOptions: { strict: true },
    });
  });
  
  /**
   * Create a test rule context
   */
  function createTestContext(sourceCode: string, filePath = '/test/app.ts'): RuleContext {
    const sourceFile = project.createSourceFile(filePath, sourceCode, { overwrite: true });
    const config: RuleConfig = {
      ...DEFAULT_RULE_CONFIG,
      severityThreshold: 'info',
    };
    
    return {
      filePath,
      sourceCode,
      sourceFile,
      projectRoot: '/test',
      config,
      previousResults: new Map(),
      report: () => {},
      getOption: <T>(key: string, defaultValue: T) => defaultValue,
    };
  }
  
  describe('owaspRulesA01A05 array', () => {
    it('should contain all 5 OWASP A01-A05 rules', () => {
      expect(owaspRulesA01A05).toHaveLength(5);
      expect(owaspRulesA01A05).toContain(owaspA01BrokenAccessControl);
      expect(owaspRulesA01A05).toContain(owaspA02CryptographicFailures);
      expect(owaspRulesA01A05).toContain(owaspA03Injection);
      expect(owaspRulesA01A05).toContain(owaspA04InsecureDesign);
      expect(owaspRulesA01A05).toContain(owaspA05SecurityMisconfiguration);
    });
  });
  
  describe('OWASP A01 - Broken Access Control', () => {
    it('should have correct metadata', () => {
      expect(owaspA01BrokenAccessControl.id).toBe('owasp-a01-broken-access-control');
      expect(owaspA01BrokenAccessControl.name).toContain('A01:2021');
      expect(owaspA01BrokenAccessControl.defaultSeverity).toBe('critical');
      expect(owaspA01BrokenAccessControl.owasp).toContain('A01:2021');
      expect(owaspA01BrokenAccessControl.cwe).toContain('284');
      expect(owaspA01BrokenAccessControl.references).toBeDefined();
      expect(owaspA01BrokenAccessControl.references!.length).toBeGreaterThan(0);
    });
    
    it('should detect missing auth middleware on sensitive endpoints', async () => {
      const code = `
        import express from 'express';
        const app = express();
        
        app.get('/api/admin/users', (req, res) => {
          res.json({ users: [] });
        });
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA01BrokenAccessControl.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings[0].message).toContain('admin');
      expect(findings[0].severity).toBe('high');
    });
    
    it('should detect IDOR vulnerabilities', async () => {
      const code = `
        app.get('/api/user/:id', async (req, res) => {
          const user = await User.findById(req.params.id);
          res.json(user);
        });
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA01BrokenAccessControl.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('IDOR') || f.message.includes('ownership'))).toBe(true);
    });
    
    it('should detect CORS misconfiguration with wildcard', async () => {
      const code = `
        app.use(cors({
          origin: '*',
          credentials: true
        }));
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA01BrokenAccessControl.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('CORS'))).toBe(true);
    });
    
    it('should detect path traversal', async () => {
      const code = `
        app.get('/file', (req, res) => {
          const filePath = path.join('/uploads', req.query.filename);
          res.sendFile(filePath);
        });
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA01BrokenAccessControl.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('path traversal'))).toBe(true);
    });
    
    it('should detect privileged operations without auth', async () => {
      const code = `
        async function deleteUser(userId: string) {
          await user.destroy();
        }
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA01BrokenAccessControl.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('Privileged operation'))).toBe(true);
    });
    
    it('should pass for endpoints with auth middleware', async () => {
      const code = `
        app.get('/api/admin/users', authMiddleware, (req, res) => {
          res.json({ users: [] });
        });
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA01BrokenAccessControl.analyze(context);
      
      // May still find other issues, but auth middleware pattern should be detected
      const authFindings = findings.filter(f => f.message.includes('lack authentication'));
      expect(authFindings.length).toBe(0);
    });
  });
  
  describe('OWASP A02 - Cryptographic Failures', () => {
    it('should have correct metadata', () => {
      expect(owaspA02CryptographicFailures.id).toBe('owasp-a02-cryptographic-failures');
      expect(owaspA02CryptographicFailures.name).toContain('A02:2021');
      expect(owaspA02CryptographicFailures.defaultSeverity).toBe('critical');
      expect(owaspA02CryptographicFailures.owasp).toContain('A02:2021');
      expect(owaspA02CryptographicFailures.cwe).toContain('327');
    });
    
    it('should detect weak hash algorithms (MD5)', async () => {
      const code = `
        const crypto = require('crypto');
        const hash = crypto.createHash('md5').update(password).digest('hex');
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA02CryptographicFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings[0].message).toContain('MD5');
    });
    
    it('should detect weak hash algorithms (SHA1)', async () => {
      const code = `
        const hash = crypto.createHash('sha1').update(data).digest('hex');
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA02CryptographicFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings[0].message).toContain('SHA1');
    });
    
    it('should detect weak encryption (DES)', async () => {
      const code = `
        const cipher = crypto.createCipheriv('des', key, iv);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA02CryptographicFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('DES'))).toBe(true);
    });
    
    it('should detect hardcoded keys', async () => {
      const code = `
        const secret = 'my-super-secret-key-12345';
        const token = jwt.sign(data, secret);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA02CryptographicFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('hardcoded'))).toBe(true);
    });
    
    it('should detect insecure random', async () => {
      const code = `
        function generateToken() {
          return Math.random().toString(36).substring(7);
        }
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA02CryptographicFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('random') || f.message.includes('Math.random'))).toBe(true);
    });
    
    it('should detect disabled TLS certificate validation', async () => {
      const code = `
        const options = {
          rejectUnauthorized: false
        };
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA02CryptographicFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('TLS'))).toBe(true);
    });
  });
  
  describe('OWASP A03 - Injection', () => {
    it('should have correct metadata', () => {
      expect(owaspA03Injection.id).toBe('owasp-a03-injection');
      expect(owaspA03Injection.name).toContain('A03:2021');
      expect(owaspA03Injection.defaultSeverity).toBe('critical');
      expect(owaspA03Injection.cwe).toContain('89');
      expect(owaspA03Injection.cwe).toContain('78');
    });
    
    it('should detect SQL injection via string concatenation', async () => {
      const code = `
        const query = 'SELECT * FROM users WHERE id = ' + req.params.id;
        db.query(query);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA03Injection.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('SQL'))).toBe(true);
    });
    
    it('should detect SQL injection via template literals', async () => {
      const code = `
        const query = \`SELECT * FROM users WHERE name = '\${req.body.name}'\`;
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA03Injection.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('SQL'))).toBe(true);
    });
    
    it('should detect NoSQL injection', async () => {
      const code = `
        const user = await User.findOne({ username: req.body.username });
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA03Injection.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('NoSQL'))).toBe(true);
    });
    
    it('should detect command injection via exec', async () => {
      const code = `
        const { exec } = require('child_process');
        exec('ls -la ' + req.query.path, callback);
        exec(\`cat \${req.params.file}\`, callback);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA03Injection.analyze(context);
      
      // Command injection might not be detected with simple concatenation
      // Test the exec with template literal pattern which is more reliably detected
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('Command') || f.message.includes('exec'))).toBe(true);
    });
    
    it('should detect code injection via eval', async () => {
      const code = `
        const result = eval(userInput);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA03Injection.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('Code') || f.message.includes('eval'))).toBe(true);
    });
    
    it('should detect template injection', async () => {
      const code = `
        document.innerHTML = req.body.content;
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA03Injection.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('Template') || f.message.includes('XSS'))).toBe(true);
    });
  });
  
  describe('OWASP A04 - Insecure Design', () => {
    it('should have correct metadata', () => {
      expect(owaspA04InsecureDesign.id).toBe('owasp-a04-insecure-design');
      expect(owaspA04InsecureDesign.name).toContain('A04:2021');
      expect(owaspA04InsecureDesign.defaultSeverity).toBe('high');
      expect(owaspA04InsecureDesign.cwe).toContain('501');
    });
    
    it('should detect missing rate limiting on login endpoint', async () => {
      const code = `
        const express = require('express');
        const app = express();
        
        app.post('/api/login', (req, res) => {
          // login logic
        });
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA04InsecureDesign.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('rate limit'))).toBe(true);
    });
    
    it('should detect missing input validation', async () => {
      const code = `
        app.post('/api/user', (req, res) => {
          const data = req.body;
          User.create(data);
        });
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA04InsecureDesign.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('validation'))).toBe(true);
    });
    
    it('should detect insecure defaults', async () => {
      const code = `
        const config = {
          debug: true,
          verbose: true
        };
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA04InsecureDesign.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('Debug mode'))).toBe(true);
    });
    
    it('should detect missing security headers', async () => {
      const code = `
        const express = require('express');
        const app = express();
        
        app.get('/', (req, res) => {
          res.send('Hello');
        });
        
        app.listen(3000);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA04InsecureDesign.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('header') || f.message.includes('Helmet'))).toBe(true);
    });
    
    it('should detect business logic flaws - price from client', async () => {
      const code = `
        app.post('/order', (req, res) => {
          const price = req.body.price;
          createOrder({ price });
        });
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA04InsecureDesign.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('Price') || f.message.includes('business logic'))).toBe(true);
    });
    
    it('should pass when helmet is used', async () => {
      const code = `
        const express = require('express');
        const helmet = require('helmet');
        const app = express();
        
        app.use(helmet());
        
        app.get('/', (req, res) => {
          res.send('Hello');
        });
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA04InsecureDesign.analyze(context);
      
      const headerFindings = findings.filter(f => f.message.includes('header'));
      expect(headerFindings.length).toBe(0);
    });
  });
  
  describe('OWASP A05 - Security Misconfiguration', () => {
    it('should have correct metadata', () => {
      expect(owaspA05SecurityMisconfiguration.id).toBe('owasp-a05-security-misconfiguration');
      expect(owaspA05SecurityMisconfiguration.name).toContain('A05:2021');
      expect(owaspA05SecurityMisconfiguration.defaultSeverity).toBe('high');
      expect(owaspA05SecurityMisconfiguration.cwe).toContain('16');
    });
    
    it('should detect default credentials', async () => {
      const code = `
        const config = {
          username: 'admin',
          password: 'password'
        };
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA05SecurityMisconfiguration.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('default') || f.message.includes('hardcoded'))).toBe(true);
    });
    
    it('should detect verbose error messages', async () => {
      const code = `
        app.use((err, req, res, next) => {
          res.json(err);
        });
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA05SecurityMisconfiguration.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('error'))).toBe(true);
    });
    
    it('should detect stack trace exposure', async () => {
      const code = `
        app.use((err, req, res, next) => {
          res.send(err.stack);
        });
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA05SecurityMisconfiguration.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('Stack trace'))).toBe(true);
    });
    
    it('should detect development settings (localhost)', async () => {
      const code = `
        const API_URL = 'http://localhost:3000/api';
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA05SecurityMisconfiguration.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('localhost') || f.message.includes('Development'))).toBe(true);
    });
    
    it('should detect exposed environment variables', async () => {
      const code = `
        app.get('/config', (req, res) => {
          res.json(process.env);
        });
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA05SecurityMisconfiguration.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('environment') || f.message.includes('process.env'))).toBe(true);
    });
    
    it('should detect unnecessary features (X-Powered-By)', async () => {
      const code = `
        res.setHeader('X-Powered-By', 'Express');
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA05SecurityMisconfiguration.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('X-Powered-By'))).toBe(true);
    });
    
    it('should pass for conditional dev settings', async () => {
      const code = `
        const API_URL = process.env.NODE_ENV === 'production'
          ? 'https://api.production.com'
          : 'http://localhost:3000/api';
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA05SecurityMisconfiguration.analyze(context);
      
      const devFindings = findings.filter(f => f.message.includes('localhost'));
      expect(devFindings.length).toBe(0);
    });
  });
});
