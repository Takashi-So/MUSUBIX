/**
 * @fileoverview OWASP A06-A10 Rules Tests
 * @module @nahisaho/musubix-security/tests/rules/owasp
 * @trace TSK-RULE-004
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { Project } from 'ts-morph';
import {
  owaspA06VulnerableComponents,
  owaspA07AuthFailures,
  owaspA08IntegrityFailures,
  owaspA09LoggingFailures,
  owaspA10SSRF,
  owaspRulesA06A10,
  owaspTop10Rules,
  DEFAULT_RULE_CONFIG,
} from '../../../src/rules/index.js';
import type { RuleContext, RuleConfig } from '../../../src/rules/types.js';

describe('OWASP A06-A10 Rules', () => {
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
  
  describe('owaspRulesA06A10 array', () => {
    it('should contain all 5 OWASP A06-A10 rules', () => {
      expect(owaspRulesA06A10).toHaveLength(5);
      expect(owaspRulesA06A10).toContain(owaspA06VulnerableComponents);
      expect(owaspRulesA06A10).toContain(owaspA07AuthFailures);
      expect(owaspRulesA06A10).toContain(owaspA08IntegrityFailures);
      expect(owaspRulesA06A10).toContain(owaspA09LoggingFailures);
      expect(owaspRulesA06A10).toContain(owaspA10SSRF);
    });
    
    it('should have complete owaspTop10Rules array', () => {
      expect(owaspTop10Rules).toHaveLength(10);
    });
  });
  
  describe('OWASP A06 - Vulnerable and Outdated Components', () => {
    it('should have correct metadata', () => {
      expect(owaspA06VulnerableComponents.id).toBe('owasp-a06-vulnerable-components');
      expect(owaspA06VulnerableComponents.name).toContain('A06:2021');
      expect(owaspA06VulnerableComponents.owasp).toContain('A06:2021');
      expect(owaspA06VulnerableComponents.cwe).toContain('1104');
    });
    
    it('should detect deprecated packages (moment)', async () => {
      const code = `
        const moment = require('moment');
        const date = moment().format('YYYY-MM-DD');
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA06VulnerableComponents.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('moment'))).toBe(true);
    });
    
    it('should detect deprecated crypto.createCipher', async () => {
      const code = `
        const crypto = require('crypto');
        const cipher = crypto.createCipher('aes-256-cbc', key);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA06VulnerableComponents.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('createCipher'))).toBe(true);
    });
    
    it('should detect missing SRI in HTML', async () => {
      const code = `
        <script src="https://cdn.example.com/jquery.min.js"></script>
      `;
      
      const context = createTestContext(code, '/test/index.html');
      const findings = await owaspA06VulnerableComponents.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('SRI') || f.message.includes('integrity'))).toBe(true);
    });
    
    it('should detect HTTP CDN usage', async () => {
      const code = `
        const cdnUrl = 'http://cdn.example.com/lib.js';
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA06VulnerableComponents.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('HTTP'))).toBe(true);
    });
  });
  
  describe('OWASP A07 - Identification and Authentication Failures', () => {
    it('should have correct metadata', () => {
      expect(owaspA07AuthFailures.id).toBe('owasp-a07-auth-failures');
      expect(owaspA07AuthFailures.name).toContain('A07:2021');
      expect(owaspA07AuthFailures.defaultSeverity).toBe('critical');
      expect(owaspA07AuthFailures.cwe).toContain('287');
    });
    
    it('should detect weak password policy', async () => {
      const code = `
        const passwordPolicy = {
          minLength: 4
        };
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA07AuthFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('password') || f.message.includes('short'))).toBe(true);
    });
    
    it('should detect insecure cookie settings', async () => {
      const code = `
        app.use(session({
          cookie: {
            secure: false
          }
        }));
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA07AuthFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('secure') || f.message.includes('cookie'))).toBe(true);
    });
    
    it('should detect password in logs', async () => {
      const code = `
        console.log('User credentials:', { email, password });
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA07AuthFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('Credential') || f.message.includes('password'))).toBe(true);
    });
    
    it('should detect JWT without verification', async () => {
      const code = `
        const payload = jwt.decode(token);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA07AuthFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('JWT') || f.message.includes('verification'))).toBe(true);
    });
    
    it('should detect token in localStorage', async () => {
      const code = `
        localStorage.setItem('authToken', token);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA07AuthFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('localStorage'))).toBe(true);
    });
  });
  
  describe('OWASP A08 - Software and Data Integrity Failures', () => {
    it('should have correct metadata', () => {
      expect(owaspA08IntegrityFailures.id).toBe('owasp-a08-integrity-failures');
      expect(owaspA08IntegrityFailures.name).toContain('A08:2021');
      expect(owaspA08IntegrityFailures.cwe).toContain('502');
    });
    
    it('should detect YAML deserialization with user input', async () => {
      const code = `
        const yaml = require('js-yaml');
        const data = yaml.load(req.body.yamlData);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA08IntegrityFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('deserialize') || f.message.includes('YAML'))).toBe(true);
    });
    
    it('should detect curl piped to shell', async () => {
      const code = `
        // Run: curl https://example.com/install.sh | bash
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA08IntegrityFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('curl') || f.message.includes('verification'))).toBe(true);
    });
    
    it('should detect object spread with user input', async () => {
      const code = `
        const user = { ...req.body };
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA08IntegrityFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('Object') || f.message.includes('injection'))).toBe(true);
    });
    
    it('should detect prototype pollution risk', async () => {
      const code = `
        obj['__proto__'].polluted = true;
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA08IntegrityFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('prototype') || f.message.includes('Prototype'))).toBe(true);
    });
  });
  
  describe('OWASP A09 - Security Logging and Monitoring Failures', () => {
    it('should have correct metadata', () => {
      expect(owaspA09LoggingFailures.id).toBe('owasp-a09-logging-failures');
      expect(owaspA09LoggingFailures.name).toContain('A09:2021');
      expect(owaspA09LoggingFailures.cwe).toContain('778');
    });
    
    it('should detect sensitive data in logs', async () => {
      const code = `
        logger.info('Login attempt', { password: userPassword });
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA09LoggingFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('Sensitive') || f.message.includes('password'))).toBe(true);
    });
    
    it('should detect API key in logs', async () => {
      const code = `
        console.log('API key:', apiKey);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA09LoggingFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('API') || f.message.includes('Sensitive'))).toBe(true);
    });
    
    it('should detect log injection', async () => {
      const code = `
        logger.info(req.body.username);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA09LoggingFailures.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('injection') || f.message.includes('User input'))).toBe(true);
    });
  });
  
  describe('OWASP A10 - Server-Side Request Forgery (SSRF)', () => {
    it('should have correct metadata', () => {
      expect(owaspA10SSRF.id).toBe('owasp-a10-ssrf');
      expect(owaspA10SSRF.name).toContain('A10:2021');
      expect(owaspA10SSRF.defaultSeverity).toBe('critical');
      expect(owaspA10SSRF.cwe).toContain('918');
    });
    
    it('should detect fetch with user-controlled URL', async () => {
      const code = `
        const response = await fetch(req.body.url);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA10SSRF.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('SSRF') || f.message.includes('user-controlled'))).toBe(true);
    });
    
    it('should detect axios with user URL', async () => {
      const code = `
        const data = await axios.get(targetUrl);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA10SSRF.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('SSRF') || f.message.includes('axios'))).toBe(true);
    });
    
    it('should detect AWS metadata endpoint', async () => {
      const code = `
        const url = req.body.url;
        fetch(url); // Can be used to access 169.254.169.254
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA10SSRF.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
    });
    
    it('should detect internal network access', async () => {
      const code = `
        const internalApi = 'http://internal.corp.com/api';
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA10SSRF.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('internal'))).toBe(true);
    });
    
    it('should detect file protocol usage', async () => {
      const code = `
        const fileUrl = 'file:///etc/passwd';
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA10SSRF.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('file://') || f.message.includes('Local'))).toBe(true);
    });
    
    it('should detect open redirect', async () => {
      const code = `
        res.redirect(req.query.returnUrl);
      `;
      
      const context = createTestContext(code);
      const findings = await owaspA10SSRF.analyze(context);
      
      expect(findings.length).toBeGreaterThan(0);
      expect(findings.some(f => f.message.includes('redirect'))).toBe(true);
    });
  });
});
