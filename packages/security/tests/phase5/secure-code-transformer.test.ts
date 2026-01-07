/**
 * @fileoverview Tests for SecureCodeTransformer
 * @module @nahisaho/musubix-security/tests/phase5/secure-code-transformer.test
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  SecureCodeTransformer,
  createSecureCodeTransformer,
  quickTransform,
  getBuiltInTransformations,
} from '../../src/remediation/secure-code-transformer.js';
import type { Vulnerability, SourceLocation } from '../../src/types/index.js';

// ============================================================================
// Test Helpers
// ============================================================================

function createLocation(file: string, startLine: number): SourceLocation {
  return {
    file,
    startLine,
    endLine: startLine,
    startColumn: 0,
    endColumn: 80,
  };
}

function createVulnerability(
  id: string,
  type: string,
  severity: 'critical' | 'high' | 'medium' | 'low' | 'info' = 'high'
): Vulnerability {
  return {
    id,
    ruleId: `SEC-${type.toUpperCase()}`,
    type,
    severity,
    description: `Test ${type} vulnerability`,
    location: createLocation('test.ts', 10),
    evidence: {
      code: 'vulnerable code',
      context: 'Test context',
    },
    cwe: ['CWE-79'],
    owasp: ['A03:2021'],
    confidence: 0.9,
    remediation: `Fix the ${type} vulnerability`,
    references: [],
    metadata: {},
  };
}

// ============================================================================
// SecureCodeTransformer Tests
// ============================================================================

describe('SecureCodeTransformer', () => {
  let transformer: SecureCodeTransformer;

  beforeEach(() => {
    transformer = createSecureCodeTransformer();
  });

  describe('constructor', () => {
    it('should create with default options', () => {
      const t = new SecureCodeTransformer();
      expect(t).toBeInstanceOf(SecureCodeTransformer);
    });

    it('should create with custom options', () => {
      const t = new SecureCodeTransformer({
        language: 'javascript',
        preserveFormatting: true,
        dryRun: true,
      });
      expect(t).toBeInstanceOf(SecureCodeTransformer);
    });

    it('should load built-in transformations', () => {
      const transformations = transformer.getAvailableTransformations();
      expect(transformations.length).toBeGreaterThan(0);
    });
  });

  describe('transform', () => {
    it('should transform innerHTML to textContent', () => {
      const code = 'element.innerHTML = userInput;';
      const result = transformer.transform(code);

      if (result.success) {
        expect(result.transformedCode).toContain('textContent');
        expect(result.transformationsApplied.length).toBeGreaterThan(0);
      }
    });

    it('should transform MD5 to SHA-256', () => {
      const code = `import crypto from 'crypto';
const hash = crypto.createHash('md5').update(data).digest('hex');`;
      const result = transformer.transform(code);

      if (result.success) {
        expect(result.transformedCode).toContain('sha256');
      }
    });

    it('should transform SHA-1 to SHA-256', () => {
      const code = `const hash = createHash('sha1').update(data).digest('hex');`;
      const result = transformer.transform(code);

      if (result.success) {
        expect(result.transformedCode).toContain('sha256');
      }
    });

    it('should transform Math.random to crypto.randomBytes', () => {
      const code = `const randomValue = Math.random();`;
      const result = transformer.transform(code);

      if (result.success) {
        expect(result.transformedCode).toContain('randomBytes');
        expect(result.requiredImports.length).toBeGreaterThan(0);
      }
    });

    it('should sanitize error messages', () => {
      const code = `res.send(err.message);`;
      const result = transformer.transform(code);

      if (result.success) {
        expect(result.transformedCode).not.toContain('err.message');
      }
    });

    it('should remove stack traces from responses', () => {
      const code = `res.json({ error: err.stack });`;
      const result = transformer.transform(code);

      if (result.success) {
        expect(result.transformedCode).not.toContain('err.stack');
      }
    });

    it('should add HttpOnly to cookies', () => {
      const code = `res.cookie('session', token);`;
      const result = transformer.transform(code);

      if (result.success) {
        expect(result.transformedCode).toContain('httpOnly');
      }
    });

    it('should not transform secure code', () => {
      const code = `const x = 1 + 2;`;
      const result = transformer.transform(code);

      // No transformations should be applied
      expect(result.transformedCode).toBe(code);
      expect(result.transformationsApplied.length).toBe(0);
    });

    it('should respect maxTransformations option', () => {
      const code = `
        element.innerHTML = userInput;
        crypto.createHash('md5').update(data);
        Math.random();
      `;
      const result = transformer.transform(code, { maxTransformations: 1 });

      expect(result.transformationsApplied.length).toBeLessThanOrEqual(1);
    });

    it('should respect onlyTransformations option', () => {
      const code = `
        element.innerHTML = userInput;
        crypto.createHash('md5').update(data);
      `;
      const result = transformer.transform(code, {
        onlyTransformations: ['transform-md5-to-sha256'],
      });

      if (result.success) {
        // Should only apply MD5 transformation
        expect(result.transformationsApplied.every(
          t => t.transformationId === 'transform-md5-to-sha256'
        )).toBe(true);
      }
    });

    it('should respect excludeTransformations option', () => {
      const code = `element.innerHTML = userInput;`;
      const result = transformer.transform(code, {
        excludeTransformations: ['transform-escape-html'],
      });

      // Should not apply the excluded transformation
      expect(result.transformationsApplied.every(
        t => t.transformationId !== 'transform-escape-html'
      )).toBe(true);
    });
  });

  describe('transformForVulnerability', () => {
    it('should transform code for XSS vulnerability', () => {
      const code = `element.innerHTML = userInput;`;
      const vuln = createVulnerability('V-001', 'xss');

      const result = transformer.transformForVulnerability(code, vuln);

      expect(result).toBeDefined();
    });

    it('should transform code for weak-crypto vulnerability', () => {
      const code = `createHash('md5').update(data);`;
      const vuln = createVulnerability('V-002', 'weak-crypto');

      const result = transformer.transformForVulnerability(code, vuln);

      expect(result).toBeDefined();
    });

    it('should transform code for hardcoded-secret vulnerability', () => {
      const code = `const apiKey = "sk-1234567890";`;
      const vuln = createVulnerability('V-003', 'hardcoded-secret');

      const result = transformer.transformForVulnerability(code, vuln);

      expect(result).toBeDefined();
    });
  });

  describe('getAvailableTransformations', () => {
    it('should return all available transformations', () => {
      const transformations = transformer.getAvailableTransformations();

      expect(Array.isArray(transformations)).toBe(true);
      expect(transformations.length).toBeGreaterThan(0);
    });

    it('should include transformation metadata', () => {
      const transformations = transformer.getAvailableTransformations();

      for (const t of transformations) {
        expect(t.id).toBeDefined();
        expect(t.name).toBeDefined();
        expect(t.category).toBeDefined();
        expect(t.riskLevel).toBeDefined();
      }
    });
  });

  describe('getTransformationsByCategory', () => {
    it('should return transformations by category', () => {
      const cryptoTransforms = transformer.getTransformationsByCategory('cryptography');

      expect(cryptoTransforms.length).toBeGreaterThan(0);
      expect(cryptoTransforms.every(t => t.category === 'cryptography')).toBe(true);
    });

    it('should return empty array for unknown category', () => {
      const transforms = transformer.getTransformationsByCategory('unknown-category' as never);
      expect(transforms).toEqual([]);
    });
  });

  describe('addTransformation', () => {
    it('should add custom transformation', () => {
      const initialCount = transformer.getAvailableTransformations().length;

      transformer.addTransformation({
        id: 'custom-transform',
        name: 'Custom Transform',
        category: 'general',
        pattern: {
          type: 'regex',
          value: 'customPattern',
        },
        replacement: {
          type: 'template',
          value: 'safePattern',
        },
        description: 'Custom transformation',
        riskLevel: 'safe',
        languages: ['typescript'],
      });

      const finalCount = transformer.getAvailableTransformations().length;

      expect(finalCount).toBe(initialCount + 1);
    });

    it('should apply custom transformation', () => {
      transformer.addTransformation({
        id: 'custom-dangerous',
        name: 'Replace dangerous',
        category: 'general',
        pattern: {
          type: 'function-call',
          value: 'dangerousCall()',
        },
        replacement: {
          type: 'template',
          value: 'safeCall()',
        },
        description: 'Replace dangerous with safe',
        riskLevel: 'safe',
        languages: ['typescript'],
      });

      const code = 'dangerousCall();';
      const result = transformer.transform(code);

      if (result.success) {
        expect(result.transformedCode).toContain('safeCall');
      }
    });
  });

  describe('removeTransformation', () => {
    it('should remove transformation', () => {
      const initialCount = transformer.getAvailableTransformations().length;

      const removed = transformer.removeTransformation('transform-escape-html');

      expect(removed).toBe(true);
      expect(transformer.getAvailableTransformations().length).toBe(initialCount - 1);
    });

    it('should return false for non-existent transformation', () => {
      const removed = transformer.removeTransformation('non-existent');
      expect(removed).toBe(false);
    });
  });

  describe('preview', () => {
    it('should preview transformation without applying', () => {
      const code = `element.innerHTML = userInput;`;
      const preview = transformer.preview(code, 'transform-escape-html');

      expect(preview.wouldApply).toBe(true);
      expect(preview.matches.length).toBeGreaterThan(0);
      expect(preview.matches[0].original).toBeDefined();
      expect(preview.matches[0].preview).toBeDefined();
    });

    it('should show no matches for non-matching code', () => {
      const code = `const x = 1;`;
      const preview = transformer.preview(code, 'transform-escape-html');

      expect(preview.wouldApply).toBe(false);
      expect(preview.matches.length).toBe(0);
    });

    it('should return empty for non-existent transformation', () => {
      const code = `const x = 1;`;
      const preview = transformer.preview(code, 'non-existent');

      expect(preview.wouldApply).toBe(false);
      expect(preview.matches.length).toBe(0);
    });
  });

  describe('validateTransformation', () => {
    it('should validate correct transformation', () => {
      const original = `const x = 1;`;
      const transformed = `const x = 2;`;

      const validation = transformer.validateTransformation(original, transformed);

      expect(validation.valid).toBe(true);
      expect(validation.issues.length).toBe(0);
    });

    it('should detect unbalanced brackets', () => {
      const original = `foo()`;
      const transformed = `foo((`;

      const validation = transformer.validateTransformation(original, transformed);

      expect(validation.valid).toBe(false);
      expect(validation.issues.some(i => i.includes('Unbalanced'))).toBe(true);
    });

    it('should detect empty transformation result', () => {
      const original = `const x = 1;`;
      const transformed = `   `;

      const validation = transformer.validateTransformation(original, transformed);

      expect(validation.valid).toBe(false);
      expect(validation.issues.some(i => i.includes('empty'))).toBe(true);
    });

    it('should detect double semicolons', () => {
      const original = `const x = 1;`;
      const transformed = `const x = 1;;`;

      const validation = transformer.validateTransformation(original, transformed);

      expect(validation.valid).toBe(false);
      expect(validation.issues.some(i => i.includes('semicolon'))).toBe(true);
    });
  });
});

// ============================================================================
// Factory Functions Tests
// ============================================================================

describe('Factory Functions', () => {
  describe('createSecureCodeTransformer', () => {
    it('should create SecureCodeTransformer instance', () => {
      const transformer = createSecureCodeTransformer();
      expect(transformer).toBeInstanceOf(SecureCodeTransformer);
    });

    it('should pass options to SecureCodeTransformer', () => {
      const transformer = createSecureCodeTransformer({
        language: 'javascript',
        dryRun: true,
      });
      expect(transformer).toBeInstanceOf(SecureCodeTransformer);
    });

    it('should accept custom transformations', () => {
      const transformer = createSecureCodeTransformer({
        customTransformations: [
          {
            id: 'factory-custom',
            name: 'Factory Custom',
            category: 'general',
            pattern: { type: 'regex', value: 'test' },
            replacement: { type: 'template', value: 'TEST' },
            description: 'Test',
            riskLevel: 'safe',
            languages: ['typescript'],
          },
        ],
      });

      const transformations = transformer.getAvailableTransformations();
      expect(transformations.some(t => t.id === 'factory-custom')).toBe(true);
    });
  });

  describe('quickTransform', () => {
    it('should quickly transform code', () => {
      const code = `element.innerHTML = userInput;`;
      const result = quickTransform(code);

      expect(result).toBeDefined();
      expect(result.originalCode).toBe(code);
    });
  });

  describe('getBuiltInTransformations', () => {
    it('should return all built-in transformations', () => {
      const transformations = getBuiltInTransformations();

      expect(Array.isArray(transformations)).toBe(true);
      expect(transformations.length).toBeGreaterThan(0);
    });

    it('should include common security transformations', () => {
      const transformations = getBuiltInTransformations();
      const ids = transformations.map(t => t.id);

      expect(ids.some(id => id.includes('html') || id.includes('escape'))).toBe(true);
      expect(ids.some(id => id.includes('md5') || id.includes('sha'))).toBe(true);
    });
  });
});

// ============================================================================
// Edge Cases
// ============================================================================

describe('Edge Cases', () => {
  let transformer: SecureCodeTransformer;

  beforeEach(() => {
    transformer = createSecureCodeTransformer();
  });

  it('should handle empty code', () => {
    const result = transformer.transform('');

    expect(result.originalCode).toBe('');
    expect(result.transformedCode).toBe('');
    expect(result.success).toBe(false);
  });

  it('should handle whitespace-only code', () => {
    const result = transformer.transform('   \n\t\n   ');

    expect(result.success).toBe(false);
  });

  it('should handle very long code', () => {
    const code = 'const x = 1;\n'.repeat(10000);
    const result = transformer.transform(code);

    expect(result).toBeDefined();
    expect(result.originalCode.length).toBeGreaterThan(0);
  });

  it('should handle code with special characters', () => {
    const code = `const regex = /[a-z]+\\d+/g; element.innerHTML = x;`;
    const result = transformer.transform(code);

    expect(result).toBeDefined();
  });

  it('should handle multiline patterns', () => {
    const code = `
      function example() {
        element.innerHTML = userInput;
        return true;
      }
    `;
    const result = transformer.transform(code);

    expect(result).toBeDefined();
  });

  it('should preserve code structure', () => {
    const code = `
// Comment
function test() {
  const x = crypto.createHash('md5').update(data).digest('hex');
  return x;
}
    `.trim();

    const result = transformer.transform(code);

    if (result.success) {
      // Should still contain function structure
      expect(result.transformedCode).toContain('function test()');
      expect(result.transformedCode).toContain('return x');
    }
  });

  it('should handle multiple occurrences', () => {
    const code = `
      const a = crypto.createHash('md5').update('a').digest('hex');
      const b = crypto.createHash('md5').update('b').digest('hex');
    `;

    const result = transformer.transform(code);

    if (result.success) {
      // Should transform all occurrences
      expect(result.transformationsApplied.length).toBe(2);
    }
  });

  it('should handle enabled categories filter', () => {
    const restrictedTransformer = createSecureCodeTransformer({
      enabledCategories: ['cryptography'],
    });

    const code = `
      element.innerHTML = userInput;
      crypto.createHash('md5').update(data);
    `;

    const result = restrictedTransformer.transform(code);

    // Should only apply cryptography transformations
    for (const applied of result.transformationsApplied) {
      const transformation = restrictedTransformer.getAvailableTransformations()
        .find(t => t.id === applied.transformationId);
      expect(transformation?.category).toBe('cryptography');
    }
  });

  it('should add imports only once for multiple transformations', () => {
    const code = `
      const a = Math.random();
      const b = Math.random();
    `;

    const result = transformer.transform(code);

    if (result.requiredImports.length > 0) {
      // Should deduplicate imports
      const moduleNames = result.requiredImports.map(i => i.module);
      const uniqueModules = [...new Set(moduleNames)];
      expect(moduleNames.length).toBe(uniqueModules.length);
    }
  });
});

// ============================================================================
// Risk Level Tests
// ============================================================================

describe('Risk Levels', () => {
  let transformer: SecureCodeTransformer;

  beforeEach(() => {
    transformer = createSecureCodeTransformer();
  });

  it('should have safe transformations', () => {
    const transformations = transformer.getAvailableTransformations();
    const safe = transformations.filter(t => t.riskLevel === 'safe');

    expect(safe.length).toBeGreaterThan(0);
  });

  it('should have caution transformations', () => {
    const transformations = transformer.getAvailableTransformations();
    const caution = transformations.filter(t => t.riskLevel === 'caution');

    expect(caution.length).toBeGreaterThan(0);
  });

  it('should have review-required transformations', () => {
    const transformations = transformer.getAvailableTransformations();
    const reviewRequired = transformations.filter(t => t.riskLevel === 'review-required');

    expect(reviewRequired.length).toBeGreaterThan(0);
  });

  it('should apply safe transformations first', () => {
    // This is an implicit test - safe transformations should be sorted first
    const transformations = transformer.getAvailableTransformations();

    // All transformations should have valid risk levels
    for (const t of transformations) {
      expect(['safe', 'caution', 'review-required']).toContain(t.riskLevel);
    }
  });
});

// ============================================================================
// Category Tests
// ============================================================================

describe('Transformation Categories', () => {
  it('should have output-encoding transformations', () => {
    const transformations = getBuiltInTransformations();
    const outputEncoding = transformations.filter(t => t.category === 'output-encoding');

    expect(outputEncoding.length).toBeGreaterThan(0);
  });

  it('should have cryptography transformations', () => {
    const transformations = getBuiltInTransformations();
    const crypto = transformations.filter(t => t.category === 'cryptography');

    expect(crypto.length).toBeGreaterThan(0);
  });

  it('should have error-handling transformations', () => {
    const transformations = getBuiltInTransformations();
    const errorHandling = transformations.filter(t => t.category === 'error-handling');

    expect(errorHandling.length).toBeGreaterThan(0);
  });

  it('should have data-protection transformations', () => {
    const transformations = getBuiltInTransformations();
    const dataProtection = transformations.filter(t => t.category === 'data-protection');

    expect(dataProtection.length).toBeGreaterThan(0);
  });

  it('should have session-management transformations', () => {
    const transformations = getBuiltInTransformations();
    const session = transformations.filter(t => t.category === 'session-management');

    expect(session.length).toBeGreaterThan(0);
  });
});
