/**
 * @fileoverview Fix generator service - generates fix suggestions for vulnerabilities
 * @module @nahisaho/musubix-security/services/fix-generator
 * @trace REQ-SEC-FIX-001
 */

import type {
  Fix,
  FixStrategy,
  CodeEdit,
  ImportEdit,
  FixGenerationOptions,
  Vulnerability,
  VulnerabilityType,
} from '../types/index.js';
import type { TaintPath } from '../types/taint.js';

/**
 * Generate fix ID
 */
let fixCounter = 0;
function generateFixId(): string {
  const date = new Date();
  const dateStr = date.toISOString().slice(0, 10).replace(/-/g, '');
  return `FIX-${dateStr}-${String(++fixCounter).padStart(3, '0')}`;
}

/**
 * Reset fix counter (for testing)
 */
export function resetFixCounter(): void {
  fixCounter = 0;
}

/**
 * Fix template for a vulnerability type
 */
interface FixTemplate {
  type: VulnerabilityType;
  strategy: FixStrategy;
  title: string;
  description: string;
  rationale: string;
  imports: ImportEdit[];
  transform: (vuln: Vulnerability) => CodeEdit[];
}

/**
 * SQL Injection fix template
 */
const sqlInjectionFix: FixTemplate = {
  type: 'injection',
  strategy: 'parameterized-query',
  title: 'Use parameterized queries',
  description: 'Replace string interpolation with parameterized queries to prevent SQL injection',
  rationale: 'Parameterized queries separate SQL code from data, preventing attackers from modifying the query structure.',
  imports: [],
  transform: (vuln: Vulnerability): CodeEdit[] => {
    const snippet = vuln.codeSnippet || '';
    
    // Pattern: `SELECT * FROM users WHERE id = ${userId}`
    // Replace with: 'SELECT * FROM users WHERE id = ?', [userId]
    const templateRegex = /`([^`]*)\$\{([^}]+)\}([^`]*)`/;
    const match = snippet.match(templateRegex);
    
    if (match) {
      const [original, before, variable, after] = match;
      const parameterized = `'${before}?${after}', [${variable}]`;
      
      return [{
        location: vuln.location,
        originalCode: original,
        newCode: parameterized,
        description: 'Convert template literal to parameterized query',
      }];
    }

    // Pattern: 'SELECT * FROM users WHERE id = ' + userId
    const concatRegex = /'([^']+)'\s*\+\s*(\w+)/;
    const concatMatch = snippet.match(concatRegex);
    
    if (concatMatch) {
      const [original, sql, variable] = concatMatch;
      const parameterized = `'${sql}?', [${variable}]`;
      
      return [{
        location: vuln.location,
        originalCode: original,
        newCode: parameterized,
        description: 'Convert string concatenation to parameterized query',
      }];
    }

    return [];
  },
};

/**
 * Command injection fix template
 */
const commandInjectionFix: FixTemplate = {
  type: 'command-injection',
  strategy: 'command-escape',
  title: 'Use execFile with array arguments',
  description: 'Replace exec() with execFile() and array arguments to prevent command injection',
  rationale: 'execFile() with array arguments does not invoke a shell, preventing shell metacharacter injection.',
  imports: [
    {
      module: 'node:child_process',
      namedImports: ['execFile'],
      insertLine: 0,
    },
  ],
  transform: (vuln: Vulnerability): CodeEdit[] => {
    const snippet = vuln.codeSnippet || '';
    
    // Pattern: exec(`command ${arg}`)
    const execRegex = /exec\s*\(\s*`([^`]+)\$\{([^}]+)\}([^`]*)`\s*\)/;
    const match = snippet.match(execRegex);
    
    if (match) {
      const [original, before, variable] = match;
      // Extract command and args
      const parts = before.trim().split(/\s+/);
      const command = parts[0];
      const fixedArgs = parts.slice(1).map(a => `'${a}'`);
      fixedArgs.push(variable);
      
      const replacement = `execFile('${command}', [${fixedArgs.join(', ')}])`;
      
      return [{
        location: vuln.location,
        originalCode: original,
        newCode: replacement,
        description: 'Replace exec() with execFile() using array arguments',
      }];
    }

    return [];
  },
};

/**
 * Path traversal fix template
 */
const pathTraversalFix: FixTemplate = {
  type: 'path-traversal',
  strategy: 'path-validation',
  title: 'Validate and sanitize file paths',
  description: 'Add path validation to prevent directory traversal attacks',
  rationale: 'Validating that the resolved path stays within the allowed directory prevents access to unauthorized files.',
  imports: [
    {
      module: 'node:path',
      namedImports: ['resolve', 'relative'],
      insertLine: 0,
    },
  ],
  transform: (vuln: Vulnerability): CodeEdit[] => {
    const snippet = vuln.codeSnippet || '';
    
    // Pattern: readFile(userPath)
    const fsRegex = /(readFile(?:Sync)?|writeFile(?:Sync)?)\s*\(\s*(\w+)/;
    const match = snippet.match(fsRegex);
    
    if (match) {
      const [, , pathVar] = match;
      const safePath = `(() => {
  const baseDir = '/allowed/base/dir';
  const resolved = resolve(baseDir, ${pathVar});
  if (!resolved.startsWith(baseDir)) {
    throw new Error('Path traversal detected');
  }
  return resolved;
})()`;
      
      return [{
        location: vuln.location,
        originalCode: pathVar,
        newCode: safePath,
        description: 'Add path validation to prevent directory traversal',
      }];
    }

    return [];
  },
};

/**
 * XSS fix template
 */
const xssFix: FixTemplate = {
  type: 'xss',
  strategy: 'html-escape',
  title: 'Escape HTML output',
  description: 'Add HTML escaping to prevent Cross-Site Scripting attacks',
  rationale: 'HTML escaping converts special characters to their HTML entities, preventing script injection.',
  imports: [],
  transform: (vuln: Vulnerability): CodeEdit[] => {
    const snippet = vuln.codeSnippet || '';
    
    // Pattern: res.send(`<div>${userInput}</div>`)
    const sendRegex = /res\.send\s*\(\s*`([^`]*)\$\{([^}]+)\}([^`]*)`\s*\)/;
    const match = snippet.match(sendRegex);
    
    if (match) {
      const [original, before, variable, after] = match;
      
      const replacement = `res.send(\`${before}\${escapeHtml(${variable})}${after}\`)`;
      
      return [{
        location: vuln.location,
        originalCode: original,
        newCode: replacement,
        description: 'Add HTML escaping to output',
      }];
    }

    return [];
  },
};

/**
 * Eval fix template
 */
const evalFix: FixTemplate = {
  type: 'code-injection',
  strategy: 'input-validation',
  title: 'Remove eval() usage',
  description: 'Replace eval() with safer alternatives',
  rationale: 'eval() executes arbitrary code, which is inherently dangerous. Safer alternatives should be used.',
  imports: [],
  transform: (vuln: Vulnerability): CodeEdit[] => {
    const snippet = vuln.codeSnippet || '';
    
    // Pattern: eval(jsonString)
    if (snippet.includes('eval') && snippet.includes('JSON')) {
      const evalRegex = /eval\s*\(\s*(\w+)\s*\)/;
      const match = snippet.match(evalRegex);
      
      if (match) {
        const [original, variable] = match;
        return [{
          location: vuln.location,
          originalCode: original,
          newCode: `JSON.parse(${variable})`,
          description: 'Replace eval() with JSON.parse() for JSON parsing',
        }];
      }
    }

    return [];
  },
};

/**
 * Prototype pollution fix template
 */
const prototypePollutionFix: FixTemplate = {
  type: 'prototype-pollution',
  strategy: 'input-validation',
  title: 'Validate object keys',
  description: 'Add validation to prevent prototype pollution via __proto__ or constructor',
  rationale: 'Blocking dangerous property names prevents attackers from modifying Object.prototype.',
  imports: [],
  transform: (vuln: Vulnerability): CodeEdit[] => {
    const snippet = vuln.codeSnippet || '';
    
    // Pattern: Object.assign(target, userInput)
    const assignRegex = /Object\.assign\s*\(\s*(\w+)\s*,\s*(\w+)\s*\)/;
    const match = snippet.match(assignRegex);
    
    if (match) {
      const [original, target, source] = match;
      const safeMerge = `Object.assign(${target}, Object.fromEntries(
  Object.entries(${source}).filter(([k]) => !['__proto__', 'constructor', 'prototype'].includes(k))
))`;
      
      return [{
        location: vuln.location,
        originalCode: original,
        newCode: safeMerge,
        description: 'Filter dangerous keys before Object.assign',
      }];
    }

    return [];
  },
};

/**
 * All fix templates
 */
const FIX_TEMPLATES: FixTemplate[] = [
  sqlInjectionFix,
  commandInjectionFix,
  pathTraversalFix,
  xssFix,
  evalFix,
  prototypePollutionFix,
];

/**
 * Fix generator service
 */
export class FixGenerator {
  private templates: FixTemplate[];

  constructor(_options: FixGenerationOptions = {}) {
    this.templates = [...FIX_TEMPLATES];
  }

  /**
   * Generate a fix for a vulnerability
   */
  generateFix(vuln: Vulnerability): Fix | null {
    // Find matching template
    const template = this.templates.find((t) => t.type === vuln.type);
    if (!template) {
      return null;
    }

    // Generate code edits
    const edits = template.transform(vuln);
    if (edits.length === 0) {
      return null;
    }

    return {
      id: generateFixId(),
      vulnerabilityId: vuln.id,
      strategy: template.strategy,
      title: template.title,
      description: template.description,
      edits,
      imports: template.imports,
      confidence: vuln.confidence * 0.8, // Reduce confidence for fixes
      breakingChange: false,
      rationale: template.rationale,
      generatedAt: new Date(),
    };
  }

  /**
   * Generate fixes for multiple vulnerabilities
   */
  generateFixes(vulnerabilities: Vulnerability[]): Fix[] {
    const fixes: Fix[] = [];

    for (const vuln of vulnerabilities) {
      const fix = this.generateFix(vuln);
      if (fix) {
        fixes.push(fix);
      }
    }

    return fixes;
  }

  /**
   * Generate a fix for a taint path
   */
  generateTaintFix(path: TaintPath): Fix | null {
    // Map sink category to vulnerability type
    const categoryToType: Record<string, VulnerabilityType> = {
      'sql-query': 'injection',
      'command-exec': 'command-injection',
      'file-read': 'path-traversal',
      'file-write': 'path-traversal',
      'html-output': 'xss',
      'eval': 'code-injection',
      'redirect': 'open-redirect',
    };

    const vulnType = categoryToType[path.sink.category];
    if (!vulnType) {
      return null;
    }

    // Create a pseudo-vulnerability for fix generation
    const pseudoVuln: Vulnerability = {
      id: `TAINT-${path.id}`,
      type: vulnType,
      severity: path.sink.severity,
      cwes: [],
      location: path.sink.location,
      description: `Taint path from ${path.source.category} to ${path.sink.category}`,
      recommendation: `Add sanitization for ${path.sink.category}`,
      confidence: path.confidence,
      ruleId: 'TAINT',
      detectedAt: new Date(),
    };

    const fix = this.generateFix(pseudoVuln);
    if (fix) {
      fix.taintPathId = path.id;
    }

    return fix;
  }

  /**
   * Add a custom fix template
   */
  addTemplate(template: FixTemplate): void {
    this.templates.push(template);
  }

  /**
   * Get available strategies
   */
  getStrategies(): FixStrategy[] {
    return [...new Set(this.templates.map((t) => t.strategy))];
  }
}

/**
 * Create a fix generator
 */
export function createFixGenerator(options?: FixGenerationOptions): FixGenerator {
  return new FixGenerator(options);
}
