/**
 * @fileoverview OWASP A03:2021 - Injection Rule
 * @module @nahisaho/musubix-security/rules/owasp/a03-injection
 * @trace TSK-RULE-003
 * 
 * Detects:
 * - SQL Injection
 * - NoSQL Injection
 * - Command Injection
 * - Code Injection (eval)
 * - Template Injection
 * 
 * Uses taint analysis when available for improved accuracy.
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

/**
 * OWASP A03 - Injection
 */
export const owaspA03Injection: SecurityRule = {
  id: 'owasp-a03-injection',
  name: 'OWASP A03:2021 - Injection',
  description: 'Detects injection vulnerabilities including SQL, NoSQL, command, and code injection',
  defaultSeverity: 'critical',
  detectionMethod: 'combined',
  tags: ['owasp', 'injection', 'sql', 'nosql', 'command', 'security'],
  owasp: ['A03:2021'],
  cwe: ['77', '78', '79', '89', '90', '91', '94', '95', '96', '917'],
  references: [
    { title: 'OWASP A03:2021 - Injection', url: 'https://owasp.org/Top10/A03_2021-Injection/' },
    { title: 'CWE-89: SQL Injection', url: 'https://cwe.mitre.org/data/definitions/89.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const sourceFile = context.sourceFile;
    if (!sourceFile) return findings;

    // Use taint analysis if available
    if (context.taintResults && context.taintResults.flows.length > 0) {
      analyzeTaintFlows(context, findings);
    }

    // Pattern-based detection
    checkSQLInjection(context, findings);
    checkNoSQLInjection(context, findings);
    checkCommandInjection(context, findings);
    checkCodeInjection(context, findings);
    checkTemplateInjection(context, findings);

    return findings;
  },
};

/**
 * Check for SQL injection vulnerabilities
 */
function checkSQLInjection(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const sqlPatterns = [
    // String concatenation in SQL
    { pattern: /['"`]SELECT\s+.*\+\s*(?:req\.|params\.|query\.|body\.)/gi, type: 'SQL query with string concatenation' },
    { pattern: /['"`]INSERT\s+INTO\s+.*\+\s*(?:req\.|params\.|query\.|body\.)/gi, type: 'SQL insert with string concatenation' },
    { pattern: /['"`]UPDATE\s+.*SET\s+.*\+\s*(?:req\.|params\.|query\.|body\.)/gi, type: 'SQL update with string concatenation' },
    { pattern: /['"`]DELETE\s+FROM\s+.*\+\s*(?:req\.|params\.|query\.|body\.)/gi, type: 'SQL delete with string concatenation' },
    // Template literals in SQL
    { pattern: /`SELECT\s+[^`]*\$\{[^}]*(?:req\.|params\.|query\.|body\.)/gi, type: 'SQL with template literal injection' },
    // Raw query with user input
    { pattern: /(?:query|execute|raw)\s*\(\s*['"`][^'"`]*\+/gi, type: 'Raw query with concatenation' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, type } of sqlPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a03-sql-${findings.length + 1}`,
          ruleId: 'owasp-a03-injection',
          severity: 'critical',
          message: `Potential SQL Injection: ${type}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['89'],
          suggestion: {
            description: 'Use parameterized queries',
            example: `// Use parameterized query:
// PostgreSQL/MySQL: db.query('SELECT * FROM users WHERE id = $1', [userId])
// ORM: Model.findOne({ where: { id: userId } })`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for NoSQL injection vulnerabilities
 */
function checkNoSQLInjection(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const nosqlPatterns = [
    // Direct user input in MongoDB queries
    { pattern: /\.\s*find\s*\(\s*\{\s*[^}]*:\s*(?:req\.body|req\.query|req\.params)/gi, type: 'MongoDB find with user input' },
    { pattern: /\.\s*findOne\s*\(\s*\{\s*[^}]*:\s*(?:req\.body|req\.query|req\.params)/gi, type: 'MongoDB findOne with user input' },
    { pattern: /\.\s*updateOne\s*\(\s*\{\s*[^}]*:\s*(?:req\.body|req\.query|req\.params)/gi, type: 'MongoDB updateOne with user input' },
    // $where with user input
    { pattern: /\$where\s*:\s*(?:req\.|params\.|query\.|body\.)/gi, type: 'MongoDB $where with user input' },
    // JSON.parse of user input in query
    { pattern: /JSON\.parse\s*\([^)]*(?:req\.body|req\.query)/gi, type: 'JSON.parse with user input' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, type } of nosqlPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        // Check for sanitization
        const surroundingCode = lines.slice(Math.max(0, lineNum - 3), lineNum + 1).join('\n');
        
        if (!hasSanitization(surroundingCode)) {
          findings.push({
            id: `owasp-a03-nosql-${findings.length + 1}`,
            ruleId: 'owasp-a03-injection',
            severity: 'high',
            message: `Potential NoSQL Injection: ${type}`,
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            cwe: ['943'],
            suggestion: {
              description: 'Sanitize user input before use in queries',
              example: `// Sanitize input before use:
const sanitizedInput = mongo.sanitize(userInput);
// Or use explicit type casting:
const id = new ObjectId(userId);`,
            },
          });
        }
        break;
      }
    }
  }
}

/**
 * Check for command injection vulnerabilities
 */
function checkCommandInjection(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const commandPatterns = [
    // exec with user input (string concatenation)
    { pattern: /exec\s*\(\s*['"`][^'"`]*['"`]\s*\+\s*(?:req\.|params\.|query\.|body\.)/gi, type: 'exec with concatenation' },
    { pattern: /exec\s*\([^)]*\+\s*req\./gi, type: 'exec with request input' },
    // exec with template literal
    { pattern: /exec\s*\(\s*`[^`]*\$\{[^}]*(?:req\.|params\.|query\.|body\.)/gi, type: 'exec with template literal' },
    { pattern: /exec\s*\(\s*`[^`]*\$\{/gi, type: 'exec with template literal variable' },
    // execSync with user input
    { pattern: /execSync\s*\(\s*['"`][^'"`]*['"`]\s*\+\s*(?:req\.|params\.|query\.|body\.)/gi, type: 'execSync with concatenation' },
    { pattern: /execSync\s*\([^)]*\+\s*req\./gi, type: 'execSync with request input' },
    // spawn with shell
    { pattern: /spawn\s*\([^)]*shell\s*:\s*true/gi, type: 'spawn with shell option' },
    // child_process with user input
    { pattern: /child_process\s*\.\s*exec\s*\([^)]*(?:req\.|params\.|query\.|body\.)/gi, type: 'child_process.exec with user input' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, type } of commandPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a03-cmd-${findings.length + 1}`,
          ruleId: 'owasp-a03-injection',
          severity: 'critical',
          message: `Potential Command Injection: ${type}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['78'],
          suggestion: {
            description: 'Use execFile or spawn with argument array',
            example: `// Use execFile with argument array (safer):
execFile('command', [arg1, arg2], callback);
// Or use spawn without shell:
spawn('command', ['arg1', 'arg2']);`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for code injection vulnerabilities (eval, Function constructor)
 */
function checkCodeInjection(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const codeInjectionPatterns = [
    // eval with any variable
    { pattern: /\beval\s*\(\s*[a-zA-Z_$]/gi, type: 'eval with variable' },
    // Function constructor
    { pattern: /new\s+Function\s*\(/gi, type: 'Function constructor' },
    // setTimeout/setInterval with string
    { pattern: /set(?:Timeout|Interval)\s*\(\s*['"`][^'"`]+['"`]/gi, type: 'setTimeout/setInterval with string' },
    // vm.runInContext with user input
    { pattern: /vm\.runIn(?:Context|NewContext|ThisContext)\s*\([^)]*(?:req\.|params\.|query\.|body\.)/gi, type: 'VM execution with user input' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, type } of codeInjectionPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a03-code-${findings.length + 1}`,
          ruleId: 'owasp-a03-injection',
          severity: 'critical',
          message: `Potential Code Injection: ${type}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['94', '95'],
          suggestion: {
            description: 'Avoid eval and Function constructor',
            example: `// Avoid eval and Function constructor
// Use JSON.parse for JSON data:
const data = JSON.parse(jsonString);
// Use a sandboxed VM for untrusted code execution`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for template injection vulnerabilities
 */
function checkTemplateInjection(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const templatePatterns = [
    // EJS with unescaped output
    { pattern: /<%[-=]\s*[^%]*(?:req\.|params\.|query\.|body\.)/gi, type: 'EJS template with unescaped user input' },
    // Pug/Jade with unescaped
    { pattern: /!{[^}]*(?:req\.|params\.|query\.|body\.)/gi, type: 'Pug template with unescaped user input' },
    // Handlebars triple braces
    { pattern: /\{\{\{[^}]*(?:req\.|params\.|query\.|body\.)/gi, type: 'Handlebars with unescaped user input' },
    // innerHTML assignment
    { pattern: /\.innerHTML\s*=\s*(?:req\.|params\.|query\.|body\.)/gi, type: 'innerHTML with user input' },
    // document.write
    { pattern: /document\.write\s*\([^)]*(?:req\.|params\.|query\.|body\.)/gi, type: 'document.write with user input' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, type } of templatePatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a03-template-${findings.length + 1}`,
          ruleId: 'owasp-a03-injection',
          severity: 'high',
          message: `Potential Template/XSS Injection: ${type}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['79', '917'],
          suggestion: {
            description: 'Use auto-escaping templates and avoid innerHTML',
            example: `// Use auto-escaping templates
// EJS: use <%= instead of <%-
// Use textContent instead of innerHTML
// Apply DOMPurify for HTML content`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Analyze taint flows for injection vulnerabilities
 */
function analyzeTaintFlows(context: RuleContext, findings: RuleFinding[]): void {
  if (!context.taintResults) return;
  
  const injectionSinks = ['sql', 'exec', 'eval', 'query', 'command', 'shell'];
  
  for (const flow of context.taintResults.flows) {
    const sinkCategory = flow.sink.category?.toLowerCase() || '';
    
    if (injectionSinks.some(sink => sinkCategory.includes(sink))) {
      findings.push({
        id: `owasp-a03-taint-${findings.length + 1}`,
        ruleId: 'owasp-a03-injection',
        severity: 'critical',
        message: `Taint flow detected: user input flows to ${flow.sink.category} sink without sanitization`,
        location: {
          file: context.filePath,
          startLine: flow.sink.location?.startLine ?? 1,
          endLine: flow.sink.location?.endLine ?? 1,
          startColumn: flow.sink.location?.startColumn ?? 0,
          endColumn: flow.sink.location?.endColumn ?? 10,
        },
        suggestion: {
          description: 'Add input validation and sanitization at the source',
          example: '// Add input validation and sanitization at the source',
        },
      });
    }
  }
}

/**
 * Check if code contains input sanitization
 */
function hasSanitization(code: string): boolean {
  const sanitizationPatterns = [
    /sanitize/i,
    /escape/i,
    /validate/i,
    /parameterized/i,
    /prepared/i,
    /placeholder/i,
    /bindParam/i,
    /ObjectId/i,
  ];
  
  return sanitizationPatterns.some(p => p.test(code));
}

export default owaspA03Injection;
