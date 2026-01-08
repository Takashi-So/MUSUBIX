/**
 * @fileoverview CWE-79: Improper Neutralization of Input During Web Page Generation (XSS)
 * @module @nahisaho/musubix-security/rules/cwe/cwe-79-xss
 * @trace TSK-RULE-005
 *
 * Detects:
 * - Reflected XSS (user input in response)
 * - Stored XSS (database content in output)
 * - DOM-based XSS (client-side manipulation)
 * - innerHTML/outerHTML usage
 * - document.write usage
 * - Unsafe template rendering
 *
 * CWE-79 is #2 in CWE Top 25 2023.
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

/**
 * CWE-79 - Cross-site Scripting (XSS)
 */
export const cwe79XSS: SecurityRule = {
  id: 'cwe-79-xss',
  name: 'CWE-79: Cross-site Scripting (XSS)',
  description:
    'Detects XSS vulnerabilities including reflected, stored, and DOM-based XSS',
  defaultSeverity: 'high',
  category: 'injection',
  tags: ['cwe', 'xss', 'injection', 'web', 'security'],
  owasp: ['A03:2021'],
  cwe: ['79'],
  references: [
    {
      title: 'CWE-79: Cross-site Scripting',
      url: 'https://cwe.mitre.org/data/definitions/79.html',
    },
    {
      title: 'OWASP XSS Prevention Cheat Sheet',
      url: 'https://cheatsheetseries.owasp.org/cheatsheets/Cross_Site_Scripting_Prevention_Cheat_Sheet.html',
    },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const sourceCode = context.sourceCode;

    checkDOMXSS(context, sourceCode, findings);
    checkReflectedXSS(context, sourceCode, findings);
    checkUnsafeTemplating(context, sourceCode, findings);
    checkReactVulnerabilities(context, sourceCode, findings);

    return findings;
  },
};

/**
 * Check for DOM-based XSS vulnerabilities
 */
function checkDOMXSS(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const domPatterns = [
    {
      pattern: /\.innerHTML\s*=\s*(?!['"`]<)/gi,
      type: 'innerHTML assignment',
      message:
        'innerHTML assignment with dynamic content can lead to DOM XSS',
      severity: 'high' as const,
    },
    {
      pattern: /\.outerHTML\s*=\s*(?!['"`]<)/gi,
      type: 'outerHTML assignment',
      message:
        'outerHTML assignment with dynamic content can lead to DOM XSS',
      severity: 'high' as const,
    },
    {
      pattern: /document\.write\s*\(/gi,
      type: 'document.write usage',
      message:
        'document.write can execute scripts and is vulnerable to XSS',
      severity: 'high' as const,
    },
    {
      pattern: /document\.writeln\s*\(/gi,
      type: 'document.writeln usage',
      message:
        'document.writeln can execute scripts and is vulnerable to XSS',
      severity: 'high' as const,
    },
    {
      pattern: /\.insertAdjacentHTML\s*\(/gi,
      type: 'insertAdjacentHTML usage',
      message:
        'insertAdjacentHTML with unsanitized input can lead to XSS',
      severity: 'medium' as const,
    },
    {
      pattern: /\.outerText\s*=|\.innerText\s*=/gi,
      type: 'Text content assignment',
      message:
        'innerText/outerText are safer but still review for proper encoding',
      severity: 'info' as const,
    },
    {
      pattern: /eval\s*\(\s*(?:location\.|document\.|window\.)/gi,
      type: 'eval with DOM properties',
      message: 'eval() with DOM properties is highly vulnerable to XSS',
      severity: 'critical' as const,
    },
    {
      pattern: /new\s+Function\s*\(\s*(?:location\.|document\.|window\.)/gi,
      type: 'Function constructor with DOM',
      message:
        'Function constructor with DOM properties can execute arbitrary code',
      severity: 'critical' as const,
    },
    {
      pattern: /setTimeout\s*\(\s*(?:location\.|document\.\w+\.value)/gi,
      type: 'setTimeout with DOM input',
      message: 'setTimeout with DOM input can execute injected code',
      severity: 'high' as const,
    },
    {
      pattern: /setInterval\s*\(\s*(?:location\.|document\.\w+\.value)/gi,
      type: 'setInterval with DOM input',
      message: 'setInterval with DOM input can execute injected code',
      severity: 'high' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of domPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-79-dom-${findings.length + 1}`,
          ruleId: 'cwe-79-xss',
          severity,
          message: `DOM XSS - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['79'],
          owasp: ['A03:2021'],
          suggestion: {
            description: 'Use safe DOM manipulation methods',
            example: `// Instead of innerHTML, use textContent for text:
element.textContent = userInput;

// Or use DOM methods for elements:
const safeElement = document.createElement('div');
safeElement.textContent = userInput;
parent.appendChild(safeElement);

// For HTML, use DOMPurify:
import DOMPurify from 'dompurify';
element.innerHTML = DOMPurify.sanitize(userInput);`,
          },
        });
      }
    }
  }
}

/**
 * Check for reflected XSS patterns (server-side)
 */
function checkReflectedXSS(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const reflectedPatterns = [
    {
      pattern: /res\.send\s*\(\s*(?:req\.|params\.|query\.)/gi,
      type: 'Direct response with user input',
      message:
        'Sending user input directly in response without encoding',
      severity: 'high' as const,
    },
    {
      pattern: /res\.write\s*\(\s*(?:req\.|params\.|query\.)/gi,
      type: 'Writing user input to response',
      message:
        'Writing user input directly to response stream without encoding',
      severity: 'high' as const,
    },
    {
      pattern: /res\.send\s*\(\s*`[^`]*\$\{(?:req\.|params\.|query\.)/gi,
      type: 'Template literal with user input',
      message:
        'User input in template literal response can cause XSS',
      severity: 'high' as const,
    },
    {
      pattern: /res\.(?:json|send)\s*\(\s*\{[^}]*:\s*(?:req\.|params\.|query\.)/gi,
      type: 'User input in JSON response',
      message:
        'Ensure JSON response Content-Type is properly set',
      severity: 'medium' as const,
    },
    {
      pattern:
        /render\s*\(\s*['"`]\w+['"`]\s*,\s*\{[^}]*:\s*(?:req\.|params\.|query\.)/gi,
      type: 'User input passed to template',
      message: 'User input passed to template without sanitization',
      severity: 'medium' as const,
    },
    {
      pattern: /\.html\s*\(\s*(?:req\.|params\.|query\.)/gi,
      type: 'User input in HTML response',
      message:
        'User input in .html() response is vulnerable to XSS',
      severity: 'high' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of reflectedPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-79-reflected-${findings.length + 1}`,
          ruleId: 'cwe-79-xss',
          severity,
          message: `Reflected XSS - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['79'],
          owasp: ['A03:2021'],
          suggestion: {
            description: 'Encode output before sending to client',
            example: `// Use a templating engine with auto-escaping (EJS, Handlebars)
// Or encode manually:
import { encode } from 'html-entities';
res.send(encode(userInput));

// For JSON responses, ensure Content-Type:
res.type('application/json').json({ data: userInput });`,
          },
        });
      }
    }
  }
}

/**
 * Check for unsafe templating patterns
 */
function checkUnsafeTemplating(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const templatePatterns = [
    {
      pattern: /\{\{\{\s*\w+\s*\}\}\}/gi,
      type: 'Triple mustache (unescaped)',
      message:
        'Triple mustache in Handlebars outputs unescaped HTML',
      severity: 'high' as const,
    },
    {
      pattern: /<%[-=]\s*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'EJS with user input',
      message:
        'EJS unescaped output (<%-) with user input is vulnerable',
      severity: 'high' as const,
    },
    {
      pattern: /\|\s*safe\s*\}\}/gi,
      type: 'Jinja/Nunjucks safe filter',
      message:
        'safe filter disables auto-escaping, verify input is trusted',
      severity: 'medium' as const,
    },
    {
      pattern: /v-html\s*=\s*["']/gi,
      type: 'Vue v-html directive',
      message:
        'v-html renders raw HTML and can cause XSS if content is untrusted',
      severity: 'high' as const,
    },
    {
      pattern: /\[innerHTML\]\s*=\s*["']/gi,
      type: 'Angular innerHTML binding',
      message:
        'Angular innerHTML binding with untrusted content is vulnerable',
      severity: 'high' as const,
    },
    {
      pattern: /bypassSecurityTrust(?:Html|Script|Style|Url|ResourceUrl)\s*\(/gi,
      type: 'Angular security bypass',
      message:
        'Bypassing Angular sanitization is dangerous with untrusted content',
      severity: 'critical' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of templatePatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-79-template-${findings.length + 1}`,
          ruleId: 'cwe-79-xss',
          severity,
          message: `Template XSS - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['79'],
          owasp: ['A03:2021'],
          suggestion: {
            description: 'Use escaped output in templates',
            example: `// Handlebars: Use double mustache for escaped output
{{ safeVariable }}

// EJS: Use <%= for escaped output
<%= userInput %>

// Vue: Use v-text or {{ }} for text content
<span>{{ userInput }}</span>

// Angular: Trust only after sanitization
this.sanitizer.sanitize(SecurityContext.HTML, content)`,
          },
        });
      }
    }
  }
}

/**
 * Check for React-specific XSS vulnerabilities
 */
function checkReactVulnerabilities(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const reactPatterns = [
    {
      pattern: /dangerouslySetInnerHTML\s*=\s*\{\s*\{/gi,
      type: 'dangerouslySetInnerHTML usage',
      message:
        'dangerouslySetInnerHTML can cause XSS if content is not sanitized',
      severity: 'high' as const,
    },
    {
      pattern:
        /dangerouslySetInnerHTML\s*=\s*\{\s*\{\s*__html\s*:\s*(?:props\.|state\.|data\.)/gi,
      type: 'dangerouslySetInnerHTML with props/state',
      message:
        'Using props or state in dangerouslySetInnerHTML without sanitization',
      severity: 'critical' as const,
    },
    {
      pattern: /href\s*=\s*\{\s*`javascript:/gi,
      type: 'JavaScript URL in href',
      message:
        'JavaScript URLs in href attributes can execute scripts',
      severity: 'critical' as const,
    },
    {
      pattern: /href\s*=\s*\{\s*(?:props\.|state\.|data\.)/gi,
      type: 'Dynamic href from props/state',
      message:
        'Dynamic href values should be validated against javascript: protocol',
      severity: 'medium' as const,
    },
    {
      pattern: /createRef\(\).*\.current\.innerHTML\s*=/gi,
      type: 'Ref innerHTML assignment',
      message:
        'Setting innerHTML via ref bypasses React protection',
      severity: 'high' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of reactPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-79-react-${findings.length + 1}`,
          ruleId: 'cwe-79-xss',
          severity,
          message: `React XSS - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['79'],
          owasp: ['A03:2021'],
          suggestion: {
            description: 'Use React safe patterns',
            example: `// Sanitize before using dangerouslySetInnerHTML
import DOMPurify from 'dompurify';
<div dangerouslySetInnerHTML={{ __html: DOMPurify.sanitize(content) }} />

// Validate URLs before using in href
const safeUrl = url.startsWith('javascript:') ? '#' : url;
<a href={safeUrl}>Link</a>

// Prefer textContent for text
<span>{userInput}</span>`,
          },
        });
      }
    }
  }
}

export default cwe79XSS;
