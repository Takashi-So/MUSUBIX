/**
 * @fileoverview OWASP A06:2021 - Vulnerable and Outdated Components
 * @module @nahisaho/musubix-security/rules/owasp/a06
 * @trace REQ-SEC-OWASP-006
 */

import type { SecurityRule, RuleContext, RuleFinding, RuleReference } from '../types.js';

/**
 * OWASP A06:2021 - Vulnerable and Outdated Components
 *
 * Detects:
 * - Known vulnerable package versions
 * - Outdated dependencies
 * - Using unmaintained packages
 * - Missing integrity checks
 */
export const owaspA06VulnerableComponents: SecurityRule = {
  id: 'owasp-a06-vulnerable-components',
  name: 'OWASP A06:2021 - Vulnerable and Outdated Components',
  description: 'Detects use of components with known vulnerabilities or outdated dependencies',
  defaultSeverity: 'high',
  category: 'dependency',
  owasp: ['A06:2021'],
  cwe: ['1035', '1104', '937'],
  references: [
    {
      title: 'OWASP A06:2021',
      url: 'https://owasp.org/Top10/A06_2021-Vulnerable_and_Outdated_Components/',
    },
    {
      title: 'CWE-1104: Use of Unmaintained Third Party Components',
      url: 'https://cwe.mitre.org/data/definitions/1104.html',
    },
  ] as RuleReference[],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];

    // Check for vulnerable patterns
    checkVulnerablePatterns(context, findings);

    // Check package.json if it's the target file
    if (context.filePath.endsWith('package.json')) {
      checkPackageJson(context, findings);
    }

    // Check for missing SRI in HTML/templates
    checkMissingSRI(context, findings);

    // Check for outdated CDN usage
    checkOutdatedCDN(context, findings);

    return findings;
  },
};

/**
 * Known vulnerable package patterns (simplified version)
 */
const VULNERABLE_PATTERNS = [
  // Lodash < 4.17.21
  { pattern: /['"`]lodash['"`]\s*:\s*['"`](?:[0-3]\.|4\.(?:[0-9]|1[0-6])\.|4\.17\.(?:[0-9]|1[0-9]|20))['"`]/i, pkg: 'lodash', issue: 'Prototype pollution vulnerability' },
  // jquery < 3.5.0
  { pattern: /['"`]jquery['"`]\s*:\s*['"`](?:[0-2]\.|3\.[0-4]\.)['"`]/i, pkg: 'jquery', issue: 'XSS vulnerability in htmlPrefilter' },
  // axios < 0.21.1
  { pattern: /['"`]axios['"`]\s*:\s*['"`]0\.(?:[0-9]|1[0-9]|20)\./i, pkg: 'axios', issue: 'SSRF vulnerability' },
  // minimist < 1.2.6
  { pattern: /['"`]minimist['"`]\s*:\s*['"`](?:0\.|1\.[0-2]\.[0-5])['"`]/i, pkg: 'minimist', issue: 'Prototype pollution vulnerability' },
  // serialize-javascript < 3.1.0
  { pattern: /['"`]serialize-javascript['"`]\s*:\s*['"`][0-2]\.['"`]/i, pkg: 'serialize-javascript', issue: 'RCE vulnerability' },
  // node-forge < 1.0.0
  { pattern: /['"`]node-forge['"`]\s*:\s*['"`]0\.['"`]/i, pkg: 'node-forge', issue: 'Improper verification of cryptographic signature' },
  // moment (unmaintained)
  { pattern: /['"`]moment['"`]\s*:/i, pkg: 'moment', issue: 'Unmaintained - consider using date-fns or luxon' },
  // request (deprecated)
  { pattern: /['"`]request['"`]\s*:/i, pkg: 'request', issue: 'Deprecated - use axios, got, or node-fetch' },
  // express-jwt < 6.0.0
  { pattern: /['"`]express-jwt['"`]\s*:\s*['"`][0-5]\.['"`]/i, pkg: 'express-jwt', issue: 'Algorithm confusion vulnerability' },
];

/**
 * Check for vulnerable patterns in source code
 */
function checkVulnerablePatterns(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  // Check for importing known vulnerable packages
  const importPatterns = [
    // CommonJS require of vulnerable packages
    { pattern: /require\s*\(\s*['"`]moment['"`]\s*\)/i, pkg: 'moment', issue: 'Unmaintained - consider using date-fns' },
    { pattern: /require\s*\(\s*['"`]request['"`]\s*\)/i, pkg: 'request', issue: 'Deprecated package' },
    // ES imports
    { pattern: /import\s+.*\s+from\s+['"`]moment['"`]/i, pkg: 'moment', issue: 'Unmaintained - consider using date-fns' },
    { pattern: /import\s+.*\s+from\s+['"`]request['"`]/i, pkg: 'request', issue: 'Deprecated package' },
    // Using vulnerable crypto in Node.js
    { pattern: /crypto\.createCipher\s*\(/i, pkg: 'crypto.createCipher', issue: 'Deprecated - use createCipheriv' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, pkg, issue } of importPatterns) {
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a06-import-${findings.length + 1}`,
          ruleId: 'owasp-a06-vulnerable-components',
          severity: 'medium',
          message: `Potentially vulnerable or deprecated component: ${pkg} - ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          suggestion: {
            description: 'Consider using a maintained alternative',
            example: pkg === 'moment'
              ? `// Use date-fns instead:\nimport { format, parseISO } from 'date-fns';`
              : pkg === 'request'
              ? `// Use axios or got instead:\nimport axios from 'axios';`
              : `// Use the recommended secure alternative`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check package.json for vulnerable dependencies
 */
function checkPackageJson(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, pkg, issue } of VULNERABLE_PATTERNS) {
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a06-pkg-${findings.length + 1}`,
          ruleId: 'owasp-a06-vulnerable-components',
          severity: 'high',
          message: `Vulnerable package version: ${pkg} - ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['1104'],
          suggestion: {
            description: 'Update to the latest secure version',
            example: `Run: npm audit fix\nOr: npm update ${pkg}`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for missing Subresource Integrity (SRI)
 */
function checkMissingSRI(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  // Only check HTML-like files or templates
  const isRelevantFile = /\.(html?|ejs|hbs|pug|vue|svelte|tsx?|jsx?)$/i.test(context.filePath);
  if (!isRelevantFile) return;

  const sriPatterns = [
    // Script tags from CDN without integrity
    { pattern: /<script[^>]+src\s*=\s*['"`]https?:\/\/(?:cdn|unpkg|jsdelivr|cdnjs)[^'"`]+['"`][^>]*>/i, type: 'script' },
    // Link tags from CDN without integrity
    { pattern: /<link[^>]+href\s*=\s*['"`]https?:\/\/(?:cdn|unpkg|jsdelivr|cdnjs)[^'"`]+['"`][^>]*>/i, type: 'stylesheet' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type } of sriPatterns) {
      if (pattern.test(line)) {
        // Check if integrity attribute is present
        if (!/integrity\s*=/i.test(line)) {
          findings.push({
            id: `owasp-a06-sri-${findings.length + 1}`,
            ruleId: 'owasp-a06-vulnerable-components',
            severity: 'medium',
            message: `Missing Subresource Integrity (SRI) for external ${type}`,
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            cwe: ['353'],
            suggestion: {
              description: 'Add integrity and crossorigin attributes',
              example: `<script src="https://cdn.example.com/lib.js" 
  integrity="sha384-..." 
  crossorigin="anonymous"></script>`,
            },
          });
        }
        break;
      }
    }
  }
}

/**
 * Check for outdated CDN URLs
 */
function checkOutdatedCDN(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const outdatedCDNPatterns = [
    // Old jQuery versions
    { pattern: /jquery[\/\-]([0-2]\.[0-9]+|3\.[0-4]\.[0-9]+)/i, lib: 'jQuery', issue: 'outdated version' },
    // Old Bootstrap versions
    { pattern: /bootstrap[\/\-]([0-3]\.[0-9]+|4\.[0-5]\.[0-9]+)/i, lib: 'Bootstrap', issue: 'outdated version' },
    // Old Angular versions
    { pattern: /angular[\/\-](1\.[0-7]\.[0-9]+)/i, lib: 'AngularJS', issue: 'legacy version' },
    // HTTP instead of HTTPS for CDN
    { pattern: /['"`]http:\/\/(?:cdn|unpkg|jsdelivr|cdnjs)/i, lib: 'CDN', issue: 'using HTTP instead of HTTPS' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, lib, issue } of outdatedCDNPatterns) {
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a06-cdn-${findings.length + 1}`,
          ruleId: 'owasp-a06-vulnerable-components',
          severity: lib === 'CDN' ? 'high' : 'medium',
          message: `Potentially ${issue}: ${lib}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          suggestion: {
            description: lib === 'CDN'
              ? 'Always use HTTPS for external resources'
              : `Update ${lib} to the latest version`,
          },
        });
        break;
      }
    }
  }
}

export default owaspA06VulnerableComponents;
