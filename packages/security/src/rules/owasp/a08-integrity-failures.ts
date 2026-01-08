/**
 * @fileoverview OWASP A08:2021 - Software and Data Integrity Failures
 * @module @nahisaho/musubix-security/rules/owasp/a08
 * @trace REQ-SEC-OWASP-008
 */

import type { SecurityRule, RuleContext, RuleFinding, RuleReference } from '../types.js';

/**
 * OWASP A08:2021 - Software and Data Integrity Failures
 *
 * Detects:
 * - Insecure deserialization
 * - Missing integrity verification
 * - Untrusted CI/CD pipelines
 * - Auto-update vulnerabilities
 */
export const owaspA08IntegrityFailures: SecurityRule = {
  id: 'owasp-a08-integrity-failures',
  name: 'OWASP A08:2021 - Software and Data Integrity Failures',
  description: 'Detects insecure deserialization and missing integrity verification',
  defaultSeverity: 'critical',
  category: 'integrity',
  owasp: ['A08:2021'],
  cwe: ['502', '829', '494', '915'],
  references: [
    {
      title: 'OWASP A08:2021',
      url: 'https://owasp.org/Top10/A08_2021-Software_and_Data_Integrity_Failures/',
    },
    {
      title: 'CWE-502: Deserialization of Untrusted Data',
      url: 'https://cwe.mitre.org/data/definitions/502.html',
    },
  ] as RuleReference[],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];

    checkInsecureDeserialization(context, findings);
    checkUnsafeJSONParse(context, findings);
    checkMissingIntegrityChecks(context, findings);
    checkUnsafeAutoUpdate(context, findings);
    checkObjectInjection(context, findings);

    return findings;
  },
};

/**
 * Check for insecure deserialization
 */
function checkInsecureDeserialization(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const deserializationPatterns = [
    // Node.js serialize
    { pattern: /node-serialize.*unserialize|unserialize\s*\(/i, lib: 'node-serialize', issue: 'Known RCE vulnerability' },
    { pattern: /serialize-javascript.*deserialize/i, lib: 'serialize-javascript', issue: 'Potential code execution' },
    // YAML deserialization
    { pattern: /yaml\.(?:load|parse)\s*\([^)]*(?:req\.|body\.|params\.)/i, lib: 'yaml', issue: 'Unsafe YAML deserialization with user input' },
    { pattern: /js-yaml.*safeLoad.*false|yaml\.load\s*\([^,]+,\s*\{\s*schema/i, lib: 'js-yaml', issue: 'YAML deserialization with unsafe schema' },
    // XML deserialization
    { pattern: /xml2js.*parseString\s*\([^)]*(?:req\.|body\.)/i, lib: 'xml2js', issue: 'XML parsing of user input' },
    // Pickle-like (if in Python-related code)
    { pattern: /pickle\.loads?\s*\(/i, lib: 'pickle', issue: 'Unsafe pickle deserialization' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, lib, issue } of deserializationPatterns) {
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a08-deserialize-${findings.length + 1}`,
          ruleId: 'owasp-a08-integrity-failures',
          severity: 'critical',
          message: `Insecure deserialization: ${lib} - ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['502'],
          suggestion: {
            description: 'Use safe deserialization methods and validate input',
            example: `// For YAML, use safe loading:
const yaml = require('js-yaml');
const data = yaml.load(input, { schema: yaml.SAFE_SCHEMA });

// For JSON, use JSON.parse with validation:
const parsed = JSON.parse(input);
if (!isValidSchema(parsed)) throw new Error('Invalid data');`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for unsafe JSON.parse with user input
 */
function checkUnsafeJSONParse(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const jsonPatterns = [
    // JSON.parse of request body directly (without validation)
    { pattern: /JSON\.parse\s*\(\s*req\.body\s*\)/i, issue: 'JSON.parse of raw request body' },
    // JSON.parse of user-controlled string
    { pattern: /JSON\.parse\s*\(\s*(?:userInput|input|data)\s*\)/i, issue: 'JSON.parse of potentially untrusted input' },
    // eval-like JSON parsing
    { pattern: /eval\s*\(\s*['"`]\s*\(\s*['"`]\s*\+/i, issue: 'eval-based parsing' },
    // Function constructor for parsing
    { pattern: /new\s+Function\s*\([^)]*(?:req\.|body\.|params\.)/i, issue: 'Function constructor with user input' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, issue } of jsonPatterns) {
      if (pattern.test(line)) {
        // Check for validation in surrounding code
        const surroundingCode = lines.slice(Math.max(0, lineNum - 3), lineNum + 4).join('\n');
        const hasValidation = /(?:validate|schema|ajv|joi|zod|yup)/i.test(surroundingCode);

        if (!hasValidation) {
          findings.push({
            id: `owasp-a08-json-${findings.length + 1}`,
            ruleId: 'owasp-a08-integrity-failures',
            severity: 'medium',
            message: `Unsafe JSON parsing: ${issue}`,
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            cwe: ['502', '20'],
            suggestion: {
              description: 'Validate JSON data after parsing',
              example: `// Use schema validation:
import Ajv from 'ajv';
const ajv = new Ajv();
const validate = ajv.compile(schema);

const data = JSON.parse(input);
if (!validate(data)) {
  throw new Error('Invalid data format');
}`,
            },
          });
        }
        break;
      }
    }
  }
}

/**
 * Check for missing integrity checks
 */
function checkMissingIntegrityChecks(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const integrityPatterns = [
    // npm install without lock file check
    { pattern: /npm\s+install(?!\s+--ignore-scripts)/i, cmdContext: true, issue: 'npm install without script safety' },
    // curl piped to shell
    { pattern: /curl\s+[^|]*\|\s*(?:bash|sh|zsh)/i, issue: 'curl piped to shell without verification' },
    // wget with insecure option
    { pattern: /wget\s+--no-check-certificate/i, issue: 'wget with certificate verification disabled' },
    // Docker without digest
    { pattern: /FROM\s+\S+(?!@sha256:)/i, fileContext: /dockerfile/i, issue: 'Docker image without digest verification' },
    // Missing signature verification
    { pattern: /download.*\{[^}]*(?!verify|signature|hash|checksum)/i, issue: 'Download without integrity verification' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, issue, fileContext } of integrityPatterns) {
      if (fileContext && !fileContext.test(context.filePath)) continue;

      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a08-integrity-${findings.length + 1}`,
          ruleId: 'owasp-a08-integrity-failures',
          severity: 'high',
          message: `Missing integrity verification: ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['494'],
          suggestion: {
            description: 'Always verify integrity of downloaded content',
            example: `// Verify downloads with checksums:
const crypto = require('crypto');
const hash = crypto.createHash('sha256');
hash.update(downloadedContent);
if (hash.digest('hex') !== expectedHash) {
  throw new Error('Integrity check failed');
}`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for unsafe auto-update mechanisms
 */
function checkUnsafeAutoUpdate(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const autoUpdatePatterns = [
    // Electron auto-update without verification
    { pattern: /autoUpdater\.(?:setFeedURL|checkForUpdates)\s*\(/i, lib: 'electron-updater', issue: 'Ensure update server uses HTTPS and signature verification' },
    // Custom update mechanism
    { pattern: /fetch\s*\([^)]*update|download\s*\([^)]*latest/i, issue: 'Custom update mechanism without signature verification' },
    // Update from HTTP
    { pattern: /['"`]http:\/\/[^'"`]*\/(?:update|download|latest)/i, issue: 'Update URL using HTTP instead of HTTPS' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, lib, issue } of autoUpdatePatterns) {
      if (pattern.test(line)) {
        // Check for signature verification
        const surroundingCode = lines.slice(Math.max(0, lineNum - 5), lineNum + 6).join('\n');
        const hasVerification = /(?:verify|signature|checksum|hash|publicKey)/i.test(surroundingCode);

        if (!hasVerification) {
          findings.push({
            id: `owasp-a08-update-${findings.length + 1}`,
            ruleId: 'owasp-a08-integrity-failures',
            severity: 'high',
            message: `Unsafe auto-update: ${lib ? `${lib} - ` : ''}${issue}`,
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            cwe: ['494'],
            suggestion: {
              description: 'Implement code signing and signature verification for updates',
              example: `// Verify update signatures:
autoUpdater.autoInstallOnAppQuit = false;
autoUpdater.on('update-downloaded', (info) => {
  if (verifySignature(info.downloadedFile, publicKey)) {
    autoUpdater.quitAndInstall();
  }
});`,
            },
          });
        }
        break;
      }
    }
  }
}

/**
 * Check for object injection vulnerabilities
 */
function checkObjectInjection(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const objectInjectionPatterns = [
    // Object spread with user input
    { pattern: /\{\s*\.\.\.(?:req\.body|req\.params|req\.query)\s*\}/i, issue: 'Object spread with unvalidated user input' },
    // Object.assign with user input
    { pattern: /Object\.assign\s*\([^)]*(?:req\.body|req\.params|req\.query)/i, issue: 'Object.assign with user input' },
    // Dynamic property access
    { pattern: /\[\s*req\.(?:body|params|query)\.\w+\s*\]/i, issue: 'Dynamic property access with user input' },
    // __proto__ manipulation risk
    { pattern: /\[['"`]?__proto__|prototype\[/i, issue: 'Prototype pollution risk' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, issue } of objectInjectionPatterns) {
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a08-object-${findings.length + 1}`,
          ruleId: 'owasp-a08-integrity-failures',
          severity: 'high',
          message: `Object injection vulnerability: ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['915', '1321'],
          suggestion: {
            description: 'Use allowlists and explicit property access',
            example: `// Use explicit property access with allowlist:
const allowedFields = ['name', 'email', 'age'];
const sanitized = {};
for (const key of allowedFields) {
  if (req.body[key] !== undefined) {
    sanitized[key] = req.body[key];
  }
}`,
          },
        });
        break;
      }
    }
  }
}

export default owaspA08IntegrityFailures;
