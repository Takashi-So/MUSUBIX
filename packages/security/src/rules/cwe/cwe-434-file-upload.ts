/**
 * @fileoverview CWE-434: Unrestricted Upload of File with Dangerous Type
 * @module @nahisaho/musubix-security/rules/cwe/cwe-434-file-upload
 * @trace TSK-RULE-005
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe434FileUpload: SecurityRule = {
  id: 'cwe-434-file-upload',
  name: 'CWE-434: Unrestricted File Upload',
  description: 'Detects dangerous file upload patterns',
  defaultSeverity: 'high',
  category: 'file-system',
  tags: ['cwe', 'upload', 'file', 'security'],
  cwe: ['434'],
  references: [
    { title: 'CWE-434', url: 'https://cwe.mitre.org/data/definitions/434.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /multer\s*\(\s*\{[^}]*dest\s*:/gi, type: 'Multer without fileFilter', severity: 'medium' as const },
      { pattern: /\.originalname/gi, type: 'Using original filename', severity: 'high' as const },
      { pattern: /req\.files?\.\w+\.(?:path|name)/gi, type: 'Direct file path usage', severity: 'medium' as const },
      { pattern: /\.mimetype\s*===?\s*['"`]/gi, type: 'Client-side mimetype trust', severity: 'medium' as const },
      { pattern: /upload\.(?:single|array|fields)\s*\(/gi, type: 'File upload endpoint', severity: 'info' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-434-${findings.length + 1}`,
            ruleId: 'cwe-434-file-upload',
            severity,
            message: `File Upload - ${type}: Validate file type and sanitize filename`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['434'],
            suggestion: {
              description: 'Validate file type by content, not extension',
              example: `const upload = multer({
  fileFilter: (req, file, cb) => {
    const allowed = ['image/jpeg', 'image/png'];
    cb(null, allowed.includes(file.mimetype));
  }
});`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe434FileUpload;
