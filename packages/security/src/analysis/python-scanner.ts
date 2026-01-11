/**
 * @fileoverview Python vulnerability scanner - static analysis for Python security vulnerabilities
 * @module @nahisaho/musubix-security/analysis/python-scanner
 * @trace REQ-SEC-PYTHON-001
 */

import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import type {
  Vulnerability,
  ScanOptions,
  ScanResult,
  SourceLocation,
  Severity,
  OWASPCategory,
} from '../types/index.js';

/**
 * Generate vulnerability ID for Python
 */
let pythonVulnCounter = 0;
function generatePythonVulnId(): string {
  const date = new Date();
  const dateStr = date.toISOString().slice(0, 10).replace(/-/g, '');
  return `PY-VULN-${dateStr}-${String(++pythonVulnCounter).padStart(3, '0')}`;
}

/**
 * Reset Python vulnerability counter (for testing)
 */
export function resetPythonVulnCounter(): void {
  pythonVulnCounter = 0;
}

/**
 * Python vulnerability pattern
 */
interface PythonPattern {
  ruleId: string;
  pattern: RegExp;
  type: string;
  severity: Severity;
  cwes: string[];
  owasp: OWASPCategory[];
  description: string;
  recommendation: string;
  confidence: number;
}

/**
 * Python security patterns
 */
const PYTHON_PATTERNS: PythonPattern[] = [
  // SQL Injection (CWE-89)
  {
    ruleId: 'PY-SEC-001',
    pattern: /(?:cursor\.execute|\.execute)\s*\(\s*(?:f["']|["'].*%|["'].*\+|["'].*\.format)/gi,
    type: 'injection',
    severity: 'critical',
    cwes: ['CWE-89'],
    owasp: ['A03:2021'],
    description: 'Potential SQL injection: String formatting in SQL query',
    recommendation: 'Use parameterized queries with placeholders (?, %s) and pass parameters separately',
    confidence: 0.85,
  },
  {
    ruleId: 'PY-SEC-001',
    pattern: /(?:cursor\.execute|\.execute)\s*\(\s*["'].*\{.*\}.*["']\.format/gi,
    type: 'injection',
    severity: 'critical',
    cwes: ['CWE-89'],
    owasp: ['A03:2021'],
    description: 'Potential SQL injection: .format() in SQL query',
    recommendation: 'Use parameterized queries instead of string formatting',
    confidence: 0.9,
  },
  // Command Injection (CWE-78)
  {
    ruleId: 'PY-SEC-002',
    pattern: /os\.system\s*\(\s*(?:f["']|.*\+|.*%|.*\.format)/gi,
    type: 'command-injection',
    severity: 'critical',
    cwes: ['CWE-78'],
    owasp: ['A03:2021'],
    description: 'Potential command injection: os.system() with user input',
    recommendation: 'Use subprocess.run() with shell=False and pass arguments as a list',
    confidence: 0.9,
  },
  {
    ruleId: 'PY-SEC-002',
    pattern: /subprocess\.(?:call|run|Popen)\s*\([^)]*shell\s*=\s*True/gi,
    type: 'command-injection',
    severity: 'high',
    cwes: ['CWE-78'],
    owasp: ['A03:2021'],
    description: 'Potential command injection: subprocess with shell=True',
    recommendation: 'Avoid shell=True. Pass command as a list without shell interpretation',
    confidence: 0.8,
  },
  {
    ruleId: 'PY-SEC-002',
    pattern: /os\.popen\s*\(/gi,
    type: 'command-injection',
    severity: 'high',
    cwes: ['CWE-78'],
    owasp: ['A03:2021'],
    description: 'Deprecated os.popen() usage - vulnerable to command injection',
    recommendation: 'Use subprocess module with shell=False instead',
    confidence: 0.75,
  },
  // Code Injection (CWE-94)
  {
    ruleId: 'PY-SEC-003',
    pattern: /\beval\s*\(/gi,
    type: 'code-injection',
    severity: 'critical',
    cwes: ['CWE-94', 'CWE-95'],
    owasp: ['A03:2021'],
    description: 'Dangerous eval() usage detected',
    recommendation: 'Avoid eval(). Use ast.literal_eval() for safe literal evaluation or find alternative approaches',
    confidence: 0.95,
  },
  {
    ruleId: 'PY-SEC-003',
    pattern: /\bexec\s*\(/gi,
    type: 'code-injection',
    severity: 'critical',
    cwes: ['CWE-94'],
    owasp: ['A03:2021'],
    description: 'Dangerous exec() usage detected',
    recommendation: 'Avoid exec(). Find safer alternatives for dynamic code execution',
    confidence: 0.9,
  },
  {
    ruleId: 'PY-SEC-003',
    pattern: /compile\s*\([^)]+\)\s*$/gim,
    type: 'code-injection',
    severity: 'medium',
    cwes: ['CWE-94'],
    owasp: ['A03:2021'],
    description: 'compile() usage - verify input is not user-controlled',
    recommendation: 'Ensure compile() input is not from untrusted sources',
    confidence: 0.6,
  },
  // Path Traversal (CWE-22)
  {
    ruleId: 'PY-SEC-004',
    pattern: /open\s*\(\s*(?:f["']|.*\+|.*%|.*\.format|os\.path\.join\s*\([^)]*request)/gi,
    type: 'path-traversal',
    severity: 'high',
    cwes: ['CWE-22'],
    owasp: ['A01:2021'],
    description: 'Potential path traversal: File path from user input',
    recommendation: 'Validate and sanitize file paths. Use os.path.realpath() and verify against allowed directories',
    confidence: 0.75,
  },
  // Insecure Deserialization (CWE-502)
  {
    ruleId: 'PY-SEC-005',
    pattern: /pickle\.(?:load|loads)\s*\(/gi,
    type: 'insecure-deserialization',
    severity: 'critical',
    cwes: ['CWE-502'],
    owasp: ['A08:2021'],
    description: 'Insecure deserialization: pickle.load() can execute arbitrary code',
    recommendation: 'Never unpickle data from untrusted sources. Use JSON or other safe formats',
    confidence: 0.95,
  },
  {
    ruleId: 'PY-SEC-005',
    pattern: /yaml\.(?:load|unsafe_load)\s*\([^)]*(?:Loader\s*=\s*yaml\.(?:Loader|UnsafeLoader|FullLoader))?/gi,
    type: 'insecure-deserialization',
    severity: 'critical',
    cwes: ['CWE-502'],
    owasp: ['A08:2021'],
    description: 'Insecure YAML deserialization - use yaml.safe_load()',
    recommendation: 'Use yaml.safe_load() instead of yaml.load() or yaml.unsafe_load()',
    confidence: 0.9,
  },
  {
    ruleId: 'PY-SEC-005',
    pattern: /marshal\.loads?\s*\(/gi,
    type: 'insecure-deserialization',
    severity: 'high',
    cwes: ['CWE-502'],
    owasp: ['A08:2021'],
    description: 'marshal module can deserialize malicious data',
    recommendation: 'Avoid marshal for untrusted data. Use JSON or safe alternatives',
    confidence: 0.85,
  },
  // XXE (CWE-611)
  {
    ruleId: 'PY-SEC-006',
    pattern: /xml\.etree\.ElementTree\.(?:parse|fromstring)\s*\(/gi,
    type: 'xxe',
    severity: 'high',
    cwes: ['CWE-611'],
    owasp: ['A05:2021'],
    description: 'XML parsing may be vulnerable to XXE attacks',
    recommendation: 'Use defusedxml library or disable external entity processing',
    confidence: 0.7,
  },
  {
    ruleId: 'PY-SEC-006',
    pattern: /lxml\.etree\.(?:parse|fromstring|XML)\s*\(/gi,
    type: 'xxe',
    severity: 'high',
    cwes: ['CWE-611'],
    owasp: ['A05:2021'],
    description: 'lxml XML parsing may be vulnerable to XXE',
    recommendation: 'Set resolve_entities=False and no_network=True in parser',
    confidence: 0.75,
  },
  // SSRF (CWE-918)
  {
    ruleId: 'PY-SEC-007',
    pattern: /requests\.(?:get|post|put|delete|patch|head)\s*\(\s*(?:f["']|.*\+|.*%|.*\.format)/gi,
    type: 'ssrf',
    severity: 'high',
    cwes: ['CWE-918'],
    owasp: ['A10:2021'],
    description: 'Potential SSRF: URL constructed from user input',
    recommendation: 'Validate and whitelist allowed URLs/hosts. Block internal network access',
    confidence: 0.8,
  },
  {
    ruleId: 'PY-SEC-007',
    pattern: /urllib\.request\.urlopen\s*\(\s*(?:f["']|.*\+|.*%|.*\.format)/gi,
    type: 'ssrf',
    severity: 'high',
    cwes: ['CWE-918'],
    owasp: ['A10:2021'],
    description: 'Potential SSRF: urllib with dynamic URL',
    recommendation: 'Validate URLs against allowlist before making requests',
    confidence: 0.8,
  },
  // LDAP Injection (CWE-90)
  {
    ruleId: 'PY-SEC-008',
    pattern: /ldap\.(?:search|search_s|search_ext)\s*\([^)]*(?:f["']|.*\+|.*%|.*\.format)/gi,
    type: 'ldap-injection',
    severity: 'critical',
    cwes: ['CWE-90'],
    owasp: ['A03:2021'],
    description: 'Potential LDAP injection: Filter constructed from user input',
    recommendation: 'Use ldap.filter.escape_filter_chars() to escape special characters',
    confidence: 0.85,
  },
  // Hardcoded Secrets
  {
    ruleId: 'PY-SEC-009',
    pattern: /(?:password|secret|api_key|apikey|token|auth)\s*=\s*["'][^"']{8,}["']/gi,
    type: 'sensitive-exposure',
    severity: 'high',
    cwes: ['CWE-798'],
    owasp: ['A07:2021'],
    description: 'Hardcoded credential detected',
    recommendation: 'Use environment variables or secure vault for credentials',
    confidence: 0.7,
  },
  // Weak Cryptography (CWE-327)
  {
    ruleId: 'PY-SEC-010',
    pattern: /hashlib\.(?:md5|sha1)\s*\(/gi,
    type: 'misconfig',
    severity: 'medium',
    cwes: ['CWE-327', 'CWE-328'],
    owasp: ['A02:2021'],
    description: 'Weak hash algorithm (MD5/SHA1) - not suitable for security',
    recommendation: 'Use SHA-256 or stronger for security-sensitive hashing',
    confidence: 0.75,
  },
  {
    ruleId: 'PY-SEC-010',
    pattern: /from\s+Crypto\.Cipher\s+import\s+(?:DES|Blowfish|ARC4|XOR)/gi,
    type: 'misconfig',
    severity: 'high',
    cwes: ['CWE-327'],
    owasp: ['A02:2021'],
    description: 'Weak/deprecated encryption algorithm',
    recommendation: 'Use AES-256 or ChaCha20 for encryption',
    confidence: 0.85,
  },
  // Debug Mode (CWE-489)
  {
    ruleId: 'PY-SEC-011',
    pattern: /app\.run\s*\([^)]*debug\s*=\s*True/gi,
    type: 'misconfig',
    severity: 'high',
    cwes: ['CWE-489'],
    owasp: ['A05:2021'],
    description: 'Flask debug mode enabled - exposes debugger in production',
    recommendation: 'Disable debug mode in production (debug=False)',
    confidence: 0.9,
  },
  {
    ruleId: 'PY-SEC-011',
    pattern: /DEBUG\s*=\s*True/gi,
    type: 'misconfig',
    severity: 'medium',
    cwes: ['CWE-489'],
    owasp: ['A05:2021'],
    description: 'Debug mode appears to be enabled',
    recommendation: 'Ensure DEBUG is False in production',
    confidence: 0.6,
  },
  // ReDoS (CWE-1333)
  {
    ruleId: 'PY-SEC-012',
    pattern: /re\.(?:match|search|findall|sub)\s*\(\s*r?["'].*(?:\(\.\*\)\+|\(\.\+\)\+|\([^)]+\+\)\+)/gi,
    type: 'redos',
    severity: 'high',
    cwes: ['CWE-1333'],
    owasp: ['A06:2021'],
    description: 'Potential ReDoS: Regex with catastrophic backtracking pattern',
    recommendation: 'Rewrite regex to avoid nested quantifiers. Consider using re2 library',
    confidence: 0.8,
  },
  // Template Injection (CWE-1336)
  {
    ruleId: 'PY-SEC-013',
    pattern: /(?:Template|render_template_string)\s*\(\s*(?:f["']|.*\+|.*%|.*\.format)/gi,
    type: 'code-injection',
    severity: 'critical',
    cwes: ['CWE-1336', 'CWE-94'],
    owasp: ['A03:2021'],
    description: 'Potential Server-Side Template Injection (SSTI)',
    recommendation: 'Never pass user input directly to template rendering. Use render_template() with separate variables',
    confidence: 0.85,
  },
  // Assert in production (CWE-617)
  {
    ruleId: 'PY-SEC-014',
    pattern: /\bassert\s+.*(?:request|input|user|data|param)/gi,
    type: 'misconfig',
    severity: 'medium',
    cwes: ['CWE-617'],
    owasp: ['A05:2021'],
    description: 'assert used for input validation - disabled with -O flag',
    recommendation: 'Use proper validation instead of assert for security checks',
    confidence: 0.7,
  },
];

/**
 * Get source location from line number
 */
function getLocation(filePath: string, content: string, match: RegExpExecArray): SourceLocation {
  const lines = content.substring(0, match.index).split('\n');
  const startLine = lines.length;
  const startColumn = lines[lines.length - 1].length;
  const matchLines = match[0].split('\n');
  const endLine = startLine + matchLines.length - 1;
  const endColumn = matchLines.length === 1 
    ? startColumn + match[0].length 
    : matchLines[matchLines.length - 1].length;

  return {
    file: filePath,
    startLine,
    endLine,
    startColumn,
    endColumn,
  };
}

/**
 * Extract code snippet around match
 */
function extractSnippet(content: string, match: RegExpExecArray): string {
  const lines = content.split('\n');
  const matchLines = content.substring(0, match.index).split('\n');
  const lineNum = matchLines.length - 1;
  const start = Math.max(0, lineNum - 1);
  const end = Math.min(lines.length, lineNum + 3);
  return lines.slice(start, end).join('\n');
}

/**
 * Python vulnerability scanner
 */
export class PythonScanner {
  private patterns: PythonPattern[];

  constructor() {
    this.patterns = [...PYTHON_PATTERNS];
  }

  /**
   * Scan a single Python file
   */
  async scanFile(filePath: string): Promise<Vulnerability[]> {
    const content = await fs.readFile(filePath, 'utf-8');
    return this.scanContent(content, filePath);
  }

  /**
   * Scan Python content
   */
  scanContent(content: string, filePath: string = 'unknown.py'): Vulnerability[] {
    const vulnerabilities: Vulnerability[] = [];

    for (const patternDef of this.patterns) {
      // Reset regex lastIndex for global patterns
      patternDef.pattern.lastIndex = 0;
      
      let match: RegExpExecArray | null;
      while ((match = patternDef.pattern.exec(content)) !== null) {
        vulnerabilities.push({
          id: generatePythonVulnId(),
          type: patternDef.type as any,
          severity: patternDef.severity,
          cwes: patternDef.cwes,
          owasp: patternDef.owasp,
          location: getLocation(filePath, content, match),
          description: patternDef.description,
          recommendation: patternDef.recommendation,
          confidence: patternDef.confidence,
          ruleId: patternDef.ruleId,
          codeSnippet: extractSnippet(content, match),
          detectedAt: new Date(),
        });
      }
    }

    return vulnerabilities;
  }

  /**
   * Scan a directory for Python files
   */
  async scanDirectory(rootPath: string, options?: ScanOptions): Promise<ScanResult> {
    const startTime = Date.now();
    const vulnerabilities: Vulnerability[] = [];
    let scannedFiles = 0;
    let skippedFiles = 0;

    const scanDir = async (dirPath: string) => {
      const entries = await fs.readdir(dirPath, { withFileTypes: true });

      for (const entry of entries) {
        const fullPath = path.join(dirPath, entry.name);

        if (entry.isDirectory()) {
          // Skip common non-source directories
          if (['__pycache__', '.git', 'node_modules', 'venv', '.venv', 'env', '.env'].includes(entry.name)) {
            continue;
          }
          await scanDir(fullPath);
        } else if (entry.isFile() && entry.name.endsWith('.py')) {
          // Apply exclude patterns
          if (options?.excludePatterns?.some(p => fullPath.includes(p))) {
            skippedFiles++;
            continue;
          }

          try {
            const fileVulns = await this.scanFile(fullPath);
            vulnerabilities.push(...fileVulns);
            scannedFiles++;
          } catch (error) {
            console.warn(`Warning: Failed to scan ${fullPath}: ${error}`);
            skippedFiles++;
          }
        }
      }
    };

    await scanDir(rootPath);

    const duration = Date.now() - startTime;

    return {
      vulnerabilities,
      scannedFiles,
      skippedFiles,
      duration,
      timestamp: new Date(),
      options: options ?? {},
      summary: {
        critical: vulnerabilities.filter(v => v.severity === 'critical').length,
        high: vulnerabilities.filter(v => v.severity === 'high').length,
        medium: vulnerabilities.filter(v => v.severity === 'medium').length,
        low: vulnerabilities.filter(v => v.severity === 'low').length,
        info: vulnerabilities.filter(v => v.severity === 'info').length,
        total: vulnerabilities.length,
      },
    };
  }

  /**
   * Add custom pattern
   */
  addPattern(pattern: PythonPattern): void {
    this.patterns.push(pattern);
  }

  /**
   * Get rule IDs
   */
  getRuleIds(): string[] {
    return [...new Set(this.patterns.map(p => p.ruleId))];
  }

  /**
   * Get rule count
   */
  getRuleCount(): number {
    return this.getRuleIds().length;
  }
}

/**
 * Create Python scanner
 */
export function createPythonScanner(): PythonScanner {
  return new PythonScanner();
}
