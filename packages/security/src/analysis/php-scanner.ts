/**
 * @fileoverview PHP vulnerability scanner - static analysis for PHP security vulnerabilities
 * @module @nahisaho/musubix-security/analysis/php-scanner
 * @trace REQ-SEC-PHP-001
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
 * Generate vulnerability ID for PHP
 */
let phpVulnCounter = 0;
function generatePhpVulnId(): string {
  const date = new Date();
  const dateStr = date.toISOString().slice(0, 10).replace(/-/g, '');
  return `PHP-VULN-${dateStr}-${String(++phpVulnCounter).padStart(3, '0')}`;
}

/**
 * Reset PHP vulnerability counter (for testing)
 */
export function resetPhpVulnCounter(): void {
  phpVulnCounter = 0;
}

/**
 * PHP vulnerability pattern
 */
interface PhpPattern {
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
 * PHP security patterns
 */
const PHP_PATTERNS: PhpPattern[] = [
  // SQL Injection (CWE-89)
  {
    ruleId: 'PHP-SEC-001',
    pattern: /mysql_query\s*\(\s*["'].*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'injection',
    severity: 'critical',
    cwes: ['CWE-89'],
    owasp: ['A03:2021'],
    description: 'SQL injection: Deprecated mysql_query with user input',
    recommendation: 'Use PDO prepared statements or mysqli with parameterized queries',
    confidence: 0.95,
  },
  {
    ruleId: 'PHP-SEC-001',
    pattern: /mysqli_query\s*\([^,]+,\s*["'].*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'injection',
    severity: 'critical',
    cwes: ['CWE-89'],
    owasp: ['A03:2021'],
    description: 'SQL injection: mysqli_query with user input concatenation',
    recommendation: 'Use mysqli_prepare() with mysqli_stmt_bind_param()',
    confidence: 0.9,
  },
  {
    ruleId: 'PHP-SEC-001',
    pattern: /->query\s*\(\s*["'].*(?:\.\s*\$|\$_(?:GET|POST|REQUEST|COOKIE))/gi,
    type: 'injection',
    severity: 'critical',
    cwes: ['CWE-89'],
    owasp: ['A03:2021'],
    description: 'SQL injection: query() with string concatenation',
    recommendation: 'Use prepare() and bind parameters instead of query()',
    confidence: 0.85,
  },
  {
    ruleId: 'PHP-SEC-001',
    pattern: /->exec\s*\(\s*["'].*(?:\.\s*\$|\$_(?:GET|POST|REQUEST|COOKIE))/gi,
    type: 'injection',
    severity: 'critical',
    cwes: ['CWE-89'],
    owasp: ['A03:2021'],
    description: 'SQL injection: exec() with string concatenation',
    recommendation: 'Use prepare() and execute() with bound parameters',
    confidence: 0.85,
  },
  // XSS (CWE-79)
  {
    ruleId: 'PHP-SEC-002',
    pattern: /echo\s+\$_(?:GET|POST|REQUEST|COOKIE)\s*\[/gi,
    type: 'xss',
    severity: 'high',
    cwes: ['CWE-79'],
    owasp: ['A03:2021'],
    description: 'Reflected XSS: Echoing user input without sanitization',
    recommendation: 'Use htmlspecialchars() or htmlentities() with ENT_QUOTES',
    confidence: 0.95,
  },
  {
    ruleId: 'PHP-SEC-002',
    pattern: /print\s+\$_(?:GET|POST|REQUEST|COOKIE)\s*\[/gi,
    type: 'xss',
    severity: 'high',
    cwes: ['CWE-79'],
    owasp: ['A03:2021'],
    description: 'Reflected XSS: Printing user input without sanitization',
    recommendation: 'Use htmlspecialchars($input, ENT_QUOTES, "UTF-8")',
    confidence: 0.95,
  },
  {
    ruleId: 'PHP-SEC-002',
    pattern: /<\?=\s*\$_(?:GET|POST|REQUEST|COOKIE)\s*\[/gi,
    type: 'xss',
    severity: 'high',
    cwes: ['CWE-79'],
    owasp: ['A03:2021'],
    description: 'Reflected XSS: Short echo tag with user input',
    recommendation: 'Sanitize output with htmlspecialchars()',
    confidence: 0.95,
  },
  // Command Injection (CWE-78)
  {
    ruleId: 'PHP-SEC-003',
    pattern: /(?:exec|system|passthru|shell_exec|popen|proc_open)\s*\(\s*.*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'command-injection',
    severity: 'critical',
    cwes: ['CWE-78'],
    owasp: ['A03:2021'],
    description: 'Command injection: System function with user input',
    recommendation: 'Use escapeshellarg() and escapeshellcmd(). Avoid system functions if possible',
    confidence: 0.95,
  },
  {
    ruleId: 'PHP-SEC-003',
    pattern: /`.*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'command-injection',
    severity: 'critical',
    cwes: ['CWE-78'],
    owasp: ['A03:2021'],
    description: 'Command injection: Backtick operator with user input',
    recommendation: 'Avoid backtick operator. Use escapeshellarg() for any external command execution',
    confidence: 0.9,
  },
  // Code Injection (CWE-94)
  {
    ruleId: 'PHP-SEC-004',
    pattern: /\beval\s*\(\s*.*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'code-injection',
    severity: 'critical',
    cwes: ['CWE-94', 'CWE-95'],
    owasp: ['A03:2021'],
    description: 'Code injection: eval() with user input',
    recommendation: 'Never use eval() with user input. Find alternative approaches',
    confidence: 0.98,
  },
  {
    ruleId: 'PHP-SEC-004',
    pattern: /\beval\s*\(/gi,
    type: 'code-injection',
    severity: 'high',
    cwes: ['CWE-94'],
    owasp: ['A03:2021'],
    description: 'Dangerous eval() usage detected',
    recommendation: 'Avoid eval(). Use safer alternatives for dynamic code',
    confidence: 0.8,
  },
  {
    ruleId: 'PHP-SEC-004',
    pattern: /create_function\s*\(/gi,
    type: 'code-injection',
    severity: 'high',
    cwes: ['CWE-94'],
    owasp: ['A03:2021'],
    description: 'Deprecated create_function() is vulnerable to injection',
    recommendation: 'Use anonymous functions (closures) instead',
    confidence: 0.85,
  },
  {
    ruleId: 'PHP-SEC-004',
    pattern: /preg_replace\s*\(\s*["']\/.*\/e["']/gi,
    type: 'code-injection',
    severity: 'critical',
    cwes: ['CWE-94'],
    owasp: ['A03:2021'],
    description: 'preg_replace with /e modifier executes code',
    recommendation: 'Use preg_replace_callback() instead of /e modifier',
    confidence: 0.95,
  },
  // File Inclusion (CWE-98)
  {
    ruleId: 'PHP-SEC-005',
    pattern: /(?:include|include_once|require|require_once)\s*\(\s*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'path-traversal',
    severity: 'critical',
    cwes: ['CWE-98', 'CWE-22'],
    owasp: ['A03:2021'],
    description: 'Local/Remote File Inclusion via user input',
    recommendation: 'Never use user input in file inclusion. Use a whitelist of allowed files',
    confidence: 0.98,
  },
  {
    ruleId: 'PHP-SEC-005',
    pattern: /(?:include|include_once|require|require_once)\s*\(\s*\$/gi,
    type: 'path-traversal',
    severity: 'high',
    cwes: ['CWE-98'],
    owasp: ['A03:2021'],
    description: 'Dynamic file inclusion with variable',
    recommendation: 'Validate against whitelist before including dynamic files',
    confidence: 0.7,
  },
  // Path Traversal (CWE-22)
  {
    ruleId: 'PHP-SEC-006',
    pattern: /(?:file_get_contents|file_put_contents|fopen|readfile|file)\s*\(\s*.*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'path-traversal',
    severity: 'high',
    cwes: ['CWE-22'],
    owasp: ['A01:2021'],
    description: 'Path traversal: File operation with user input',
    recommendation: 'Use basename() and realpath() to validate file paths',
    confidence: 0.85,
  },
  {
    ruleId: 'PHP-SEC-006',
    pattern: /unlink\s*\(\s*.*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'path-traversal',
    severity: 'critical',
    cwes: ['CWE-22'],
    owasp: ['A01:2021'],
    description: 'Arbitrary file deletion via user input',
    recommendation: 'Strictly validate file paths. Never allow user-controlled file deletion paths',
    confidence: 0.95,
  },
  // Insecure Deserialization (CWE-502)
  {
    ruleId: 'PHP-SEC-007',
    pattern: /unserialize\s*\(\s*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'insecure-deserialization',
    severity: 'critical',
    cwes: ['CWE-502'],
    owasp: ['A08:2021'],
    description: 'Insecure deserialization: unserialize() with user input',
    recommendation: 'Use JSON instead of serialize/unserialize. If needed, use allowed_classes option',
    confidence: 0.98,
  },
  {
    ruleId: 'PHP-SEC-007',
    pattern: /unserialize\s*\(/gi,
    type: 'insecure-deserialization',
    severity: 'medium',
    cwes: ['CWE-502'],
    owasp: ['A08:2021'],
    description: 'unserialize() usage - verify input source',
    recommendation: 'Ensure data is from trusted source. Use allowed_classes parameter',
    confidence: 0.6,
  },
  // SSRF (CWE-918)
  {
    ruleId: 'PHP-SEC-008',
    pattern: /file_get_contents\s*\(\s*["']https?:\/\/.*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'ssrf',
    severity: 'high',
    cwes: ['CWE-918'],
    owasp: ['A10:2021'],
    description: 'SSRF: URL from user input in file_get_contents()',
    recommendation: 'Validate URLs against allowlist. Block internal network access',
    confidence: 0.9,
  },
  {
    ruleId: 'PHP-SEC-008',
    pattern: /curl_setopt\s*\([^,]+,\s*CURLOPT_URL\s*,\s*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'ssrf',
    severity: 'high',
    cwes: ['CWE-918'],
    owasp: ['A10:2021'],
    description: 'SSRF: User-controlled URL in cURL',
    recommendation: 'Validate and sanitize URLs. Use URL allowlists',
    confidence: 0.9,
  },
  // XXE (CWE-611)
  {
    ruleId: 'PHP-SEC-009',
    pattern: /simplexml_load_string\s*\(\s*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'xxe',
    severity: 'critical',
    cwes: ['CWE-611'],
    owasp: ['A05:2021'],
    description: 'XXE: XML parsing of user input',
    recommendation: 'Disable external entities: libxml_disable_entity_loader(true)',
    confidence: 0.95,
  },
  {
    ruleId: 'PHP-SEC-009',
    pattern: /DOMDocument\s*\(\).*loadXML\s*\(\s*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'xxe',
    severity: 'critical',
    cwes: ['CWE-611'],
    owasp: ['A05:2021'],
    description: 'XXE: DOMDocument loading user-controlled XML',
    recommendation: 'Set LIBXML_NOENT | LIBXML_DTDLOAD options to disable entities',
    confidence: 0.9,
  },
  // LDAP Injection (CWE-90)
  {
    ruleId: 'PHP-SEC-010',
    pattern: /ldap_search\s*\([^,]+,[^,]+,\s*.*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'ldap-injection',
    severity: 'critical',
    cwes: ['CWE-90'],
    owasp: ['A03:2021'],
    description: 'LDAP injection: User input in search filter',
    recommendation: 'Escape special characters with ldap_escape()',
    confidence: 0.9,
  },
  // Hardcoded Secrets (CWE-798)
  {
    ruleId: 'PHP-SEC-011',
    pattern: /\$(?:password|secret|api_key|apikey|token|auth)\s*=\s*["'][^"']{8,}["']/gi,
    type: 'sensitive-exposure',
    severity: 'high',
    cwes: ['CWE-798'],
    owasp: ['A07:2021'],
    description: 'Hardcoded credential detected',
    recommendation: 'Use environment variables or config files outside webroot',
    confidence: 0.7,
  },
  // Weak Cryptography (CWE-327)
  {
    ruleId: 'PHP-SEC-012',
    pattern: /md5\s*\(\s*\$(?:password|pass|pwd)/gi,
    type: 'misconfig',
    severity: 'high',
    cwes: ['CWE-327', 'CWE-328'],
    owasp: ['A02:2021'],
    description: 'Weak password hashing: MD5 is not suitable for passwords',
    recommendation: 'Use password_hash() with PASSWORD_DEFAULT or PASSWORD_ARGON2ID',
    confidence: 0.95,
  },
  {
    ruleId: 'PHP-SEC-012',
    pattern: /sha1\s*\(\s*\$(?:password|pass|pwd)/gi,
    type: 'misconfig',
    severity: 'high',
    cwes: ['CWE-327'],
    owasp: ['A02:2021'],
    description: 'Weak password hashing: SHA1 is not suitable for passwords',
    recommendation: 'Use password_hash() for secure password storage',
    confidence: 0.95,
  },
  // Session Fixation (CWE-384)
  {
    ruleId: 'PHP-SEC-013',
    pattern: /session_id\s*\(\s*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'misconfig',
    severity: 'critical',
    cwes: ['CWE-384'],
    owasp: ['A07:2021'],
    description: 'Session fixation: Setting session ID from user input',
    recommendation: 'Never accept session IDs from user input. Use session_regenerate_id()',
    confidence: 0.95,
  },
  // Open Redirect (CWE-601)
  {
    ruleId: 'PHP-SEC-014',
    pattern: /header\s*\(\s*["']Location:\s*["']\s*\.\s*\$_(?:GET|POST|REQUEST|COOKIE)/gi,
    type: 'misconfig',
    severity: 'medium',
    cwes: ['CWE-601'],
    owasp: ['A03:2021'],
    description: 'Open redirect: User-controlled redirect destination',
    recommendation: 'Validate redirect URLs against whitelist of allowed domains',
    confidence: 0.85,
  },
  // Information Disclosure
  {
    ruleId: 'PHP-SEC-015',
    pattern: /(?:var_dump|print_r|debug_print_backtrace)\s*\(/gi,
    type: 'sensitive-exposure',
    severity: 'low',
    cwes: ['CWE-209'],
    owasp: ['A04:2021'],
    description: 'Debug function may expose sensitive information',
    recommendation: 'Remove or disable debug output in production',
    confidence: 0.5,
  },
  {
    ruleId: 'PHP-SEC-015',
    pattern: /error_reporting\s*\(\s*E_ALL\s*\)/gi,
    type: 'misconfig',
    severity: 'low',
    cwes: ['CWE-209'],
    owasp: ['A05:2021'],
    description: 'Full error reporting enabled - may leak information',
    recommendation: 'Disable display_errors in production, log errors instead',
    confidence: 0.6,
  },
  // Insecure Cookie
  {
    ruleId: 'PHP-SEC-016',
    pattern: /setcookie\s*\([^)]+\)\s*(?!.*(?:httponly|secure))/gi,
    type: 'misconfig',
    severity: 'medium',
    cwes: ['CWE-614', 'CWE-1004'],
    owasp: ['A05:2021'],
    description: 'Cookie without secure flags',
    recommendation: 'Set httponly and secure flags for sensitive cookies',
    confidence: 0.6,
  },
];

/**
 * Get source location from match
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
 * PHP vulnerability scanner
 */
export class PhpScanner {
  private patterns: PhpPattern[];

  constructor() {
    this.patterns = [...PHP_PATTERNS];
  }

  /**
   * Scan a single PHP file
   */
  async scanFile(filePath: string): Promise<Vulnerability[]> {
    const content = await fs.readFile(filePath, 'utf-8');
    return this.scanContent(content, filePath);
  }

  /**
   * Scan PHP content
   */
  scanContent(content: string, filePath: string = 'unknown.php'): Vulnerability[] {
    const vulnerabilities: Vulnerability[] = [];

    for (const patternDef of this.patterns) {
      // Reset regex lastIndex for global patterns
      patternDef.pattern.lastIndex = 0;
      
      let match: RegExpExecArray | null;
      while ((match = patternDef.pattern.exec(content)) !== null) {
        vulnerabilities.push({
          id: generatePhpVulnId(),
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
   * Scan a directory for PHP files
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
          if (['.git', 'node_modules', 'vendor', 'cache', 'tmp'].includes(entry.name)) {
            continue;
          }
          await scanDir(fullPath);
        } else if (entry.isFile() && (entry.name.endsWith('.php') || entry.name.endsWith('.phtml'))) {
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
  addPattern(pattern: PhpPattern): void {
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
 * Create PHP scanner
 */
export function createPhpScanner(): PhpScanner {
  return new PhpScanner();
}
