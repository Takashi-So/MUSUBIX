/**
 * Security Scanner
 * 
 * Scans code for security vulnerabilities
 * 
 * @packageDocumentation
 * @module codegen/security-scanner
 * 
 * @see REQ-COD-006 - Security Analysis
 * @see Article VII - Security Standards
 */

/**
 * Vulnerability severity
 */
export type VulnerabilitySeverity = 'critical' | 'high' | 'medium' | 'low' | 'info';

/**
 * Vulnerability category
 */
export type VulnerabilityCategory =
  | 'injection'
  | 'xss'
  | 'auth'
  | 'crypto'
  | 'sensitive-data'
  | 'access-control'
  | 'misconfiguration'
  | 'dependencies'
  | 'secrets';

/**
 * Security vulnerability
 */
export interface SecurityVulnerability {
  /** Vulnerability ID */
  id: string;
  /** Rule ID */
  ruleId: string;
  /** Severity */
  severity: VulnerabilitySeverity;
  /** Category */
  category: VulnerabilityCategory;
  /** Title */
  title: string;
  /** Description */
  description: string;
  /** File path */
  file?: string;
  /** Line number */
  line?: number;
  /** Column */
  column?: number;
  /** Code snippet */
  snippet?: string;
  /** CWE ID */
  cweId?: string;
  /** OWASP category */
  owasp?: string;
  /** Remediation */
  remediation: string;
  /** References */
  references?: string[];
}

/**
 * Security scan result
 */
export interface SecurityScanResult {
  /** File scanned */
  file: string;
  /** Vulnerabilities found */
  vulnerabilities: SecurityVulnerability[];
  /** Scan time */
  scanTime: number;
  /** Summary */
  summary: SecuritySummary;
}

/**
 * Security summary
 */
export interface SecuritySummary {
  /** Total vulnerabilities */
  total: number;
  /** By severity */
  bySeverity: Record<VulnerabilitySeverity, number>;
  /** By category */
  byCategory: Record<VulnerabilityCategory, number>;
  /** Risk score (0-100) */
  riskScore: number;
  /** Pass/fail */
  passed: boolean;
}

/**
 * Security rule
 */
export interface SecurityRule {
  /** Rule ID */
  id: string;
  /** Rule name */
  name: string;
  /** Category */
  category: VulnerabilityCategory;
  /** Default severity */
  severity: VulnerabilitySeverity;
  /** Description */
  description: string;
  /** Detection pattern */
  pattern: RegExp;
  /** CWE ID */
  cweId?: string;
  /** OWASP category */
  owasp?: string;
  /** Remediation advice */
  remediation: string;
  /** Languages applicable */
  languages?: string[];
  /** Is enabled */
  enabled: boolean;
}

/**
 * Security scanner configuration
 */
export interface SecurityScannerConfig {
  /** Severity threshold */
  severityThreshold: VulnerabilitySeverity;
  /** Categories to scan */
  categories: VulnerabilityCategory[];
  /** Custom rules */
  customRules?: SecurityRule[];
  /** Fail on findings */
  failOnFindings: boolean;
  /** Risk score threshold */
  riskScoreThreshold: number;
}

/**
 * Default configuration
 */
export const DEFAULT_SCANNER_CONFIG: SecurityScannerConfig = {
  severityThreshold: 'medium',
  categories: [
    'injection',
    'xss',
    'auth',
    'crypto',
    'sensitive-data',
    'access-control',
    'secrets',
  ],
  failOnFindings: true,
  riskScoreThreshold: 70,
};

/**
 * Built-in security rules
 */
const SECURITY_RULES: SecurityRule[] = [
  // Injection
  {
    id: 'sql-injection',
    name: 'SQL Injection',
    category: 'injection',
    severity: 'critical',
    description: 'Possible SQL injection vulnerability',
    pattern: /(?:execute|query)\s*\(\s*[`'"].*\$\{|(?:execute|query)\s*\(\s*.*\+\s*(?:req\.|params\.|query\.)/gi,
    cweId: 'CWE-89',
    owasp: 'A03:2021',
    remediation: 'Use parameterized queries or prepared statements',
    enabled: true,
  },
  {
    id: 'command-injection',
    name: 'Command Injection',
    category: 'injection',
    severity: 'critical',
    description: 'Possible command injection vulnerability',
    pattern: /(?:exec|spawn|execSync|execFile)\s*\(\s*[`'"]?.*\$\{|(?:exec|spawn)\s*\(\s*.*\+/gi,
    cweId: 'CWE-78',
    owasp: 'A03:2021',
    remediation: 'Avoid executing shell commands with user input. Use safe alternatives.',
    enabled: true,
  },
  {
    id: 'path-traversal',
    name: 'Path Traversal',
    category: 'injection',
    severity: 'high',
    description: 'Possible path traversal vulnerability',
    pattern: /(?:readFile|writeFile|readdir|access|stat)\s*\(\s*(?:req\.|params\.|query\.|.*\+)/gi,
    cweId: 'CWE-22',
    owasp: 'A01:2021',
    remediation: 'Validate and sanitize file paths. Use path.resolve() and verify within allowed directory.',
    enabled: true,
  },
  
  // XSS
  {
    id: 'xss-innerhtml',
    name: 'XSS via innerHTML',
    category: 'xss',
    severity: 'high',
    description: 'Possible XSS vulnerability via innerHTML',
    pattern: /\.innerHTML\s*=\s*(?!['"`])/gi,
    cweId: 'CWE-79',
    owasp: 'A03:2021',
    remediation: 'Use textContent or sanitize HTML before setting innerHTML',
    languages: ['javascript', 'typescript'],
    enabled: true,
  },
  {
    id: 'xss-dangerouslysetinnerhtml',
    name: 'XSS via dangerouslySetInnerHTML',
    category: 'xss',
    severity: 'high',
    description: 'Possible XSS via React dangerouslySetInnerHTML',
    pattern: /dangerouslySetInnerHTML\s*=\s*\{\s*\{\s*__html\s*:/gi,
    cweId: 'CWE-79',
    owasp: 'A03:2021',
    remediation: 'Sanitize HTML content before using dangerouslySetInnerHTML',
    languages: ['javascript', 'typescript'],
    enabled: true,
  },
  {
    id: 'xss-document-write',
    name: 'XSS via document.write',
    category: 'xss',
    severity: 'high',
    description: 'Possible XSS via document.write',
    pattern: /document\.write\s*\(/gi,
    cweId: 'CWE-79',
    owasp: 'A03:2021',
    remediation: 'Avoid document.write. Use DOM manipulation methods instead.',
    languages: ['javascript', 'typescript'],
    enabled: true,
  },

  // Crypto
  {
    id: 'weak-hash-md5',
    name: 'Weak Hash Algorithm (MD5)',
    category: 'crypto',
    severity: 'high',
    description: 'Use of weak hash algorithm MD5',
    pattern: /createHash\s*\(\s*['"]md5['"]\s*\)/gi,
    cweId: 'CWE-328',
    owasp: 'A02:2021',
    remediation: 'Use stronger hash algorithms like SHA-256 or SHA-3',
    enabled: true,
  },
  {
    id: 'weak-hash-sha1',
    name: 'Weak Hash Algorithm (SHA1)',
    category: 'crypto',
    severity: 'medium',
    description: 'Use of weak hash algorithm SHA1',
    pattern: /createHash\s*\(\s*['"]sha1['"]\s*\)/gi,
    cweId: 'CWE-328',
    owasp: 'A02:2021',
    remediation: 'Use stronger hash algorithms like SHA-256 or SHA-3',
    enabled: true,
  },
  {
    id: 'weak-random',
    name: 'Weak Random Number Generator',
    category: 'crypto',
    severity: 'medium',
    description: 'Use of Math.random() for security-sensitive operations',
    pattern: /Math\.random\s*\(\s*\)/gi,
    cweId: 'CWE-338',
    owasp: 'A02:2021',
    remediation: 'Use crypto.randomBytes() or crypto.getRandomValues() for security purposes',
    enabled: true,
  },
  {
    id: 'hardcoded-iv',
    name: 'Hardcoded IV',
    category: 'crypto',
    severity: 'high',
    description: 'Hardcoded initialization vector in cryptographic operation',
    pattern: /(?:createCipheriv|createDecipheriv)\s*\([^,]+,\s*[^,]+,\s*(?:Buffer\.from\s*\(\s*)?['"][^'"]+['"]/gi,
    cweId: 'CWE-329',
    owasp: 'A02:2021',
    remediation: 'Generate a random IV for each encryption operation',
    enabled: true,
  },

  // Sensitive Data
  {
    id: 'hardcoded-password',
    name: 'Hardcoded Password',
    category: 'secrets',
    severity: 'critical',
    description: 'Possible hardcoded password in code',
    pattern: /(?:password|passwd|pwd|secret)\s*[=:]\s*['"][^'"]{4,}['"]/gi,
    cweId: 'CWE-798',
    owasp: 'A07:2021',
    remediation: 'Store passwords in environment variables or secure secrets management',
    enabled: true,
  },
  {
    id: 'hardcoded-api-key',
    name: 'Hardcoded API Key',
    category: 'secrets',
    severity: 'critical',
    description: 'Possible hardcoded API key in code',
    pattern: /(?:api[_-]?key|apikey|api[_-]?secret|auth[_-]?token)\s*[=:]\s*['"][^'"]{8,}['"]/gi,
    cweId: 'CWE-798',
    owasp: 'A07:2021',
    remediation: 'Store API keys in environment variables or secure secrets management',
    enabled: true,
  },
  {
    id: 'aws-credentials',
    name: 'AWS Credentials',
    category: 'secrets',
    severity: 'critical',
    description: 'Possible AWS credentials in code',
    pattern: /(?:AKIA[0-9A-Z]{16})|(?:aws[_-]?(?:access[_-]?key|secret)[_-]?(?:id)?)\s*[=:]\s*['"][^'"]+['"]/gi,
    cweId: 'CWE-798',
    owasp: 'A07:2021',
    remediation: 'Use AWS IAM roles or environment variables for credentials',
    enabled: true,
  },
  {
    id: 'private-key',
    name: 'Private Key Exposure',
    category: 'secrets',
    severity: 'critical',
    description: 'Possible private key in code',
    pattern: /-----BEGIN\s+(?:RSA\s+)?PRIVATE\s+KEY-----/gi,
    cweId: 'CWE-321',
    owasp: 'A07:2021',
    remediation: 'Store private keys in secure key management systems',
    enabled: true,
  },

  // Authentication
  {
    id: 'jwt-none-algorithm',
    name: 'JWT None Algorithm',
    category: 'auth',
    severity: 'critical',
    description: 'JWT with none algorithm allows token forgery',
    pattern: /algorithm\s*[=:]\s*['"]none['"]/gi,
    cweId: 'CWE-347',
    owasp: 'A07:2021',
    remediation: 'Always specify a secure algorithm like RS256 or HS256',
    enabled: true,
  },
  {
    id: 'jwt-weak-secret',
    name: 'JWT Weak Secret',
    category: 'auth',
    severity: 'high',
    description: 'JWT signed with potentially weak secret',
    pattern: /jwt\.sign\s*\([^,]+,\s*['"][^'"]{1,15}['"]/gi,
    cweId: 'CWE-326',
    owasp: 'A07:2021',
    remediation: 'Use a strong, random secret at least 256 bits long',
    enabled: true,
  },
  {
    id: 'basic-auth-header',
    name: 'Basic Auth in Code',
    category: 'auth',
    severity: 'medium',
    description: 'Hardcoded basic authentication credentials',
    pattern: /Authorization['"]\s*[=:]\s*['"]Basic\s+[A-Za-z0-9+/=]+['"]/gi,
    cweId: 'CWE-798',
    owasp: 'A07:2021',
    remediation: 'Use secure credential storage and avoid hardcoding auth headers',
    enabled: true,
  },

  // Misconfiguration
  {
    id: 'cors-allow-all',
    name: 'CORS Allow All Origins',
    category: 'misconfiguration',
    severity: 'medium',
    description: 'CORS configured to allow all origins',
    pattern: /(?:Access-Control-Allow-Origin|origin)\s*[=:]\s*['"][*]['"]/gi,
    cweId: 'CWE-942',
    owasp: 'A05:2021',
    remediation: 'Restrict CORS to specific trusted origins',
    enabled: true,
  },
  {
    id: 'debug-mode',
    name: 'Debug Mode Enabled',
    category: 'misconfiguration',
    severity: 'low',
    description: 'Debug mode appears to be enabled',
    pattern: /(?:debug|DEBUG)\s*[=:]\s*(?:true|1|['"]true['"])/gi,
    cweId: 'CWE-489',
    owasp: 'A05:2021',
    remediation: 'Disable debug mode in production',
    enabled: true,
  },
  {
    id: 'disable-ssl-verify',
    name: 'SSL Verification Disabled',
    category: 'misconfiguration',
    severity: 'high',
    description: 'SSL certificate verification is disabled',
    pattern: /(?:rejectUnauthorized|verify|strict[_-]?ssl)\s*[=:]\s*false/gi,
    cweId: 'CWE-295',
    owasp: 'A07:2021',
    remediation: 'Enable SSL verification in production',
    enabled: true,
  },

  // Access Control
  {
    id: 'insecure-redirect',
    name: 'Insecure Redirect',
    category: 'access-control',
    severity: 'medium',
    description: 'Possible open redirect vulnerability',
    pattern: /(?:res\.redirect|location\.href|window\.location)\s*[=(]\s*(?:req\.|params\.|query\.)/gi,
    cweId: 'CWE-601',
    owasp: 'A01:2021',
    remediation: 'Validate redirect URLs against a whitelist of allowed destinations',
    enabled: true,
  },

  // Other
  {
    id: 'eval-usage',
    name: 'Eval Usage',
    category: 'injection',
    severity: 'high',
    description: 'Use of eval() is dangerous',
    pattern: /\beval\s*\(/gi,
    cweId: 'CWE-95',
    owasp: 'A03:2021',
    remediation: 'Avoid eval(). Use safer alternatives like JSON.parse()',
    enabled: true,
  },
  {
    id: 'new-function',
    name: 'New Function Constructor',
    category: 'injection',
    severity: 'high',
    description: 'Use of Function constructor is similar to eval()',
    pattern: /new\s+Function\s*\(/gi,
    cweId: 'CWE-95',
    owasp: 'A03:2021',
    remediation: 'Avoid new Function(). Use regular functions instead.',
    enabled: true,
  },
];

/**
 * Security Scanner
 */
export class SecurityScanner {
  private config: SecurityScannerConfig;
  private rules: SecurityRule[];

  constructor(config?: Partial<SecurityScannerConfig>) {
    this.config = { ...DEFAULT_SCANNER_CONFIG, ...config };
    this.rules = [...SECURITY_RULES];
    
    if (this.config.customRules) {
      this.rules.push(...this.config.customRules);
    }
  }

  /**
   * Scan code for vulnerabilities
   */
  scan(code: string, file: string, language = 'typescript'): SecurityScanResult {
    const startTime = Date.now();
    const vulnerabilities: SecurityVulnerability[] = [];

    for (const rule of this.rules) {
      if (!rule.enabled) continue;
      if (!this.config.categories.includes(rule.category)) continue;
      if (rule.languages && !rule.languages.includes(language)) continue;

      const matches = this.findMatches(code, rule, file);
      vulnerabilities.push(...matches);
    }

    // Filter by severity
    const filtered = this.filterBySeverity(vulnerabilities);

    const scanTime = Date.now() - startTime;
    const summary = this.createSummary(filtered);

    return {
      file,
      vulnerabilities: filtered,
      scanTime,
      summary,
    };
  }

  /**
   * Scan multiple files
   */
  scanFiles(
    files: Array<{ path: string; content: string; language?: string }>
  ): SecurityScanResult[] {
    return files.map((f) => this.scan(f.content, f.path, f.language));
  }

  /**
   * Find pattern matches in code
   */
  private findMatches(
    code: string,
    rule: SecurityRule,
    file: string
  ): SecurityVulnerability[] {
    const vulnerabilities: SecurityVulnerability[] = [];
    const lines = code.split('\n');
    let match;

    // Reset regex lastIndex
    rule.pattern.lastIndex = 0;

    while ((match = rule.pattern.exec(code)) !== null) {
      const line = code.substring(0, match.index).split('\n').length;
      const lineContent = lines[line - 1] || '';

      vulnerabilities.push({
        id: `${file}:${line}:${rule.id}`,
        ruleId: rule.id,
        severity: rule.severity,
        category: rule.category,
        title: rule.name,
        description: rule.description,
        file,
        line,
        snippet: lineContent.trim().substring(0, 100),
        cweId: rule.cweId,
        owasp: rule.owasp,
        remediation: rule.remediation,
      });
    }

    return vulnerabilities;
  }

  /**
   * Filter vulnerabilities by severity threshold
   */
  private filterBySeverity(
    vulnerabilities: SecurityVulnerability[]
  ): SecurityVulnerability[] {
    const severityOrder: VulnerabilitySeverity[] = [
      'critical',
      'high',
      'medium',
      'low',
      'info',
    ];
    const thresholdIndex = severityOrder.indexOf(this.config.severityThreshold);

    return vulnerabilities.filter((v) => {
      const vIndex = severityOrder.indexOf(v.severity);
      return vIndex <= thresholdIndex;
    });
  }

  /**
   * Create security summary
   */
  private createSummary(vulnerabilities: SecurityVulnerability[]): SecuritySummary {
    const bySeverity: Record<VulnerabilitySeverity, number> = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
      info: 0,
    };

    const byCategory: Record<VulnerabilityCategory, number> = {
      injection: 0,
      xss: 0,
      auth: 0,
      crypto: 0,
      'sensitive-data': 0,
      'access-control': 0,
      misconfiguration: 0,
      dependencies: 0,
      secrets: 0,
    };

    for (const v of vulnerabilities) {
      bySeverity[v.severity]++;
      byCategory[v.category]++;
    }

    const riskScore = this.calculateRiskScore(bySeverity);
    const passed = riskScore <= this.config.riskScoreThreshold &&
                   bySeverity.critical === 0;

    return {
      total: vulnerabilities.length,
      bySeverity,
      byCategory,
      riskScore,
      passed,
    };
  }

  /**
   * Calculate risk score
   */
  private calculateRiskScore(
    bySeverity: Record<VulnerabilitySeverity, number>
  ): number {
    const weights = {
      critical: 40,
      high: 20,
      medium: 10,
      low: 5,
      info: 1,
    };

    let score = 0;
    for (const [severity, count] of Object.entries(bySeverity)) {
      score += weights[severity as VulnerabilitySeverity] * count;
    }

    return Math.min(100, score);
  }

  /**
   * Get available rules
   */
  getRules(): SecurityRule[] {
    return [...this.rules];
  }

  /**
   * Enable/disable rule
   */
  setRuleEnabled(ruleId: string, enabled: boolean): void {
    const rule = this.rules.find((r) => r.id === ruleId);
    if (rule) {
      rule.enabled = enabled;
    }
  }

  /**
   * Add custom rule
   */
  addRule(rule: SecurityRule): void {
    this.rules.push(rule);
  }
}

/**
 * Create security scanner instance
 */
export function createSecurityScanner(
  config?: Partial<SecurityScannerConfig>
): SecurityScanner {
  return new SecurityScanner(config);
}
