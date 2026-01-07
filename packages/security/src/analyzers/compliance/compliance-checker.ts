/**
 * @fileoverview Compliance Checker - Security compliance verification
 * @module @nahisaho/musubix-security/analyzers/compliance/compliance-checker
 * @trace DES-SEC3-COMPLIANCE-001, REQ-SEC3-COMPLIANCE-001
 */

import type { Vulnerability, Severity, OWASPCategory } from '../../types/vulnerability.js';

/**
 * Compliance standard types
 */
export type ComplianceStandard = 
  | 'owasp-asvs-l1'
  | 'owasp-asvs-l2'
  | 'owasp-asvs-l3'
  | 'pci-dss'
  | 'soc2'
  | 'hipaa'
  | 'gdpr'
  | 'iso27001';

/**
 * Compliance requirement
 */
export interface ComplianceRequirement {
  id: string;
  standard: ComplianceStandard;
  category: string;
  title: string;
  description: string;
  level: 1 | 2 | 3;
  controls: string[];
}

/**
 * Compliance check result
 */
export interface ComplianceCheckResult {
  requirement: ComplianceRequirement;
  status: 'pass' | 'fail' | 'partial' | 'not-applicable';
  findings: ComplianceFinding[];
  evidence: string[];
  remediationSteps?: string[];
}

/**
 * Compliance finding
 */
export interface ComplianceFinding {
  id: string;
  requirementId: string;
  severity: Severity;
  location?: {
    file: string;
    line?: number;
  };
  description: string;
  evidence: string;
  recommendation: string;
}

/**
 * Compliance report
 */
export interface ComplianceReport {
  standard: ComplianceStandard;
  timestamp: Date;
  overallStatus: 'compliant' | 'non-compliant' | 'partial';
  score: number;
  totalRequirements: number;
  passedRequirements: number;
  failedRequirements: number;
  partialRequirements: number;
  notApplicable: number;
  results: ComplianceCheckResult[];
  summary: ComplianceSummary;
}

/**
 * Compliance summary by category
 */
export interface ComplianceSummary {
  byCategory: Record<string, CategorySummary>;
  criticalFindings: ComplianceFinding[];
  topRemediations: string[];
}

/**
 * Category summary
 */
export interface CategorySummary {
  total: number;
  passed: number;
  failed: number;
  partial: number;
  percentage: number;
}

/**
 * Compliance checker options
 */
export interface ComplianceCheckerOptions {
  standards?: ComplianceStandard[];
  level?: 1 | 2 | 3;
  includeEvidence?: boolean;
  skipCategories?: string[];
}

/**
 * OWASP ASVS Requirements Database
 */
const ASVS_REQUIREMENTS: ComplianceRequirement[] = [
  // V1: Architecture
  {
    id: 'V1.1.1',
    standard: 'owasp-asvs-l1',
    category: 'Architecture',
    title: 'Secure Development Lifecycle',
    description: 'Verify that a secure software development lifecycle is in use',
    level: 1,
    controls: ['SDLC', 'security-requirements'],
  },
  {
    id: 'V1.1.2',
    standard: 'owasp-asvs-l1',
    category: 'Architecture',
    title: 'Threat Modeling',
    description: 'Verify that threat modeling is performed for changes',
    level: 2,
    controls: ['threat-model', 'design-review'],
  },
  // V2: Authentication
  {
    id: 'V2.1.1',
    standard: 'owasp-asvs-l1',
    category: 'Authentication',
    title: 'Password Length',
    description: 'Verify that user passwords are at least 12 characters',
    level: 1,
    controls: ['password-policy', 'input-validation'],
  },
  {
    id: 'V2.1.2',
    standard: 'owasp-asvs-l1',
    category: 'Authentication',
    title: 'Password Complexity',
    description: 'Verify that passwords can contain spaces and all printable characters',
    level: 1,
    controls: ['password-policy'],
  },
  {
    id: 'V2.2.1',
    standard: 'owasp-asvs-l1',
    category: 'Authentication',
    title: 'Anti-Automation',
    description: 'Verify that anti-automation controls are in place',
    level: 1,
    controls: ['rate-limiting', 'captcha'],
  },
  {
    id: 'V2.5.1',
    standard: 'owasp-asvs-l1',
    category: 'Authentication',
    title: 'Credential Recovery',
    description: 'Verify that credential recovery does not reveal current password',
    level: 1,
    controls: ['password-reset', 'secure-recovery'],
  },
  // V3: Session Management
  {
    id: 'V3.1.1',
    standard: 'owasp-asvs-l1',
    category: 'Session Management',
    title: 'Secure Session Tokens',
    description: 'Verify that the app generates a new session token on authentication',
    level: 1,
    controls: ['session-management', 'token-generation'],
  },
  {
    id: 'V3.2.1',
    standard: 'owasp-asvs-l1',
    category: 'Session Management',
    title: 'Session Binding',
    description: 'Verify that session tokens are bound to the user',
    level: 1,
    controls: ['session-binding', 'cookie-security'],
  },
  {
    id: 'V3.3.1',
    standard: 'owasp-asvs-l1',
    category: 'Session Management',
    title: 'Session Timeout',
    description: 'Verify that session times out after inactivity',
    level: 1,
    controls: ['session-timeout', 'idle-timeout'],
  },
  // V4: Access Control
  {
    id: 'V4.1.1',
    standard: 'owasp-asvs-l1',
    category: 'Access Control',
    title: 'Access Control Policy',
    description: 'Verify that the app enforces access control rules on trusted service layer',
    level: 1,
    controls: ['access-control', 'authorization'],
  },
  {
    id: 'V4.1.2',
    standard: 'owasp-asvs-l1',
    category: 'Access Control',
    title: 'Sensitive Data Access',
    description: 'Verify that sensitive data and APIs are protected',
    level: 1,
    controls: ['data-protection', 'api-security'],
  },
  {
    id: 'V4.2.1',
    standard: 'owasp-asvs-l1',
    category: 'Access Control',
    title: 'Secure Direct Object References',
    description: 'Verify that users can only access authorized data',
    level: 1,
    controls: ['idor-prevention', 'authorization'],
  },
  // V5: Validation
  {
    id: 'V5.1.1',
    standard: 'owasp-asvs-l1',
    category: 'Input Validation',
    title: 'Input Validation',
    description: 'Verify that input validation is performed on all input',
    level: 1,
    controls: ['input-validation', 'sanitization'],
  },
  {
    id: 'V5.2.1',
    standard: 'owasp-asvs-l1',
    category: 'Input Validation',
    title: 'Sanitization',
    description: 'Verify that output encoding is applied to prevent XSS',
    level: 1,
    controls: ['output-encoding', 'xss-prevention'],
  },
  {
    id: 'V5.3.1',
    standard: 'owasp-asvs-l1',
    category: 'Input Validation',
    title: 'SQL Injection Prevention',
    description: 'Verify that parameterized queries are used',
    level: 1,
    controls: ['parameterized-queries', 'sql-injection'],
  },
  // V6: Cryptography
  {
    id: 'V6.1.1',
    standard: 'owasp-asvs-l1',
    category: 'Cryptography',
    title: 'Data Classification',
    description: 'Verify that regulated data is stored encrypted',
    level: 1,
    controls: ['encryption-at-rest', 'data-classification'],
  },
  {
    id: 'V6.2.1',
    standard: 'owasp-asvs-l1',
    category: 'Cryptography',
    title: 'Strong Algorithms',
    description: 'Verify that only approved cryptographic algorithms are used',
    level: 1,
    controls: ['crypto-algorithms', 'key-management'],
  },
  // V7: Error Handling
  {
    id: 'V7.1.1',
    standard: 'owasp-asvs-l1',
    category: 'Error Handling',
    title: 'Error Logging',
    description: 'Verify that the app logs security events',
    level: 1,
    controls: ['logging', 'audit-trail'],
  },
  {
    id: 'V7.2.1',
    standard: 'owasp-asvs-l1',
    category: 'Error Handling',
    title: 'Generic Error Messages',
    description: 'Verify that error messages do not leak sensitive information',
    level: 1,
    controls: ['error-handling', 'information-disclosure'],
  },
  // V8: Data Protection
  {
    id: 'V8.1.1',
    standard: 'owasp-asvs-l1',
    category: 'Data Protection',
    title: 'Sensitive Data Protection',
    description: 'Verify that sensitive data is protected in transit',
    level: 1,
    controls: ['tls', 'encryption-in-transit'],
  },
  {
    id: 'V8.2.1',
    standard: 'owasp-asvs-l1',
    category: 'Data Protection',
    title: 'Client-side Data Protection',
    description: 'Verify that sensitive data is not cached on client',
    level: 1,
    controls: ['cache-control', 'client-storage'],
  },
];

/**
 * PCI-DSS Requirements Database
 */
const PCI_DSS_REQUIREMENTS: ComplianceRequirement[] = [
  {
    id: 'PCI-1.1',
    standard: 'pci-dss',
    category: 'Network Security',
    title: 'Firewall Configuration',
    description: 'Install and maintain firewall configurations',
    level: 1,
    controls: ['firewall', 'network-segmentation'],
  },
  {
    id: 'PCI-2.1',
    standard: 'pci-dss',
    category: 'Secure Configuration',
    title: 'Default Credentials',
    description: 'Change vendor-supplied defaults',
    level: 1,
    controls: ['credential-management', 'configuration'],
  },
  {
    id: 'PCI-3.1',
    standard: 'pci-dss',
    category: 'Data Protection',
    title: 'Stored Data Protection',
    description: 'Protect stored cardholder data',
    level: 1,
    controls: ['encryption', 'data-masking'],
  },
  {
    id: 'PCI-4.1',
    standard: 'pci-dss',
    category: 'Encryption',
    title: 'Transmission Encryption',
    description: 'Encrypt transmission of cardholder data',
    level: 1,
    controls: ['tls', 'certificate-management'],
  },
  {
    id: 'PCI-6.1',
    standard: 'pci-dss',
    category: 'Vulnerability Management',
    title: 'Security Patching',
    description: 'Deploy critical security patches within one month',
    level: 1,
    controls: ['patch-management', 'vulnerability-scanning'],
  },
  {
    id: 'PCI-6.5',
    standard: 'pci-dss',
    category: 'Secure Development',
    title: 'Secure Coding',
    description: 'Develop applications based on secure coding guidelines',
    level: 1,
    controls: ['secure-sdlc', 'code-review'],
  },
  {
    id: 'PCI-8.1',
    standard: 'pci-dss',
    category: 'Access Control',
    title: 'User Identification',
    description: 'Assign unique IDs to each person with access',
    level: 1,
    controls: ['identity-management', 'user-provisioning'],
  },
  {
    id: 'PCI-10.1',
    standard: 'pci-dss',
    category: 'Logging',
    title: 'Audit Logging',
    description: 'Implement audit trails for system components',
    level: 1,
    controls: ['audit-logging', 'log-management'],
  },
];

/**
 * Code patterns to check for compliance
 */
interface CodePattern {
  id: string;
  name: string;
  pattern: RegExp;
  type: 'present' | 'absent';
  relatedControls: string[];
  severity: Severity;
}

const COMPLIANCE_PATTERNS: CodePattern[] = [
  // Password validation
  {
    id: 'CP-001',
    name: 'Weak Password Check',
    pattern: /password\.length\s*[<>=]+\s*[0-8]\b/gi,
    type: 'absent',
    relatedControls: ['password-policy'],
    severity: 'high',
  },
  // SQL Injection
  {
    id: 'CP-002',
    name: 'SQL String Concatenation',
    pattern: /(?:query|sql|execute)\s*\(\s*['"`].*\$\{|query\s*\+\s*(?:req|user|input)/gi,
    type: 'absent',
    relatedControls: ['parameterized-queries', 'sql-injection'],
    severity: 'critical',
  },
  // Rate Limiting
  {
    id: 'CP-003',
    name: 'Rate Limiting Present',
    pattern: /rateLimit|rateLimiter|throttle|express-rate-limit/gi,
    type: 'present',
    relatedControls: ['rate-limiting'],
    severity: 'medium',
  },
  // Session Management
  {
    id: 'CP-004',
    name: 'Session Configuration',
    pattern: /session\s*\(\s*\{[^}]*(?:secure|httpOnly|sameSite)/gi,
    type: 'present',
    relatedControls: ['session-management', 'cookie-security'],
    severity: 'high',
  },
  // TLS/HTTPS
  {
    id: 'CP-005',
    name: 'HTTP Redirect',
    pattern: /app\.use\([^)]*redirect[^)]*https|forceHTTPS|requireHTTPS/gi,
    type: 'present',
    relatedControls: ['tls', 'encryption-in-transit'],
    severity: 'high',
  },
  // Crypto
  {
    id: 'CP-006',
    name: 'Weak Crypto Algorithm',
    pattern: /createHash\s*\(\s*['"](?:md5|sha1)['"]\s*\)|DES|RC4|MD5/gi,
    type: 'absent',
    relatedControls: ['crypto-algorithms'],
    severity: 'high',
  },
  // Input Validation
  {
    id: 'CP-007',
    name: 'Input Validation',
    pattern: /(?:validator|joi|yup|zod)\.(?:string|number|object)|validate\s*\(/gi,
    type: 'present',
    relatedControls: ['input-validation'],
    severity: 'medium',
  },
  // Output Encoding
  {
    id: 'CP-008',
    name: 'XSS Prevention',
    pattern: /(?:escape|encode|sanitize)(?:Html|Xml|Url)|DOMPurify|xss/gi,
    type: 'present',
    relatedControls: ['output-encoding', 'xss-prevention'],
    severity: 'high',
  },
  // Logging
  {
    id: 'CP-009',
    name: 'Security Logging',
    pattern: /(?:logger|log)\.(?:security|audit|info)\s*\(|winston|pino|bunyan/gi,
    type: 'present',
    relatedControls: ['logging', 'audit-trail'],
    severity: 'medium',
  },
  // Error Handling
  {
    id: 'CP-010',
    name: 'Error Information Disclosure',
    pattern: /(?:res|response)\.(?:send|json)\s*\(\s*(?:err|error)(?:\.stack|\.message)?[^,)]*\)/gi,
    type: 'absent',
    relatedControls: ['error-handling', 'information-disclosure'],
    severity: 'medium',
  },
  // Access Control
  {
    id: 'CP-011',
    name: 'Authorization Check',
    pattern: /(?:isAuthorized|checkPermission|requireRole|hasAccess|authorize)\s*\(/gi,
    type: 'present',
    relatedControls: ['access-control', 'authorization'],
    severity: 'high',
  },
  // IDOR Prevention
  {
    id: 'CP-012',
    name: 'User ID Verification',
    pattern: /(?:user\.id|userId|currentUser)\s*===?\s*(?:req\.params|params|id)/gi,
    type: 'present',
    relatedControls: ['idor-prevention'],
    severity: 'high',
  },
];

/**
 * Compliance Checker
 * @trace DES-SEC3-COMPLIANCE-001
 */
export class ComplianceChecker {
  private options: Required<ComplianceCheckerOptions>;
  private requirements: Map<ComplianceStandard, ComplianceRequirement[]>;

  constructor(options: ComplianceCheckerOptions = {}) {
    this.options = {
      standards: options.standards ?? ['owasp-asvs-l1'],
      level: options.level ?? 1,
      includeEvidence: options.includeEvidence ?? true,
      skipCategories: options.skipCategories ?? [],
    };

    // Initialize requirements database
    this.requirements = new Map();
    this.requirements.set('owasp-asvs-l1', ASVS_REQUIREMENTS.filter(r => r.level <= 1));
    this.requirements.set('owasp-asvs-l2', ASVS_REQUIREMENTS.filter(r => r.level <= 2));
    this.requirements.set('owasp-asvs-l3', ASVS_REQUIREMENTS);
    this.requirements.set('pci-dss', PCI_DSS_REQUIREMENTS);
  }

  /**
   * Check compliance against a standard
   * @trace REQ-SEC3-COMPLIANCE-001
   */
  async check(
    code: string,
    filePath: string,
    standard?: ComplianceStandard
  ): Promise<ComplianceReport> {
    const targetStandard = standard ?? this.options.standards[0];
    const requirements = this.getRequirementsInternal(targetStandard);
    
    const results: ComplianceCheckResult[] = [];
    let passed = 0;
    let failed = 0;
    let partial = 0;
    let notApplicable = 0;

    for (const requirement of requirements) {
      // Skip excluded categories
      if (this.options.skipCategories.includes(requirement.category)) {
        notApplicable++;
        results.push({
          requirement,
          status: 'not-applicable',
          findings: [],
          evidence: ['Category excluded from scan'],
        });
        continue;
      }

      const result = this.checkRequirement(requirement, code, filePath);
      results.push(result);

      switch (result.status) {
        case 'pass':
          passed++;
          break;
        case 'fail':
          failed++;
          break;
        case 'partial':
          partial++;
          break;
        case 'not-applicable':
          notApplicable++;
          break;
      }
    }

    const total = requirements.length;
    const applicable = total - notApplicable;
    const score = applicable > 0 ? Math.round((passed / applicable) * 100) : 100;

    return {
      standard: targetStandard,
      timestamp: new Date(),
      overallStatus: this.determineOverallStatus(passed, failed, partial, applicable),
      score,
      totalRequirements: total,
      passedRequirements: passed,
      failedRequirements: failed,
      partialRequirements: partial,
      notApplicable,
      results,
      summary: this.generateSummary(results),
    };
  }

  /**
   * Check multiple files for compliance
   */
  async checkFiles(
    files: Array<{ path: string; content: string }>,
    standard?: ComplianceStandard
  ): Promise<ComplianceReport> {
    const combinedCode = files.map(f => `// FILE: ${f.path}\n${f.content}`).join('\n\n');
    return this.check(combinedCode, 'combined', standard);
  }

  /**
   * Alias for check() - Check compliance against a standard with empty code
   * Used for obtaining compliance reports without actual code analysis
   */
  async checkCompliance(standard: ComplianceStandard): Promise<{
    standard: ComplianceStandard;
    timestamp: Date;
    findings: Array<{
      requirement: ComplianceRequirement;
      status: 'pass' | 'fail' | 'partial' | 'not-applicable';
      evidence?: string;
    }>;
    summary: {
      totalRequirements: number;
      passed: number;
      failed: number;
      notApplicable: number;
      compliancePercentage: number;
      byCategory: Array<{ category: string; passed: number; failed: number }>;
    };
  }> {
    const report = await this.check('', 'compliance-check', standard);
    
    return {
      standard: report.standard,
      timestamp: report.timestamp,
      findings: report.results.map(r => ({
        requirement: r.requirement,
        status: r.status,
        evidence: r.evidence?.join('; '),
      })),
      summary: {
        totalRequirements: report.totalRequirements,
        passed: report.passedRequirements,
        failed: report.failedRequirements,
        notApplicable: report.notApplicable,
        compliancePercentage: report.score,
        byCategory: Object.entries(report.summary.byCategory).map(([category, data]) => ({
          category,
          passed: data.passed,
          failed: data.failed,
        })),
      },
    };
  }

  /**
   * Check all configured standards
   */
  async checkAllStandards(): Promise<Array<{
    standard: ComplianceStandard;
    timestamp: Date;
    findings: Array<{
      requirement: ComplianceRequirement;
      status: 'pass' | 'fail' | 'partial' | 'not-applicable';
      evidence?: string;
    }>;
    summary: {
      totalRequirements: number;
      passed: number;
      failed: number;
      notApplicable: number;
      compliancePercentage: number;
      byCategory: Array<{ category: string; passed: number; failed: number }>;
    };
  }>> {
    const results = [];
    for (const standard of this.options.standards) {
      results.push(await this.checkCompliance(standard));
    }
    return results;
  }

  /**
   * Get list of supported compliance standards
   */
  getSupportedStandards(): ComplianceStandard[] {
    return Array.from(this.requirements.keys());
  }

  /**
   * Get requirements for a specific standard (public accessor)
   */
  getRequirements(standard: ComplianceStandard): ComplianceRequirement[] {
    return this.getRequirementsInternal(standard);
  }

  /**
   * Check a specific requirement
   */
  private checkRequirement(
    requirement: ComplianceRequirement,
    code: string,
    filePath: string
  ): ComplianceCheckResult {
    const findings: ComplianceFinding[] = [];
    const evidence: string[] = [];
    let passCount = 0;
    let failCount = 0;

    // Check code patterns related to this requirement
    for (const pattern of COMPLIANCE_PATTERNS) {
      const hasOverlap = pattern.relatedControls.some(c => 
        requirement.controls.includes(c)
      );

      if (!hasOverlap) continue;

      const matches = code.match(pattern.pattern);
      
      if (pattern.type === 'present') {
        if (matches && matches.length > 0) {
          passCount++;
          if (this.options.includeEvidence) {
            evidence.push(`Found ${pattern.name}: ${matches.slice(0, 3).join(', ')}`);
          }
        } else {
          failCount++;
          findings.push({
            id: `${requirement.id}-${pattern.id}`,
            requirementId: requirement.id,
            severity: pattern.severity,
            location: { file: filePath },
            description: `Missing ${pattern.name}`,
            evidence: 'Pattern not found in code',
            recommendation: `Implement ${pattern.name} to meet ${requirement.title}`,
          });
        }
      } else {
        // type === 'absent'
        if (matches && matches.length > 0) {
          failCount++;
          // Find line numbers
          const lines = code.split('\n');
          for (let i = 0; i < lines.length; i++) {
            if (pattern.pattern.test(lines[i])) {
              findings.push({
                id: `${requirement.id}-${pattern.id}-L${i + 1}`,
                requirementId: requirement.id,
                severity: pattern.severity,
                location: { file: filePath, line: i + 1 },
                description: `Found problematic pattern: ${pattern.name}`,
                evidence: lines[i].trim().substring(0, 100),
                recommendation: `Remove or fix ${pattern.name} to meet ${requirement.title}`,
              });
            }
            // Reset regex lastIndex
            pattern.pattern.lastIndex = 0;
          }
        } else {
          passCount++;
          if (this.options.includeEvidence) {
            evidence.push(`No ${pattern.name} found (good)`);
          }
        }
      }
      // Reset regex lastIndex
      pattern.pattern.lastIndex = 0;
    }

    // Determine status
    let status: ComplianceCheckResult['status'];
    if (failCount === 0 && passCount > 0) {
      status = 'pass';
    } else if (passCount === 0 && failCount > 0) {
      status = 'fail';
    } else if (passCount > 0 && failCount > 0) {
      status = 'partial';
    } else {
      status = 'not-applicable';
    }

    return {
      requirement,
      status,
      findings,
      evidence,
      remediationSteps: findings.length > 0 
        ? findings.map(f => f.recommendation)
        : undefined,
    };
  }

  /**
   * Get requirements for a standard (internal)
   */
  private getRequirementsInternal(standard: ComplianceStandard): ComplianceRequirement[] {
    const reqs = this.requirements.get(standard);
    if (!reqs) {
      // Return ASVS L1 as default
      return this.requirements.get('owasp-asvs-l1') ?? [];
    }
    return reqs.filter(r => r.level <= this.options.level);
  }

  /**
   * Determine overall compliance status
   */
  private determineOverallStatus(
    passed: number,
    failed: number,
    partial: number,
    applicable: number
  ): ComplianceReport['overallStatus'] {
    if (applicable === 0) return 'compliant';
    if (failed === 0 && partial === 0) return 'compliant';
    if (passed === 0) return 'non-compliant';
    return 'partial';
  }

  /**
   * Generate compliance summary
   */
  private generateSummary(results: ComplianceCheckResult[]): ComplianceSummary {
    const byCategory: Record<string, CategorySummary> = {};
    const criticalFindings: ComplianceFinding[] = [];
    const remediations = new Set<string>();

    for (const result of results) {
      const category = result.requirement.category;
      
      if (!byCategory[category]) {
        byCategory[category] = {
          total: 0,
          passed: 0,
          failed: 0,
          partial: 0,
          percentage: 0,
        };
      }

      byCategory[category].total++;
      
      switch (result.status) {
        case 'pass':
          byCategory[category].passed++;
          break;
        case 'fail':
          byCategory[category].failed++;
          break;
        case 'partial':
          byCategory[category].partial++;
          break;
      }

      // Collect critical findings
      for (const finding of result.findings) {
        if (finding.severity === 'critical' || finding.severity === 'high') {
          criticalFindings.push(finding);
        }
        remediations.add(finding.recommendation);
      }
    }

    // Calculate percentages
    for (const category of Object.keys(byCategory)) {
      const cat = byCategory[category];
      const applicable = cat.total - (results.filter(r => 
        r.requirement.category === category && r.status === 'not-applicable'
      ).length);
      cat.percentage = applicable > 0 
        ? Math.round((cat.passed / applicable) * 100) 
        : 100;
    }

    return {
      byCategory,
      criticalFindings: criticalFindings.slice(0, 10),
      topRemediations: Array.from(remediations).slice(0, 5),
    };
  }

  /**
   * Convert compliance findings to vulnerabilities
   */
  toVulnerabilities(report: ComplianceReport): Vulnerability[] {
    const vulnerabilities: Vulnerability[] = [];

    for (const result of report.results) {
      for (const finding of result.findings) {
        vulnerabilities.push({
          id: finding.id,
          type: 'configuration',
          severity: finding.severity,
          cwes: this.mapRequirementToCWE(result.requirement),
          owasp: this.mapRequirementToOWASP(result.requirement),
          location: {
            file: finding.location?.file ?? 'unknown',
            startLine: finding.location?.line ?? 1,
            endLine: finding.location?.line ?? 1,
            startColumn: 0,
            endColumn: 0,
          },
          description: finding.description,
          recommendation: finding.recommendation,
          confidence: 0.85,
          ruleId: result.requirement.id,
          codeSnippet: finding.evidence,
          detectedAt: new Date(),
        });
      }
    }

    return vulnerabilities;
  }

  /**
   * Map requirement to CWE IDs
   */
  private mapRequirementToCWE(requirement: ComplianceRequirement): string[] {
    const cweMappings: Record<string, string[]> = {
      'password-policy': ['CWE-521'],
      'sql-injection': ['CWE-89'],
      'xss-prevention': ['CWE-79'],
      'session-management': ['CWE-384'],
      'access-control': ['CWE-284'],
      'crypto-algorithms': ['CWE-327'],
      'logging': ['CWE-778'],
      'error-handling': ['CWE-209'],
      'tls': ['CWE-319'],
    };

    const cwes: string[] = [];
    for (const control of requirement.controls) {
      if (cweMappings[control]) {
        cwes.push(...cweMappings[control]);
      }
    }
    return [...new Set(cwes)];
  }

  /**
   * Map requirement to OWASP categories
   */
  private mapRequirementToOWASP(requirement: ComplianceRequirement): OWASPCategory[] {
    const owaspMappings: Record<string, OWASPCategory[]> = {
      'Authentication': ['A07:2021'],
      'Session Management': ['A07:2021'],
      'Access Control': ['A01:2021'],
      'Input Validation': ['A03:2021'],
      'Cryptography': ['A02:2021'],
      'Error Handling': ['A09:2021'],
      'Data Protection': ['A02:2021'],
    };

    return owaspMappings[requirement.category] ?? ['A00:Unknown'];
  }
}

/**
 * Create compliance checker instance
 */
export function createComplianceChecker(options?: ComplianceCheckerOptions): ComplianceChecker {
  return new ComplianceChecker(options);
}
