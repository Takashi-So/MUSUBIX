/**
 * @fileoverview Security service - facade for all security scanning operations
 * @module @nahisaho/musubix-security/services/security-service
 * @trace REQ-SEC-SCAN-001
 */

import * as path from 'node:path';

import type {
  SecurityConfig,
  ScanResult,
  TaintResult,
  SecretScanResult,
  AuditResult,
  Fix,
  VerificationResult,
} from '../types/index.js';
import { DEFAULT_CONFIG } from '../types/index.js';
import { VulnerabilityScanner } from '../analysis/index.js';
import { TaintAnalyzer } from '../analysis/index.js';
import { SecretDetector } from '../analysis/index.js';
import { DependencyAuditor } from '../analysis/index.js';
import { FileScanner } from '../infrastructure/index.js';
import { loadConfig } from '../infrastructure/index.js';
import { FixGenerator } from './fix-generator.js';
import { FixVerifier } from './fix-verifier.js';
import {
  ReportGenerator,
  type CombinedResults,
  type ReportMetadata,
  type ReportFormat,
} from './report-generator.js';

/**
 * Scan options
 */
export interface ScanOptions {
  /** Target path (file or directory) */
  target: string;
  /** Enable vulnerability scanning */
  vulnerabilities?: boolean;
  /** Enable taint analysis */
  taint?: boolean;
  /** Enable secret detection */
  secrets?: boolean;
  /** Enable dependency audit */
  dependencies?: boolean;
  /** Generate fixes */
  generateFixes?: boolean;
  /** Verify fixes */
  verifyFixes?: boolean;
  /** Use cache */
  useCache?: boolean;
  /** Configuration overrides */
  config?: Partial<SecurityConfig>;
}

/**
 * Complete scan result
 */
export interface CompleteScanResult {
  /** Scan metadata */
  metadata: {
    target: string;
    scanTime: Date;
    duration: number;
    filesScanned: number;
    rulesApplied: number;
  };
  /** Vulnerability scan results */
  vulnerabilities?: ScanResult;
  /** Taint analysis results */
  taint?: TaintResult;
  /** Secret scan results */
  secrets?: SecretScanResult;
  /** Dependency audit results */
  dependencies?: AuditResult;
  /** Generated fixes */
  fixes?: Fix[];
  /** Fix verification results */
  verifications?: VerificationResult[];
  /** Summary statistics */
  summary: {
    totalVulnerabilities: number;
    bySeverity: {
      critical: number;
      high: number;
      medium: number;
      low: number;
      info: number;
    };
    taintedPaths: number;
    secretsFound: number;
    vulnerableDependencies: number;
    fixesGenerated: number;
    fixesVerified: number;
  };
}

/**
 * Security service - main facade for security operations
 */
export class SecurityService {
  private config: SecurityConfig;
  private vulnerabilityScanner: VulnerabilityScanner;
  private taintAnalyzer: TaintAnalyzer;
  private secretDetector: SecretDetector;
  private dependencyAuditor: DependencyAuditor;
  private fixGenerator: FixGenerator;
  private fixVerifier: FixVerifier;
  private reportGenerator: ReportGenerator;
  private fileScanner: FileScanner;

  constructor(config: Partial<SecurityConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
    
    // Initialize components
    this.vulnerabilityScanner = new VulnerabilityScanner();
    this.taintAnalyzer = new TaintAnalyzer();
    this.secretDetector = new SecretDetector();
    this.dependencyAuditor = new DependencyAuditor();
    this.fixGenerator = new FixGenerator();
    this.fixVerifier = new FixVerifier();
    this.reportGenerator = new ReportGenerator(this.config.report);
    this.fileScanner = new FileScanner({
      extensions: this.config.scan?.severityFilter as unknown as string[] | undefined,
      excludePatterns: this.config.excludePatterns,
      maxFileSize: this.config.scan?.maxFileSize,
    });
  }

  /**
   * Run a complete security scan
   */
  async scan(options: ScanOptions): Promise<CompleteScanResult> {
    const startTime = Date.now();
    const scanConfig = { ...this.config, ...options.config };

    // Determine what to scan
    const runVulns = options.vulnerabilities ?? true;
    const runTaint = options.taint ?? (scanConfig.taint !== undefined);
    const runSecrets = options.secrets ?? (scanConfig.secret !== undefined);
    const runDeps = options.dependencies ?? (scanConfig.audit !== undefined);
    const genFixes = options.generateFixes ?? true;
    const verFixes = options.verifyFixes ?? false;

    // Collect files to scan
    const files = await this.fileScanner.scan(options.target);

    // Run scans in parallel where possible
    const results: {
      vulnerabilities?: ScanResult;
      taint?: TaintResult;
      secrets?: SecretScanResult;
      dependencies?: AuditResult;
    } = {};

    // Run parallel scans
    const promises: Promise<void>[] = [];

    if (runVulns) {
      promises.push(
        this.vulnerabilityScanner.scanDirectory(options.target).then((r) => {
          results.vulnerabilities = r;
        })
      );
    }

    if (runTaint) {
      promises.push(
        this.taintAnalyzer.analyze(options.target).then((r) => {
          results.taint = r;
        })
      );
    }

    if (runSecrets) {
      promises.push(
        this.secretDetector.scan(options.target).then((r) => {
          results.secrets = r;
        })
      );
    }

    if (runDeps) {
      promises.push(
        this.dependencyAuditor.audit(options.target).then((r) => {
          results.dependencies = r;
        })
      );
    }

    await Promise.all(promises);

    // Generate fixes if requested
    let fixes: Fix[] = [];
    if (genFixes && results.vulnerabilities) {
      fixes = await this.fixGenerator.generateFixes(
        results.vulnerabilities.vulnerabilities
      );

      // Add taint-based fixes
      if (results.taint) {
        for (const taintPath of results.taint.unsafePaths) {
          const taintFix = await this.fixGenerator.generateTaintFix(taintPath);
          if (taintFix) {
            fixes.push(taintFix);
          }
        }
      }
    }

    // Verify fixes if requested
    let verifications: VerificationResult[] = [];
    if (verFixes && fixes.length > 0) {
      verifications = await this.fixVerifier.verifyBatch(fixes);
    }

    // Calculate duration
    const duration = Date.now() - startTime;

    // Generate summary
    const summary = this.generateSummary(results, fixes, verifications);

    return {
      metadata: {
        target: options.target,
        scanTime: new Date(),
        duration,
        filesScanned: files.length,
        rulesApplied: this.vulnerabilityScanner.getRuleCount(),
      },
      vulnerabilities: results.vulnerabilities,
      taint: results.taint,
      secrets: results.secrets,
      dependencies: results.dependencies,
      fixes: genFixes ? fixes : undefined,
      verifications: verFixes ? verifications : undefined,
      summary,
    };
  }

  /**
   * Quick scan - vulnerabilities only
   */
  async quickScan(target: string): Promise<ScanResult> {
    return this.vulnerabilityScanner.scanDirectory(target);
  }

  /**
   * Scan a single file
   */
  async scanFile(filePath: string): Promise<ScanResult> {
    const vulnerabilities = this.vulnerabilityScanner.scanFile(filePath);
    return {
      vulnerabilities,
      scannedFiles: 1,
      skippedFiles: 0,
      duration: 0,
      timestamp: new Date(),
      options: {},
      summary: {
        critical: vulnerabilities.filter((v) => v.severity === 'critical').length,
        high: vulnerabilities.filter((v) => v.severity === 'high').length,
        medium: vulnerabilities.filter((v) => v.severity === 'medium').length,
        low: vulnerabilities.filter((v) => v.severity === 'low').length,
        info: vulnerabilities.filter((v) => v.severity === 'info').length,
        total: vulnerabilities.length,
      },
    };
  }

  /**
   * Run taint analysis only
   */
  async analyzeTaint(target: string): Promise<TaintResult> {
    return this.taintAnalyzer.analyze(target);
  }

  /**
   * Detect secrets only
   */
  async detectSecrets(target: string): Promise<SecretScanResult> {
    return this.secretDetector.scan(target);
  }

  /**
   * Audit dependencies only
   */
  async auditDependencies(target: string): Promise<AuditResult> {
    return this.dependencyAuditor.audit(target);
  }

  /**
   * Generate a fix for a vulnerability
   */
  async generateFix(vulnerabilityId: string, scanResult: ScanResult): Promise<Fix | null> {
    const vulnerability = scanResult.vulnerabilities.find(
      (v) => v.id === vulnerabilityId
    );
    if (!vulnerability) {
      return null;
    }
    return this.fixGenerator.generateFix(vulnerability);
  }

  /**
   * Verify a fix
   */
  async verifyFix(fix: Fix): Promise<VerificationResult> {
    return this.fixVerifier.verify(fix);
  }

  /**
   * Generate a report from scan results
   */
  async generateReport(
    scanResult: CompleteScanResult,
    format: ReportFormat = 'json'
  ): Promise<string> {
    const combined: CombinedResults = {
      vulnerabilities: scanResult.vulnerabilities ?? {
        vulnerabilities: [],
        scannedFiles: 0,
        skippedFiles: 0,
        duration: 0,
        timestamp: new Date(),
        options: {},
        summary: { critical: 0, high: 0, medium: 0, low: 0, info: 0, total: 0 },
      },
      dependencies: scanResult.dependencies,
      taint: scanResult.taint,
      secrets: scanResult.secrets,
      fixes: scanResult.fixes,
    };

    const metadata: ReportMetadata = {
      title: 'Security Scan Report',
      project: path.basename(scanResult.metadata.target),
      scanTime: scanResult.metadata.scanTime,
      duration: scanResult.metadata.duration,
      targetPath: scanResult.metadata.target,
    };

    return this.reportGenerator.generate(combined, metadata, format);
  }

  /**
   * Generate summary statistics
   */
  private generateSummary(
    results: {
      vulnerabilities?: ScanResult;
      taint?: TaintResult;
      secrets?: SecretScanResult;
      dependencies?: AuditResult;
    },
    fixes: Fix[],
    verifications: VerificationResult[]
  ): CompleteScanResult['summary'] {
    const vulns = results.vulnerabilities?.vulnerabilities ?? [];
    
    return {
      totalVulnerabilities: vulns.length,
      bySeverity: {
        critical: vulns.filter((v) => v.severity === 'critical').length,
        high: vulns.filter((v) => v.severity === 'high').length,
        medium: vulns.filter((v) => v.severity === 'medium').length,
        low: vulns.filter((v) => v.severity === 'low').length,
        info: vulns.filter((v) => v.severity === 'info').length,
      },
      taintedPaths: results.taint?.unsafePaths.length ?? 0,
      secretsFound: results.secrets?.summary.total ?? 0,
      vulnerableDependencies: results.dependencies?.vulnerableDependencies.length ?? 0,
      fixesGenerated: fixes.length,
      fixesVerified: verifications.filter((v) => v.status === 'verified').length,
    };
  }

  /**
   * Get current configuration
   */
  getConfig(): SecurityConfig {
    return { ...this.config };
  }

  /**
   * Update configuration
   */
  setConfig(config: Partial<SecurityConfig>): void {
    this.config = { ...this.config, ...config };
  }

  /**
   * Load configuration from file
   */
  async loadConfigFile(searchFrom?: string): Promise<void> {
    const loaded = await loadConfig(searchFrom);
    if (loaded) {
      this.config = { ...this.config, ...loaded };
    }
  }
}

/**
 * Create a security service
 */
export function createSecurityService(config?: Partial<SecurityConfig>): SecurityService {
  return new SecurityService(config);
}

/**
 * Quick scan helper function
 */
export async function scanForVulnerabilities(target: string): Promise<ScanResult> {
  const service = createSecurityService();
  return service.quickScan(target);
}

/**
 * Full scan helper function
 */
export async function runSecurityScan(
  target: string,
  options?: Partial<ScanOptions>
): Promise<CompleteScanResult> {
  const service = createSecurityService();
  return service.scan({ target, ...options });
}
