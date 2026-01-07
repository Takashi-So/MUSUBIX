/**
 * @fileoverview Container Image Scanner - scans container images for vulnerabilities
 * @module @nahisaho/musubix-security/analyzers/container/image-scanner
 * @trace DES-SEC2-CONTAINER-001, REQ-SEC2-CONTAINER-001
 */

import { spawn } from 'node:child_process';
import { existsSync, readFileSync } from 'node:fs';
import type { Vulnerability, Severity } from '../../types/vulnerability.js';

/**
 * Container image vulnerability
 */
export interface ContainerVulnerability {
  id: string;
  packageName: string;
  installedVersion: string;
  fixedVersion?: string;
  severity: Severity;
  cve?: string;
  description: string;
  layer?: string;
}

/**
 * Image scan result
 */
export interface ImageScanResult {
  image: string;
  tag: string;
  digest?: string;
  vulnerabilities: ContainerVulnerability[];
  metadata: ImageMetadata;
  scanTime: Date;
  scanner: 'trivy' | 'grype' | 'internal';
}

/**
 * Image metadata
 */
export interface ImageMetadata {
  os?: string;
  osVersion?: string;
  architecture?: string;
  size?: number;
  layers?: number;
  created?: Date;
}

/**
 * Image scan options
 */
export interface ImageScanOptions {
  /** Scanner to use (default: trivy) */
  scanner?: 'trivy' | 'grype';
  /** Minimum severity to report */
  minSeverity?: Severity;
  /** Skip update of vulnerability database */
  skipDbUpdate?: boolean;
  /** Scan timeout in milliseconds */
  timeout?: number;
  /** Include unfixed vulnerabilities */
  includeUnfixed?: boolean;
  /** Rule IDs to skip (e.g., ['DKR-001', 'DKR-002']) */
  skipRules?: string[];
}

/**
 * Dockerfile analysis result
 */
export interface DockerfileAnalysis {
  filePath: string;
  baseImage: string;
  issues: DockerfileIssue[];
  bestPractices: BestPracticeViolation[];
}

/**
 * Dockerfile issue
 */
export interface DockerfileIssue {
  id: string;
  severity: Severity;
  line: number;
  instruction: string;
  message: string;
  recommendation: string;
}

/**
 * Best practice violation
 */
export interface BestPracticeViolation {
  rule: string;
  description: string;
  line?: number;
  recommendation: string;
}

/**
 * Severity mapping from external scanners
 */
const SEVERITY_MAP: Record<string, Severity> = {
  'CRITICAL': 'critical',
  'HIGH': 'high',
  'MEDIUM': 'medium',
  'LOW': 'low',
  'UNKNOWN': 'info',
  'NEGLIGIBLE': 'info',
};

/**
 * Dockerfile best practice rules
 */
const DOCKERFILE_RULES: Array<{
  id: string;
  pattern: RegExp;
  severity: Severity;
  message: string;
  recommendation: string;
}> = [
  {
    id: 'DKR-001',
    pattern: /^FROM\s+\S+:latest\s*$/im,
    severity: 'medium',
    message: 'Using `:latest` tag is not recommended',
    recommendation: 'Use a specific version tag for reproducible builds',
  },
  {
    id: 'DKR-002',
    pattern: /^USER\s+root\s*$/im,
    severity: 'high',
    message: 'Running as root user',
    recommendation: 'Create and use a non-root user',
  },
  {
    id: 'DKR-003',
    pattern: /^RUN\s+.*apt-get\s+install.*-y(?!.*--no-install-recommends)/im,
    severity: 'low',
    message: 'Installing packages without --no-install-recommends',
    recommendation: 'Add --no-install-recommends to reduce image size',
  },
  {
    id: 'DKR-004',
    pattern: /^RUN\s+.*curl.*\|\s*(bash|sh)/im,
    severity: 'critical',
    message: 'Piping curl to shell is dangerous',
    recommendation: 'Download and verify script before execution',
  },
  {
    id: 'DKR-005',
    pattern: /^ADD\s+https?:\/\//im,
    severity: 'medium',
    message: 'Using ADD with URL is discouraged',
    recommendation: 'Use RUN with curl/wget for better caching',
  },
  {
    id: 'DKR-006',
    pattern: /^EXPOSE\s+22\s*$/im,
    severity: 'high',
    message: 'Exposing SSH port',
    recommendation: 'Avoid SSH in containers; use kubectl exec or docker exec',
  },
  {
    id: 'DKR-007',
    pattern: /ENV\s+.*PASSWORD|SECRET|KEY|TOKEN.*=/i,
    severity: 'critical',
    message: 'Hardcoded secrets in ENV',
    recommendation: 'Use Docker secrets or environment variables at runtime',
  },
  {
    id: 'DKR-008',
    pattern: /^COPY\s+\.\s+/im,
    severity: 'medium',
    message: 'Copying entire context',
    recommendation: 'Use specific paths or .dockerignore',
  },
];

/**
 * Container Image Scanner
 * @trace DES-SEC2-CONTAINER-001
 */
export class ImageScanner {
  private options: ImageScanOptions;

  constructor(options: ImageScanOptions = {}) {
    this.options = {
      scanner: options.scanner ?? 'trivy',
      minSeverity: options.minSeverity ?? 'low',
      skipDbUpdate: options.skipDbUpdate ?? false,
      timeout: options.timeout ?? 300000, // 5 minutes
      includeUnfixed: options.includeUnfixed ?? true,
      skipRules: options.skipRules ?? [],
    };
  }

  /**
   * Scan a container image
   * @trace REQ-SEC2-CONTAINER-001
   */
  async scan(imageRef: string, options?: ImageScanOptions): Promise<ImageScanResult> {
    const mergedOptions = { ...this.options, ...options };
    
    // Parse image reference
    const { image, tag } = this.parseImageRef(imageRef);
    
    try {
      // Try external scanner first
      const externalResult = await this.runExternalScanner(imageRef, mergedOptions);
      if (externalResult) {
        return {
          ...externalResult,
          image,
          tag,
          scanTime: new Date(),
        };
      }
    } catch {
      // Fall back to internal scanning
    }
    
    // Internal scanning (Dockerfile analysis only without external scanner)
    return {
      image,
      tag,
      vulnerabilities: [],
      metadata: {},
      scanTime: new Date(),
      scanner: 'internal',
    };
  }

  /**
   * Analyze a Dockerfile for security issues
   * @trace REQ-SEC2-CONTAINER-002
   */
  async analyzeDockerfile(dockerfilePath: string): Promise<DockerfileAnalysis> {
    if (!existsSync(dockerfilePath)) {
      throw new Error(`Dockerfile not found: ${dockerfilePath}`);
    }
    
    const content = readFileSync(dockerfilePath, 'utf-8');
    const lines = content.split('\n');
    
    // Extract base image
    const baseImage = this.extractBaseImage(content);
    
    // Check for issues and filter by skipRules
    const allIssues = this.checkDockerfileIssues(content, lines);
    const skipRules = this.options.skipRules ?? [];
    const issues = allIssues.filter(issue => !skipRules.includes(issue.id));
    
    // Check best practices
    const bestPractices = this.checkBestPractices(content, lines);
    
    return {
      filePath: dockerfilePath,
      baseImage,
      issues,
      bestPractices,
    };
  }

  /**
   * Convert container vulnerabilities to standard vulnerability format
   */
  toVulnerabilities(result: ImageScanResult): Vulnerability[] {
    return result.vulnerabilities.map((cv, index) => ({
      id: `CONTAINER-${result.image.replace(/[^a-zA-Z0-9]/g, '-')}-${index}`,
      type: 'dependency' as const,
      severity: cv.severity,
      cwes: this.mapCVEToCWE(cv.cve),
      owasp: ['A06:2021'], // Vulnerable and Outdated Components
      location: {
        file: result.image,
        startLine: 1,
        endLine: 1,
        startColumn: 0,
        endColumn: 0,
      },
      description: `${cv.packageName}@${cv.installedVersion}: ${cv.description}`,
      recommendation: cv.fixedVersion 
        ? `Upgrade to ${cv.packageName}@${cv.fixedVersion}`
        : 'No fix available; consider using an alternative package',
      confidence: 0.95,
      ruleId: cv.cve ?? cv.id,
      codeSnippet: `Package: ${cv.packageName}\nVersion: ${cv.installedVersion}${cv.layer ? `\nLayer: ${cv.layer}` : ''}`,
      detectedAt: new Date(),
    }));
  }

  /**
   * Parse image reference into image name and tag
   */
  private parseImageRef(imageRef: string): { image: string; tag: string; digest?: string } {
    // Handle digest format
    if (imageRef.includes('@sha256:')) {
      const [image, digest] = imageRef.split('@');
      return { image, tag: 'latest', digest };
    }
    
    // Handle tag format
    const lastColon = imageRef.lastIndexOf(':');
    if (lastColon > 0 && !imageRef.substring(lastColon).includes('/')) {
      return {
        image: imageRef.substring(0, lastColon),
        tag: imageRef.substring(lastColon + 1),
      };
    }
    
    return { image: imageRef, tag: 'latest' };
  }

  /**
   * Run external scanner (Trivy or Grype)
   */
  private async runExternalScanner(
    imageRef: string,
    options: ImageScanOptions
  ): Promise<Omit<ImageScanResult, 'image' | 'tag' | 'scanTime'> | null> {
    const scanner = options.scanner ?? 'trivy';
    
    // Check if scanner is available
    const isAvailable = await this.isScannerAvailable(scanner);
    if (!isAvailable) {
      return null;
    }
    
    if (scanner === 'trivy') {
      return this.runTrivy(imageRef, options);
    } else if (scanner === 'grype') {
      return this.runGrype(imageRef, options);
    }
    
    return null;
  }

  /**
   * Check if a scanner is available
   */
  private async isScannerAvailable(scanner: string): Promise<boolean> {
    return new Promise((resolve) => {
      const proc = spawn(scanner, ['--version'], { stdio: 'ignore' });
      proc.on('close', (code) => resolve(code === 0));
      proc.on('error', () => resolve(false));
    });
  }

  /**
   * Run Trivy scanner
   */
  private async runTrivy(
    imageRef: string,
    options: ImageScanOptions
  ): Promise<Omit<ImageScanResult, 'image' | 'tag' | 'scanTime'> | null> {
    const args = ['image', '--format', 'json'];
    
    if (options.skipDbUpdate) {
      args.push('--skip-db-update');
    }
    
    if (!options.includeUnfixed) {
      args.push('--ignore-unfixed');
    }
    
    args.push(imageRef);
    
    return new Promise((resolve, reject) => {
      let stdout = '';
      let stderr = '';
      
      const proc = spawn('trivy', args, {
        timeout: options.timeout,
      });
      
      proc.stdout.on('data', (data) => { stdout += data; });
      proc.stderr.on('data', (data) => { stderr += data; });
      
      proc.on('close', (code) => {
        if (code !== 0) {
          reject(new Error(`Trivy failed: ${stderr}`));
          return;
        }
        
        try {
          const result = JSON.parse(stdout);
          resolve(this.parseTrivyOutput(result, options));
        } catch (e) {
          reject(new Error(`Failed to parse Trivy output: ${e}`));
        }
      });
      
      proc.on('error', (err) => reject(err));
    });
  }

  /**
   * Run Grype scanner
   */
  private async runGrype(
    imageRef: string,
    options: ImageScanOptions
  ): Promise<Omit<ImageScanResult, 'image' | 'tag' | 'scanTime'> | null> {
    const args = ['-o', 'json', imageRef];
    
    return new Promise((resolve, reject) => {
      let stdout = '';
      let stderr = '';
      
      const proc = spawn('grype', args, {
        timeout: options.timeout,
      });
      
      proc.stdout.on('data', (data) => { stdout += data; });
      proc.stderr.on('data', (data) => { stderr += data; });
      
      proc.on('close', (code) => {
        if (code !== 0) {
          reject(new Error(`Grype failed: ${stderr}`));
          return;
        }
        
        try {
          const result = JSON.parse(stdout);
          resolve(this.parseGrypeOutput(result, options));
        } catch (e) {
          reject(new Error(`Failed to parse Grype output: ${e}`));
        }
      });
      
      proc.on('error', (err) => reject(err));
    });
  }

  /**
   * Parse Trivy JSON output
   */
  private parseTrivyOutput(
    output: any,
    options: ImageScanOptions
  ): Omit<ImageScanResult, 'image' | 'tag' | 'scanTime'> {
    const vulnerabilities: ContainerVulnerability[] = [];
    const minSeverityLevel = this.getSeverityLevel(options.minSeverity ?? 'low');
    
    // Handle Results array
    const results = output.Results ?? [];
    for (const result of results) {
      const vulns = result.Vulnerabilities ?? [];
      for (const vuln of vulns) {
        const severity = SEVERITY_MAP[vuln.Severity?.toUpperCase()] ?? 'info';
        
        if (this.getSeverityLevel(severity) < minSeverityLevel) {
          continue;
        }
        
        vulnerabilities.push({
          id: vuln.VulnerabilityID,
          packageName: vuln.PkgName,
          installedVersion: vuln.InstalledVersion,
          fixedVersion: vuln.FixedVersion,
          severity,
          cve: vuln.VulnerabilityID?.startsWith('CVE-') ? vuln.VulnerabilityID : undefined,
          description: vuln.Description ?? vuln.Title ?? 'No description',
          layer: result.Target,
        });
      }
    }
    
    // Extract metadata
    const metadata: ImageMetadata = {};
    if (output.Metadata) {
      metadata.os = output.Metadata.OS?.Family;
      metadata.osVersion = output.Metadata.OS?.Name;
      metadata.architecture = output.Metadata.ImageConfig?.architecture;
    }
    
    return {
      vulnerabilities,
      metadata,
      scanner: 'trivy',
    };
  }

  /**
   * Parse Grype JSON output
   */
  private parseGrypeOutput(
    output: any,
    options: ImageScanOptions
  ): Omit<ImageScanResult, 'image' | 'tag' | 'scanTime'> {
    const vulnerabilities: ContainerVulnerability[] = [];
    const minSeverityLevel = this.getSeverityLevel(options.minSeverity ?? 'low');
    
    const matches = output.matches ?? [];
    for (const match of matches) {
      const vuln = match.vulnerability;
      const artifact = match.artifact;
      
      const severity = SEVERITY_MAP[vuln?.severity?.toUpperCase()] ?? 'info';
      
      if (this.getSeverityLevel(severity) < minSeverityLevel) {
        continue;
      }
      
      vulnerabilities.push({
        id: vuln?.id ?? 'UNKNOWN',
        packageName: artifact?.name ?? 'unknown',
        installedVersion: artifact?.version ?? 'unknown',
        fixedVersion: match.vulnerability?.fix?.versions?.[0],
        severity,
        cve: vuln?.id?.startsWith('CVE-') ? vuln.id : undefined,
        description: vuln?.description ?? 'No description',
      });
    }
    
    // Extract metadata
    const metadata: ImageMetadata = {};
    if (output.source?.target?.imageID) {
      metadata.os = output.distro?.name;
      metadata.osVersion = output.distro?.version;
    }
    
    return {
      vulnerabilities,
      metadata,
      scanner: 'grype',
    };
  }

  /**
   * Get numeric severity level for comparison
   */
  private getSeverityLevel(severity: Severity): number {
    const levels: Record<Severity, number> = {
      critical: 4,
      high: 3,
      medium: 2,
      low: 1,
      info: 0,
    };
    return levels[severity] ?? 0;
  }

  /**
   * Extract base image from Dockerfile
   */
  private extractBaseImage(content: string): string {
    const match = content.match(/^FROM\s+(\S+)/im);
    return match?.[1] ?? 'unknown';
  }

  /**
   * Check Dockerfile for security issues
   */
  private checkDockerfileIssues(content: string, lines: string[]): DockerfileIssue[] {
    const issues: DockerfileIssue[] = [];
    
    for (const rule of DOCKERFILE_RULES) {
      const match = content.match(rule.pattern);
      if (match) {
        // Find line number
        let lineNumber = 1;
        for (let i = 0; i < lines.length; i++) {
          if (lines[i].match(rule.pattern)) {
            lineNumber = i + 1;
            break;
          }
        }
        
        issues.push({
          id: rule.id,
          severity: rule.severity,
          line: lineNumber,
          instruction: match[0].trim(),
          message: rule.message,
          recommendation: rule.recommendation,
        });
      }
    }
    
    return issues;
  }

  /**
   * Check best practices
   */
  private checkBestPractices(content: string, _lines: string[]): BestPracticeViolation[] {
    const violations: BestPracticeViolation[] = [];
    
    // Check for HEALTHCHECK
    if (!content.includes('HEALTHCHECK')) {
      violations.push({
        rule: 'HEALTHCHECK',
        description: 'No HEALTHCHECK instruction found',
        recommendation: 'Add HEALTHCHECK to enable container health monitoring',
      });
    }
    
    // Check for multi-stage builds when large packages are installed
    const hasInstallCommands = /apt-get install|npm install|pip install|yarn add/i.test(content);
    const isMultiStage = (content.match(/^FROM\s+/gim) ?? []).length > 1;
    if (hasInstallCommands && !isMultiStage) {
      violations.push({
        rule: 'MULTI_STAGE_BUILD',
        description: 'Consider using multi-stage builds',
        recommendation: 'Use multi-stage builds to reduce final image size',
      });
    }
    
    // Check for .dockerignore mention
    // This is a reminder, not detectable from Dockerfile alone
    
    return violations;
  }

  /**
   * Map CVE to CWE
   */
  private mapCVEToCWE(cve?: string): string[] {
    // In a real implementation, this would query a CVE database
    // For now, return a generic CWE for supply chain vulnerability
    return cve ? ['CWE-1035'] : ['CWE-1035']; // Using Components from Untrusted Source
  }
}

/**
 * Create image scanner instance
 */
export function createImageScanner(options?: ImageScanOptions): ImageScanner {
  return new ImageScanner(options);
}
