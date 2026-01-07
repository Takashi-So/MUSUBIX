/**
 * @fileoverview CI/CD Integration for Security Scanning
 * @module @nahisaho/musubix-security/integrations/ci-integration
 * 
 * Provides integration with GitHub Actions, GitLab CI, and other CI/CD platforms
 * for automated security scanning in pipelines.
 */

import type { ScanResult, Severity } from '../types/index.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Supported CI/CD platforms
 */
export type CIPlatform = 'github-actions' | 'gitlab-ci' | 'azure-pipelines' | 'jenkins' | 'circleci' | 'generic';

/**
 * CI environment detection result
 */
export interface CIEnvironment {
  /** Detected CI platform */
  platform: CIPlatform;
  /** Whether running in CI environment */
  isCI: boolean;
  /** CI-specific metadata */
  metadata: CIMetadata;
}

/**
 * CI-specific metadata
 */
export interface CIMetadata {
  /** Repository name */
  repository?: string;
  /** Branch name */
  branch?: string;
  /** Commit SHA */
  commitSha?: string;
  /** Pull request number */
  pullRequest?: string;
  /** Build number/ID */
  buildId?: string;
  /** Actor/user who triggered the build */
  actor?: string;
  /** Event type that triggered the build */
  event?: string;
  /** Workflow/job name */
  workflow?: string;
  /** Runner OS */
  runnerOS?: string;
}

/**
 * CI integration options
 */
export interface CIIntegrationOptions {
  /** Fail on specific severity levels */
  failOn?: Severity[];
  /** Output format for CI */
  outputFormat?: 'json' | 'sarif' | 'checkrun' | 'annotations';
  /** Enable GitHub annotations */
  annotations?: boolean;
  /** Create/update PR comment */
  prComment?: boolean;
  /** Upload to code scanning */
  uploadToCodeScanning?: boolean;
  /** Custom threshold for failure */
  thresholds?: CIThresholds;
  /** Enable caching */
  enableCache?: boolean;
  /** Cache key prefix */
  cacheKeyPrefix?: string;
}

/**
 * CI failure thresholds
 */
export interface CIThresholds {
  /** Maximum critical vulnerabilities */
  maxCritical?: number;
  /** Maximum high vulnerabilities */
  maxHigh?: number;
  /** Maximum medium vulnerabilities */
  maxMedium?: number;
  /** Maximum total vulnerabilities */
  maxTotal?: number;
  /** Minimum security score (0-100) */
  minSecurityScore?: number;
}

/**
 * GitHub annotation for PR checks
 */
export interface GitHubAnnotation {
  /** Annotation level */
  level: 'notice' | 'warning' | 'error';
  /** File path */
  file: string;
  /** Start line */
  startLine: number;
  /** End line */
  endLine: number;
  /** Annotation title */
  title: string;
  /** Annotation message */
  message: string;
}

/**
 * CI scan result with platform-specific formatting
 */
export interface CIScanResult {
  /** Original scan result */
  scanResult: ScanResult;
  /** CI environment */
  environment: CIEnvironment;
  /** Whether to fail the build */
  shouldFail: boolean;
  /** Failure reasons */
  failureReasons: string[];
  /** GitHub annotations */
  annotations: GitHubAnnotation[];
  /** Formatted output for CI logs */
  formattedOutput: string;
  /** Exit code for CI */
  exitCode: number;
  /** Summary for PR comment */
  summary: CISummary;
}

/**
 * Summary for CI/PR display
 */
export interface CISummary {
  /** Total vulnerabilities */
  total: number;
  /** Breakdown by severity */
  bySeverity: Record<Severity, number>;
  /** Security score */
  securityScore: number;
  /** Pass/fail status */
  passed: boolean;
  /** Human-readable status */
  statusEmoji: string;
  /** Short description */
  shortDescription: string;
}

// ============================================================================
// CI Integration Class
// ============================================================================

/**
 * CI/CD Integration for automated security scanning
 * 
 * @example
 * ```typescript
 * const ci = createCIIntegration({
 *   failOn: ['critical', 'high'],
 *   annotations: true,
 *   prComment: true,
 * });
 * 
 * const env = ci.detectEnvironment();
 * const result = ci.processScanResult(scanResult);
 * 
 * if (result.shouldFail) {
 *   process.exit(result.exitCode);
 * }
 * ```
 */
export class CIIntegration {
  private options: Required<CIIntegrationOptions>;

  constructor(options: CIIntegrationOptions = {}) {
    this.options = {
      failOn: options.failOn ?? ['critical', 'high'],
      outputFormat: options.outputFormat ?? 'annotations',
      annotations: options.annotations ?? true,
      prComment: options.prComment ?? false,
      uploadToCodeScanning: options.uploadToCodeScanning ?? false,
      thresholds: options.thresholds ?? {},
      enableCache: options.enableCache ?? true,
      cacheKeyPrefix: options.cacheKeyPrefix ?? 'musubix-security',
    };
  }

  /**
   * Detect CI environment
   */
  detectEnvironment(): CIEnvironment {
    const env = process.env;

    // GitHub Actions
    if (env.GITHUB_ACTIONS === 'true') {
      return {
        platform: 'github-actions',
        isCI: true,
        metadata: {
          repository: env.GITHUB_REPOSITORY,
          branch: env.GITHUB_REF_NAME ?? env.GITHUB_HEAD_REF,
          commitSha: env.GITHUB_SHA,
          pullRequest: env.GITHUB_EVENT_NAME === 'pull_request' 
            ? env.GITHUB_REF?.split('/')[2] 
            : undefined,
          buildId: env.GITHUB_RUN_ID,
          actor: env.GITHUB_ACTOR,
          event: env.GITHUB_EVENT_NAME,
          workflow: env.GITHUB_WORKFLOW,
          runnerOS: env.RUNNER_OS,
        },
      };
    }

    // GitLab CI
    if (env.GITLAB_CI === 'true') {
      return {
        platform: 'gitlab-ci',
        isCI: true,
        metadata: {
          repository: env.CI_PROJECT_PATH,
          branch: env.CI_COMMIT_REF_NAME,
          commitSha: env.CI_COMMIT_SHA,
          pullRequest: env.CI_MERGE_REQUEST_IID,
          buildId: env.CI_PIPELINE_ID,
          actor: env.GITLAB_USER_LOGIN,
          event: env.CI_PIPELINE_SOURCE,
          workflow: env.CI_JOB_NAME,
        },
      };
    }

    // Azure Pipelines
    if (env.TF_BUILD === 'True') {
      return {
        platform: 'azure-pipelines',
        isCI: true,
        metadata: {
          repository: env.BUILD_REPOSITORY_NAME,
          branch: env.BUILD_SOURCEBRANCHNAME,
          commitSha: env.BUILD_SOURCEVERSION,
          pullRequest: env.SYSTEM_PULLREQUEST_PULLREQUESTID,
          buildId: env.BUILD_BUILDID,
          actor: env.BUILD_REQUESTEDFOR,
          workflow: env.BUILD_DEFINITIONNAME,
        },
      };
    }

    // Jenkins
    if (env.JENKINS_URL) {
      return {
        platform: 'jenkins',
        isCI: true,
        metadata: {
          branch: env.GIT_BRANCH ?? env.BRANCH_NAME,
          commitSha: env.GIT_COMMIT,
          buildId: env.BUILD_NUMBER,
          workflow: env.JOB_NAME,
        },
      };
    }

    // CircleCI
    if (env.CIRCLECI === 'true') {
      return {
        platform: 'circleci',
        isCI: true,
        metadata: {
          repository: env.CIRCLE_PROJECT_REPONAME,
          branch: env.CIRCLE_BRANCH,
          commitSha: env.CIRCLE_SHA1,
          pullRequest: env.CIRCLE_PULL_REQUEST?.split('/').pop(),
          buildId: env.CIRCLE_BUILD_NUM,
          actor: env.CIRCLE_USERNAME,
          workflow: env.CIRCLE_WORKFLOW_ID,
        },
      };
    }

    // Generic CI detection
    const isCI = env.CI === 'true' || env.CONTINUOUS_INTEGRATION === 'true';
    
    return {
      platform: 'generic',
      isCI,
      metadata: {},
    };
  }

  /**
   * Process scan result for CI output
   */
  processScanResult(scanResult: ScanResult): CIScanResult {
    const environment = this.detectEnvironment();
    const annotations = this.generateAnnotations(scanResult);
    const summary = this.generateSummary(scanResult);
    const { shouldFail, failureReasons } = this.checkThresholds(scanResult, summary);
    const formattedOutput = this.formatOutput(scanResult, environment, summary);
    const exitCode = shouldFail ? 1 : 0;

    return {
      scanResult,
      environment,
      shouldFail,
      failureReasons,
      annotations,
      formattedOutput,
      exitCode,
      summary,
    };
  }

  /**
   * Generate GitHub-style annotations
   */
  generateAnnotations(scanResult: ScanResult): GitHubAnnotation[] {
    if (!this.options.annotations) {
      return [];
    }

    return scanResult.vulnerabilities.map((vuln) => ({
      level: this.severityToAnnotationLevel(vuln.severity),
      file: vuln.location.file,
      startLine: vuln.location.startLine,
      endLine: vuln.location.endLine ?? vuln.location.startLine,
      title: `${vuln.severity.toUpperCase()}: ${vuln.ruleId}`,
      message: `${vuln.description}\n\nRule: ${vuln.ruleId}\nOWASP: ${vuln.owasp?.join(', ') ?? 'N/A'}\nCWE: ${vuln.cwes?.join(', ') ?? 'N/A'}`,
    }));
  }

  /**
   * Generate summary for display
   */
  generateSummary(scanResult: ScanResult): CISummary {
    const bySeverity = scanResult.summary;
    const total = bySeverity.critical + bySeverity.high + bySeverity.medium + bySeverity.low + bySeverity.info;
    
    // Calculate security score (100 - weighted penalty)
    const penalty = 
      bySeverity.critical * 25 +
      bySeverity.high * 10 +
      bySeverity.medium * 5 +
      bySeverity.low * 2 +
      bySeverity.info * 0.5;
    const securityScore = Math.max(0, Math.min(100, 100 - penalty));

    const passed = !this.shouldFailOnSeverity(scanResult) && !this.shouldFailOnThresholds(scanResult, { securityScore });
    const statusEmoji = passed ? '✅' : '❌';
    const shortDescription = passed 
      ? `${total} issues found (acceptable)`
      : `${total} issues found (policy violation)`;

    return {
      total,
      bySeverity: {
        critical: bySeverity.critical,
        high: bySeverity.high,
        medium: bySeverity.medium,
        low: bySeverity.low,
        info: bySeverity.info,
      },
      securityScore: Math.round(securityScore),
      passed,
      statusEmoji,
      shortDescription,
    };
  }

  /**
   * Check if build should fail based on thresholds
   */
  checkThresholds(scanResult: ScanResult, summary: CISummary): { shouldFail: boolean; failureReasons: string[] } {
    const failureReasons: string[] = [];

    // Check severity-based failure
    if (this.shouldFailOnSeverity(scanResult)) {
      const violations = this.options.failOn
        .filter(severity => scanResult.summary[severity] > 0)
        .map(severity => `${scanResult.summary[severity]} ${severity} vulnerability(s)`);
      failureReasons.push(...violations);
    }

    // Check threshold-based failure
    const thresholds = this.options.thresholds;
    if (thresholds.maxCritical !== undefined && summary.bySeverity.critical > thresholds.maxCritical) {
      failureReasons.push(`Critical vulnerabilities (${summary.bySeverity.critical}) exceed threshold (${thresholds.maxCritical})`);
    }
    if (thresholds.maxHigh !== undefined && summary.bySeverity.high > thresholds.maxHigh) {
      failureReasons.push(`High vulnerabilities (${summary.bySeverity.high}) exceed threshold (${thresholds.maxHigh})`);
    }
    if (thresholds.maxMedium !== undefined && summary.bySeverity.medium > thresholds.maxMedium) {
      failureReasons.push(`Medium vulnerabilities (${summary.bySeverity.medium}) exceed threshold (${thresholds.maxMedium})`);
    }
    if (thresholds.maxTotal !== undefined && summary.total > thresholds.maxTotal) {
      failureReasons.push(`Total vulnerabilities (${summary.total}) exceed threshold (${thresholds.maxTotal})`);
    }
    if (thresholds.minSecurityScore !== undefined && summary.securityScore < thresholds.minSecurityScore) {
      failureReasons.push(`Security score (${summary.securityScore}) below threshold (${thresholds.minSecurityScore})`);
    }

    return {
      shouldFail: failureReasons.length > 0,
      failureReasons,
    };
  }

  /**
   * Format output for CI logs
   */
  formatOutput(scanResult: ScanResult, environment: CIEnvironment, summary: CISummary): string {
    const lines: string[] = [];
    
    // Header
    lines.push('');
    lines.push('═══════════════════════════════════════════════════════════════');
    lines.push('  MUSUBIX Security Scan Results');
    lines.push('═══════════════════════════════════════════════════════════════');
    lines.push('');

    // Environment info
    if (environment.isCI) {
      lines.push(`Platform: ${environment.platform}`);
      if (environment.metadata.repository) lines.push(`Repository: ${environment.metadata.repository}`);
      if (environment.metadata.branch) lines.push(`Branch: ${environment.metadata.branch}`);
      if (environment.metadata.commitSha) lines.push(`Commit: ${environment.metadata.commitSha.substring(0, 7)}`);
      lines.push('');
    }

    // Summary
    lines.push(`${summary.statusEmoji} Status: ${summary.passed ? 'PASSED' : 'FAILED'}`);
    lines.push(`📊 Security Score: ${summary.securityScore}/100`);
    lines.push('');
    lines.push('Vulnerability Summary:');
    lines.push(`  🔴 Critical: ${summary.bySeverity.critical}`);
    lines.push(`  🟠 High:     ${summary.bySeverity.high}`);
    lines.push(`  🟡 Medium:   ${summary.bySeverity.medium}`);
    lines.push(`  🔵 Low:      ${summary.bySeverity.low}`);
    lines.push(`  ⚪ Info:     ${summary.bySeverity.info}`);
    lines.push(`  ─────────────`);
    lines.push(`  Total:      ${summary.total}`);
    lines.push('');

    // GitHub Actions specific: output annotations
    if (environment.platform === 'github-actions' && this.options.annotations) {
      for (const vuln of scanResult.vulnerabilities) {
        const level = this.severityToAnnotationLevel(vuln.severity);
        lines.push(`::${level} file=${vuln.location.file},line=${vuln.location.startLine},title=${vuln.ruleId}::${vuln.description}`);
      }
    }

    lines.push('═══════════════════════════════════════════════════════════════');
    lines.push('');

    return lines.join('\n');
  }

  /**
   * Generate workflow file content
   */
  generateWorkflowFile(platform: CIPlatform): string {
    switch (platform) {
      case 'github-actions':
        return this.generateGitHubActionsWorkflow();
      case 'gitlab-ci':
        return this.generateGitLabCIConfig();
      case 'azure-pipelines':
        return this.generateAzurePipelinesConfig();
      default:
        return this.generateGenericScript();
    }
  }

  /**
   * Generate GitHub Actions workflow
   */
  private generateGitHubActionsWorkflow(): string {
    return `name: Security Scan

on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main]

jobs:
  security-scan:
    runs-on: ubuntu-latest
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup Node.js
        uses: actions/setup-node@v4
        with:
          node-version: '20'
          cache: 'npm'
      
      - name: Install dependencies
        run: npm ci
      
      - name: Run MUSUBIX Security Scan
        run: npx @nahisaho/musubix-security scan ./src --ci --format sarif --output results.sarif
        continue-on-error: true
      
      - name: Upload SARIF to GitHub
        uses: github/codeql-action/upload-sarif@v3
        with:
          sarif_file: results.sarif
      
      - name: Check scan results
        run: npx @nahisaho/musubix-security check --fail-on critical,high
`;
  }

  /**
   * Generate GitLab CI config
   */
  private generateGitLabCIConfig(): string {
    return `security-scan:
  stage: test
  image: node:20
  script:
    - npm ci
    - npx @nahisaho/musubix-security scan ./src --ci --format json --output gl-sast-report.json
  artifacts:
    reports:
      sast: gl-sast-report.json
    paths:
      - gl-sast-report.json
  rules:
    - if: $CI_MERGE_REQUEST_IID
    - if: $CI_COMMIT_BRANCH == $CI_DEFAULT_BRANCH
`;
  }

  /**
   * Generate Azure Pipelines config
   */
  private generateAzurePipelinesConfig(): string {
    return `trigger:
  - main
  - develop

pool:
  vmImage: 'ubuntu-latest'

steps:
  - task: NodeTool@0
    inputs:
      versionSpec: '20.x'
    displayName: 'Install Node.js'

  - script: npm ci
    displayName: 'Install dependencies'

  - script: npx @nahisaho/musubix-security scan ./src --ci --format sarif --output $(Build.ArtifactStagingDirectory)/results.sarif
    displayName: 'Run Security Scan'
    continueOnError: true

  - task: PublishBuildArtifacts@1
    inputs:
      pathToPublish: '$(Build.ArtifactStagingDirectory)/results.sarif'
      artifactName: 'SecurityScanResults'
`;
  }

  /**
   * Generate generic shell script
   */
  private generateGenericScript(): string {
    return `#!/bin/bash
set -e

# Install dependencies
npm ci

# Run security scan
npx @nahisaho/musubix-security scan ./src --ci --format json --output security-report.json

# Check results and fail if critical/high vulnerabilities found
npx @nahisaho/musubix-security check --fail-on critical,high

echo "Security scan completed successfully"
`;
  }

  /**
   * Generate cache key for CI
   */
  generateCacheKey(files: string[]): string {
    const hash = files.sort().join('|');
    return `${this.options.cacheKeyPrefix}-${Buffer.from(hash).toString('base64').substring(0, 16)}`;
  }

  // ============================================================================
  // Private helpers
  // ============================================================================

  private severityToAnnotationLevel(severity: Severity): 'notice' | 'warning' | 'error' {
    switch (severity) {
      case 'critical':
      case 'high':
        return 'error';
      case 'medium':
        return 'warning';
      default:
        return 'notice';
    }
  }

  private shouldFailOnSeverity(scanResult: ScanResult): boolean {
    return this.options.failOn.some(severity => scanResult.summary[severity] > 0);
  }

  private shouldFailOnThresholds(scanResult: ScanResult, extra: { securityScore: number }): boolean {
    const t = this.options.thresholds;
    const s = scanResult.summary;
    const total = s.critical + s.high + s.medium + s.low + s.info;

    return (
      (t.maxCritical !== undefined && s.critical > t.maxCritical) ||
      (t.maxHigh !== undefined && s.high > t.maxHigh) ||
      (t.maxMedium !== undefined && s.medium > t.maxMedium) ||
      (t.maxTotal !== undefined && total > t.maxTotal) ||
      (t.minSecurityScore !== undefined && extra.securityScore < t.minSecurityScore)
    );
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create a CI integration instance
 */
export function createCIIntegration(options?: CIIntegrationOptions): CIIntegration {
  return new CIIntegration(options);
}

/**
 * Quick check if running in CI environment
 */
export function isCI(): boolean {
  const ci = createCIIntegration();
  return ci.detectEnvironment().isCI;
}

/**
 * Detect CI platform
 */
export function detectCIPlatform(): CIPlatform {
  const ci = createCIIntegration();
  return ci.detectEnvironment().platform;
}
