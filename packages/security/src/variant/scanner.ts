/**
 * @fileoverview Security Scanner - High-level scan API
 * @module @nahisaho/musubix-security/variant/scanner
 * @trace TSK-025, REQ-SEC-VARIANT-003
 * 
 * NOTE: v3.0.11 - Simplified implementation without CodeDB dependency
 */

import { TaintDetector, createDetector, type DetectorOptions } from './detector.js';
import { VulnerabilityModelManager, defaultModelManager } from './model.js';
import type {
  VulnerabilityFinding,
  VulnerabilitySeverity,
  ScanConfig,
  ScanResult,
  ScanSummary,
  ScanError,
} from '../types/variant.js';
import * as fs from 'node:fs';
import * as path from 'node:path';

// ============================================================================
// Types
// ============================================================================

/**
 * Scanner options
 */
export interface ScannerOptions {
  /** Scan configuration */
  config?: Partial<ScanConfig>;
  /** Detector options */
  detectorOptions?: DetectorOptions;
  /** Progress callback */
  onProgress?: (progress: ScanProgress) => void;
}

/**
 * Scan progress
 */
export interface ScanProgress {
  /** Current phase */
  phase: 'init' | 'scan' | 'analyze' | 'report';
  /** Progress percentage (0-100) */
  progress: number;
  /** Current file */
  currentFile?: string;
  /** Message */
  message: string;
}

// ============================================================================
// Scanner
// ============================================================================

/**
 * Security Scanner (v3.0.11 - File-based implementation)
 */
export class SecurityScanner {
  private config: ScanConfig;
  private detector: TaintDetector;
  private onProgress?: (progress: ScanProgress) => void;
  
  /** Model manager for vulnerability models (reserved for future use) */
  readonly modelManager: VulnerabilityModelManager;

  constructor(options: ScannerOptions = {}) {
    this.config = {
      targets: options.config?.targets ?? ['.'],
      include: options.config?.include ?? ['**/*.ts', '**/*.js', '**/*.java', '**/*.go', '**/*.py', '**/*.php'],
      exclude: options.config?.exclude ?? ['**/node_modules/**', '**/dist/**', '**/build/**', '**/.git/**'],
      enabledModels: options.config?.enabledModels,
      disabledModels: options.config?.disabledModels,
      minSeverity: options.config?.minSeverity ?? 'low',
      incremental: options.config?.incremental ?? false,
      maxFindingsPerRule: options.config?.maxFindingsPerRule ?? 100,
      fileTimeout: options.config?.fileTimeout ?? 30000,
    };
    this.detector = createDetector(options.detectorOptions);
    this.modelManager = options.detectorOptions?.modelManager ?? defaultModelManager;
    this.onProgress = options.onProgress;
  }

  /**
   * Run full scan
   */
  async scan(targetPath: string): Promise<ScanResult> {
    const startTime = Date.now();
    const errors: ScanError[] = [];
    let findings: VulnerabilityFinding[] = [];
    let filesScanned = 0;
    let linesScanned = 0;

    try {
      // Phase 1: Initialize
      this.reportProgress({
        phase: 'init',
        progress: 0,
        message: 'Initializing scan...',
      });

      // Phase 2: Collect files
      this.reportProgress({
        phase: 'scan',
        progress: 10,
        message: 'Collecting files...',
      });

      const files = await this.collectFiles(targetPath);
      const totalFiles = files.length;

      // Phase 3: Analyze files
      this.reportProgress({
        phase: 'analyze',
        progress: 20,
        message: `Analyzing ${totalFiles} files...`,
      });

      const fileContents: Array<{ path: string; content: string; lines: string[] }> = [];

      for (let i = 0; i < files.length; i++) {
        const filePath = files[i];
        const progress = 20 + (i / totalFiles) * 60;
        
        this.reportProgress({
          phase: 'analyze',
          progress,
          currentFile: filePath,
          message: `Analyzing ${path.basename(filePath)}...`,
        });

        try {
          const content = fs.readFileSync(filePath, 'utf-8');
          const lines = content.split('\n');
          fileContents.push({ path: filePath, content, lines });
          filesScanned++;
          linesScanned += lines.length;
        } catch (error) {
          errors.push({
            file: filePath,
            type: 'parse',
            message: `Failed to read file: ${error}`,
          });
        }
      }

      // Run detection
      const language = this.detectPrimaryLanguage(files);
      const result = await this.detector.detectInFiles(fileContents, language);
      findings = result.findings;
      
      if (result.errors.length > 0) {
        for (const err of result.errors) {
          errors.push({
            file: '',
            type: 'unknown',
            message: err,
          });
        }
      }

      // Filter by severity
      findings = this.filterBySeverity(findings, this.config.minSeverity ?? 'low');

      // Limit findings per rule
      if (this.config.maxFindingsPerRule) {
        findings = this.limitFindingsPerRule(findings, this.config.maxFindingsPerRule);
      }

      // Phase 4: Report
      this.reportProgress({
        phase: 'report',
        progress: 90,
        message: 'Generating report...',
      });

    } catch (error) {
      errors.push({
        file: targetPath,
        type: 'unknown',
        message: `Scan failed: ${error}`,
      });
    }

    const duration = Date.now() - startTime;

    this.reportProgress({
      phase: 'report',
      progress: 100,
      message: 'Scan complete.',
    });

    return {
      id: `scan-${Date.now()}`,
      timestamp: new Date(),
      duration,
      filesScanned,
      linesScanned,
      findings,
      summary: this.createSummary(findings),
      errors: errors.length > 0 ? errors : undefined,
      config: this.config,
    };
  }

  /**
   * Scan a single file
   */
  async scanFile(filePath: string): Promise<ScanResult> {
    const startTime = Date.now();
    const errors: ScanError[] = [];
    let findings: VulnerabilityFinding[] = [];
    let linesScanned = 0;

    try {
      const content = fs.readFileSync(filePath, 'utf-8');
      const lines = content.split('\n');
      linesScanned = lines.length;

      const language = this.detectLanguage(filePath);
      const result = await this.detector.detectInFiles(
        [{ path: filePath, content, lines }],
        language
      );
      findings = result.findings;
    } catch (error) {
      errors.push({
        file: filePath,
        type: 'parse',
        message: `Failed to scan file: ${error}`,
      });
    }

    return {
      id: `scan-${Date.now()}`,
      timestamp: new Date(),
      duration: Date.now() - startTime,
      filesScanned: 1,
      linesScanned,
      findings,
      summary: this.createSummary(findings),
      errors: errors.length > 0 ? errors : undefined,
      config: this.config,
    };
  }

  /**
   * Collect files to scan
   */
  private async collectFiles(targetPath: string): Promise<string[]> {
    const files: string[] = [];
    const stats = fs.statSync(targetPath);

    if (stats.isFile()) {
      if (this.shouldIncludeFile(targetPath)) {
        files.push(targetPath);
      }
      return files;
    }

    const walk = (dir: string): void => {
      const entries = fs.readdirSync(dir, { withFileTypes: true });
      
      for (const entry of entries) {
        const fullPath = path.join(dir, entry.name);
        const relativePath = path.relative(targetPath, fullPath);

        if (this.shouldExclude(relativePath)) {
          continue;
        }

        if (entry.isDirectory()) {
          walk(fullPath);
        } else if (entry.isFile() && this.shouldIncludeFile(fullPath)) {
          files.push(fullPath);
        }
      }
    };

    walk(targetPath);
    return files;
  }

  /**
   * Check if file should be included
   */
  private shouldIncludeFile(filePath: string): boolean {
    const ext = path.extname(filePath).toLowerCase();
    const supportedExtensions = ['.ts', '.js', '.tsx', '.jsx', '.java', '.go', '.py', '.php'];
    return supportedExtensions.includes(ext);
  }

  /**
   * Check if path should be excluded
   */
  private shouldExclude(relativePath: string): boolean {
    const excludePatterns = this.config.exclude ?? [];
    const normalizedPath = relativePath.replace(/\\/g, '/');

    for (const pattern of excludePatterns) {
      const regexPattern = pattern
        .replace(/\*\*/g, '.*')
        .replace(/\*/g, '[^/]*')
        .replace(/\//g, '\\/');
      
      if (new RegExp(regexPattern).test(normalizedPath)) {
        return true;
      }
    }

    return false;
  }

  /**
   * Detect primary language from files
   */
  private detectPrimaryLanguage(files: string[]): string | undefined {
    const counts: Record<string, number> = {};

    for (const file of files) {
      const ext = path.extname(file).toLowerCase();
      const lang = this.extToLanguage(ext);
      if (lang) {
        counts[lang] = (counts[lang] ?? 0) + 1;
      }
    }

    let maxCount = 0;
    let primaryLang: string | undefined;

    for (const [lang, count] of Object.entries(counts)) {
      if (count > maxCount) {
        maxCount = count;
        primaryLang = lang;
      }
    }

    return primaryLang;
  }

  /**
   * Detect language from file path
   */
  private detectLanguage(filePath: string): string | undefined {
    const ext = path.extname(filePath).toLowerCase();
    return this.extToLanguage(ext);
  }

  /**
   * Map extension to language
   */
  private extToLanguage(ext: string): string | undefined {
    const mapping: Record<string, string> = {
      '.ts': 'typescript',
      '.tsx': 'typescript',
      '.js': 'javascript',
      '.jsx': 'javascript',
      '.java': 'java',
      '.go': 'go',
      '.py': 'python',
      '.php': 'php',
    };
    return mapping[ext];
  }

  /**
   * Filter findings by minimum severity
   */
  private filterBySeverity(findings: VulnerabilityFinding[], minSeverity: VulnerabilitySeverity): VulnerabilityFinding[] {
    const severityOrder: VulnerabilitySeverity[] = ['critical', 'high', 'medium', 'low', 'info'];
    const minIndex = severityOrder.indexOf(minSeverity);

    return findings.filter((f) => {
      const index = severityOrder.indexOf(f.severity);
      return index <= minIndex;
    });
  }

  /**
   * Limit findings per rule
   */
  private limitFindingsPerRule(findings: VulnerabilityFinding[], limit: number): VulnerabilityFinding[] {
    const byRule: Record<string, VulnerabilityFinding[]> = {};

    for (const finding of findings) {
      if (!byRule[finding.ruleId]) {
        byRule[finding.ruleId] = [];
      }
      if (byRule[finding.ruleId].length < limit) {
        byRule[finding.ruleId].push(finding);
      }
    }

    return Object.values(byRule).flat();
  }

  /**
   * Create scan summary
   */
  private createSummary(findings: VulnerabilityFinding[]): ScanSummary {
    const bySeverity: Record<VulnerabilitySeverity, number> = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
      info: 0,
    };

    const byCWE: Record<number, number> = {};
    const byFile: Record<string, number> = {};

    for (const finding of findings) {
      bySeverity[finding.severity]++;

      for (const cwe of finding.cwe) {
        byCWE[cwe] = (byCWE[cwe] ?? 0) + 1;
      }

      byFile[finding.location.file] = (byFile[finding.location.file] ?? 0) + 1;
    }

    return {
      total: findings.length,
      bySeverity,
      byCWE,
      byFile,
    };
  }

  /**
   * Report progress
   */
  private reportProgress(progress: ScanProgress): void {
    this.onProgress?.(progress);
  }
}

/**
 * Create a security scanner instance
 */
export function createScanner(options?: ScannerOptions): SecurityScanner {
  return new SecurityScanner(options);
}
