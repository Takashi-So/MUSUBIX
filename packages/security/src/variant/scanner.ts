/**
 * @fileoverview Security Scanner - High-level scanning API
 * @module @nahisaho/musubix-security/variant/scanner
 * @trace TSK-025, REQ-SEC-VARIANT-003
 */

import { CodeDB, createCodeDB } from '../codedb/database.js';
import { CodeDBBuilder, createCodeDBBuilder } from '../codedb/builder.js';
import { VulnerabilityDetector, createDetector } from './detector.js';
import { VulnerabilityModelManager, createModelManager } from './model.js';
import type {
  VulnerabilityFinding,
  ScanConfig,
  ScanResult,
  ScanProgress,
  ScanPhase,
} from '../types/variant.js';
import type { BuildProgress } from '../codedb/builder.js';

/**
 * Default scan configuration
 */
const DEFAULT_SCAN_CONFIG: ScanConfig = {
  includePaths: ['**/*.ts', '**/*.js', '**/*.java', '**/*.go', '**/*.py', '**/*.php'],
  excludePaths: ['**/node_modules/**', '**/vendor/**', '**/dist/**', '**/build/**'],
  languages: [],
  modelIds: [],
  severityThreshold: 'info',
  maxFindings: 1000,
  timeout: 300000, // 5 minutes
  parallel: true,
  incremental: false,
};

/**
 * Progress callback type
 */
type ProgressCallback = (progress: ScanProgress) => void;

/**
 * Security Scanner
 */
export class SecurityScanner {
  private readonly config: ScanConfig;
  private readonly modelManager: VulnerabilityModelManager;
  private readonly detector: VulnerabilityDetector;
  private codeDB: CodeDB | null = null;
  private progressCallback: ProgressCallback | null = null;

  constructor(config?: Partial<ScanConfig>) {
    this.config = { ...DEFAULT_SCAN_CONFIG, ...config };
    this.modelManager = createModelManager();
    this.detector = createDetector(this.modelManager, {
      timeout: this.config.timeout,
    });
  }

  /**
   * Set progress callback
   */
  onProgress(callback: ProgressCallback): void {
    this.progressCallback = callback;
  }

  /**
   * Scan directory for vulnerabilities
   */
  async scan(rootPath: string): Promise<ScanResult> {
    const startTime = Date.now();
    let findings: VulnerabilityFinding[] = [];

    this.reportProgress({
      phase: 'initialization',
      progress: 0,
      message: 'Initializing scanner...',
    });

    try {
      // Phase 1: Build CodeDB
      this.reportProgress({
        phase: 'parsing',
        progress: 10,
        message: 'Building code database...',
      });

      const builder = createCodeDBBuilder({
        includePaths: this.config.includePaths,
        excludePaths: this.config.excludePaths,
        parallel: this.config.parallel,
      });

      // Connect builder progress to scanner progress
      builder.onProgress((buildProgress: BuildProgress) => {
        const overallProgress = 10 + (buildProgress.progress * 0.4);
        this.reportProgress({
          phase: 'parsing',
          progress: overallProgress,
          message: `Parsing: ${buildProgress.filesProcessed}/${buildProgress.totalFiles} files`,
          currentFile: buildProgress.currentFile,
        });
      });

      const buildResult = await builder.build(rootPath);
      this.codeDB = buildResult.database;

      if (buildResult.errors.length > 0) {
        console.warn(`Build warnings: ${buildResult.errors.length} files had errors`);
      }

      // Phase 2: Detect vulnerabilities for each language
      this.reportProgress({
        phase: 'analysis',
        progress: 50,
        message: 'Analyzing code for vulnerabilities...',
      });

      const languages = this.detectLanguages(buildResult);
      const languageProgress = 40 / languages.length;

      for (let i = 0; i < languages.length; i++) {
        const language = languages[i];

        this.reportProgress({
          phase: 'analysis',
          progress: 50 + (i * languageProgress),
          message: `Analyzing ${language} code...`,
        });

        const result = await this.detector.detect(this.codeDB, language);
        findings.push(...result.findings);
      }

      // Phase 3: Post-processing
      this.reportProgress({
        phase: 'reporting',
        progress: 90,
        message: 'Processing findings...',
      });

      // Filter by severity
      findings = this.filterBySeverity(findings);

      // Limit findings
      if (findings.length > this.config.maxFindings) {
        findings = findings.slice(0, this.config.maxFindings);
      }

      // Sort by severity
      findings = this.sortBySeverity(findings);

      // Deduplicate
      findings = this.deduplicate(findings);

      this.reportProgress({
        phase: 'complete',
        progress: 100,
        message: 'Scan complete',
      });

      const executionTime = Date.now() - startTime;

      return {
        findings,
        summary: this.generateSummary(findings),
        metadata: {
          scanId: this.generateScanId(),
          startTime: new Date(startTime).toISOString(),
          endTime: new Date().toISOString(),
          executionTime,
          rootPath,
          config: this.config,
          languagesScanned: languages,
          filesScanned: buildResult.stats.filesSucceeded,
        },
      };
    } catch (error) {
      this.reportProgress({
        phase: 'complete',
        progress: 100,
        message: `Scan failed: ${error instanceof Error ? error.message : String(error)}`,
        error: error instanceof Error ? error.message : String(error),
      });

      throw error;
    }
  }

  /**
   * Scan single file
   */
  async scanFile(filePath: string): Promise<VulnerabilityFinding[]> {
    const builder = createCodeDBBuilder({
      includePaths: [filePath],
      excludePaths: [],
      parallel: false,
    });

    const buildResult = await builder.buildFromFiles([filePath]);
    this.codeDB = buildResult.database;

    const language = this.detectLanguageFromFile(filePath);
    const result = await this.detector.detect(this.codeDB, language);

    return result.findings;
  }

  /**
   * Get model manager for customization
   */
  getModelManager(): VulnerabilityModelManager {
    return this.modelManager;
  }

  /**
   * Get CodeDB for direct queries
   */
  getCodeDB(): CodeDB | null {
    return this.codeDB;
  }

  /**
   * Detect languages from build result
   */
  private detectLanguages(buildResult: { stats: { languageBreakdown?: Map<string, number> } }): string[] {
    const configuredLanguages = this.config.languages;
    if (configuredLanguages && configuredLanguages.length > 0) {
      return configuredLanguages;
    }

    // Auto-detect from build result
    const languages: string[] = [];
    if (buildResult.stats.languageBreakdown) {
      for (const [lang] of buildResult.stats.languageBreakdown) {
        languages.push(lang);
      }
    }

    // Default languages if none detected
    if (languages.length === 0) {
      return ['typescript', 'javascript'];
    }

    return languages;
  }

  /**
   * Detect language from file extension
   */
  private detectLanguageFromFile(filePath: string): string {
    const ext = filePath.split('.').pop()?.toLowerCase();
    switch (ext) {
      case 'ts':
      case 'tsx':
        return 'typescript';
      case 'js':
      case 'jsx':
        return 'javascript';
      case 'java':
        return 'java';
      case 'go':
        return 'go';
      case 'py':
        return 'python';
      case 'php':
        return 'php';
      case 'rb':
        return 'ruby';
      case 'rs':
        return 'rust';
      default:
        return 'typescript';
    }
  }

  /**
   * Filter findings by severity threshold
   */
  private filterBySeverity(findings: VulnerabilityFinding[]): VulnerabilityFinding[] {
    const severityOrder = ['critical', 'high', 'medium', 'low', 'info'];
    const thresholdIndex = severityOrder.indexOf(this.config.severityThreshold);

    return findings.filter((f) => {
      const findingIndex = severityOrder.indexOf(f.severity);
      return findingIndex <= thresholdIndex;
    });
  }

  /**
   * Sort findings by severity (critical first)
   */
  private sortBySeverity(findings: VulnerabilityFinding[]): VulnerabilityFinding[] {
    const severityOrder = ['critical', 'high', 'medium', 'low', 'info'];

    return [...findings].sort((a, b) => {
      const aIndex = severityOrder.indexOf(a.severity);
      const bIndex = severityOrder.indexOf(b.severity);
      if (aIndex !== bIndex) return aIndex - bIndex;

      // Secondary sort by confidence
      const confidenceOrder = ['high', 'medium', 'low'];
      const aConf = confidenceOrder.indexOf(a.confidence);
      const bConf = confidenceOrder.indexOf(b.confidence);
      return aConf - bConf;
    });
  }

  /**
   * Deduplicate findings
   */
  private deduplicate(findings: VulnerabilityFinding[]): VulnerabilityFinding[] {
    const seen = new Set<string>();
    const result: VulnerabilityFinding[] = [];

    for (const finding of findings) {
      const key = `${finding.modelId}:${finding.location.file}:${finding.location.startLine}`;
      if (!seen.has(key)) {
        seen.add(key);
        result.push(finding);
      }
    }

    return result;
  }

  /**
   * Generate scan summary
   */
  private generateSummary(findings: VulnerabilityFinding[]): ScanResult['summary'] {
    const bySeverity = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
      info: 0,
    };

    const byCategory = new Map<string, number>();
    const byCWE = new Map<string, number>();

    for (const finding of findings) {
      bySeverity[finding.severity]++;

      const catCount = byCategory.get(finding.category) ?? 0;
      byCategory.set(finding.category, catCount + 1);

      const cweCount = byCWE.get(finding.cweId) ?? 0;
      byCWE.set(finding.cweId, cweCount + 1);
    }

    // Top CWEs
    const topCWEs = [...byCWE.entries()]
      .sort((a, b) => b[1] - a[1])
      .slice(0, 5)
      .map(([cweId, count]) => ({ cweId, count }));

    return {
      totalFindings: findings.length,
      bySeverity,
      byCategory: Object.fromEntries(byCategory),
      topCWEs,
    };
  }

  /**
   * Generate scan ID
   */
  private generateScanId(): string {
    return `scan-${Date.now()}-${Math.random().toString(36).substring(7)}`;
  }

  /**
   * Report progress
   */
  private reportProgress(progress: ScanProgress): void {
    if (this.progressCallback) {
      this.progressCallback(progress);
    }
  }
}

/**
 * Create security scanner
 */
export function createScanner(config?: Partial<ScanConfig>): SecurityScanner {
  return new SecurityScanner(config);
}

/**
 * Quick scan function
 */
export async function scan(
  rootPath: string,
  config?: Partial<ScanConfig>,
): Promise<ScanResult> {
  const scanner = createScanner(config);
  return scanner.scan(rootPath);
}

/**
 * Quick scan single file
 */
export async function scanFile(
  filePath: string,
  config?: Partial<ScanConfig>,
): Promise<VulnerabilityFinding[]> {
  const scanner = createScanner(config);
  return scanner.scanFile(filePath);
}
