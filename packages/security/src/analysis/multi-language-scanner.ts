/**
 * @fileoverview Multi-language vulnerability scanner - unified scanner for TypeScript, JavaScript, Python, PHP
 * @module @nahisaho/musubix-security/analysis/multi-language-scanner
 * @trace REQ-SEC-MULTI-001
 */

import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import { Dirent } from 'node:fs';
import type {
  Vulnerability,
  ScanOptions,
  ScanResult,
} from '../types/index.js';
import { VulnerabilityScanner, createVulnerabilityScanner } from './vulnerability-scanner.js';
import { PythonScanner, createPythonScanner } from './python-scanner.js';
import { PhpScanner, createPhpScanner } from './php-scanner.js';

/**
 * Language type
 */
export type SupportedLanguage = 'typescript' | 'javascript' | 'python' | 'php';

/**
 * Multi-language scan options
 */
export interface MultiLanguageScanOptions extends ScanOptions {
  /** Languages to scan (default: all) */
  languages?: SupportedLanguage[];
}

/**
 * Multi-language scan result
 */
export interface MultiLanguageScanResult extends ScanResult {
  /** Results by language */
  byLanguage: Record<SupportedLanguage, {
    vulnerabilities: Vulnerability[];
    scannedFiles: number;
  }>;
}

/**
 * File extension to language mapping
 */
const EXTENSION_TO_LANGUAGE: Record<string, SupportedLanguage> = {
  '.ts': 'typescript',
  '.tsx': 'typescript',
  '.mts': 'typescript',
  '.cts': 'typescript',
  '.js': 'javascript',
  '.jsx': 'javascript',
  '.mjs': 'javascript',
  '.cjs': 'javascript',
  '.py': 'python',
  '.pyw': 'python',
  '.php': 'php',
  '.phtml': 'php',
  '.php5': 'php',
  '.php7': 'php',
};

/**
 * Multi-language vulnerability scanner
 */
export class MultiLanguageScanner {
  private tsScanner: VulnerabilityScanner;
  private pythonScanner: PythonScanner;
  private phpScanner: PhpScanner;

  constructor() {
    this.tsScanner = createVulnerabilityScanner();
    this.pythonScanner = createPythonScanner();
    this.phpScanner = createPhpScanner();
  }

  /**
   * Detect language from file extension
   */
  detectLanguage(filePath: string): SupportedLanguage | null {
    const ext = path.extname(filePath).toLowerCase();
    return EXTENSION_TO_LANGUAGE[ext] ?? null;
  }

  /**
   * Get all supported languages
   */
  getSupportedLanguages(): SupportedLanguage[] {
    return ['typescript', 'javascript', 'python', 'php'];
  }

  /**
   * Get supported extensions
   */
  getSupportedExtensions(): string[] {
    return Object.keys(EXTENSION_TO_LANGUAGE);
  }

  /**
   * Scan a single file
   */
  async scanFile(filePath: string): Promise<Vulnerability[]> {
    const language = this.detectLanguage(filePath);
    if (!language) {
      return [];
    }

    switch (language) {
      case 'typescript':
      case 'javascript':
        return this.tsScanner.scanFile(filePath);
      case 'python':
        return this.pythonScanner.scanFile(filePath);
      case 'php':
        return this.phpScanner.scanFile(filePath);
      default:
        return [];
    }
  }

  /**
   * Scan content with specified language
   * Note: TypeScript/JavaScript only supports file-based scanning via ts-morph
   */
  scanContent(content: string, language: SupportedLanguage, filePath?: string): Vulnerability[] {
    switch (language) {
      case 'typescript':
      case 'javascript':
        // TypeScript scanner requires file-based scanning (ts-morph)
        // For content scanning, use Python or PHP
        console.warn('TypeScript/JavaScript content scanning not supported. Use scanFile() instead.');
        return [];
      case 'python':
        return this.pythonScanner.scanContent(content, filePath ?? 'unknown.py');
      case 'php':
        return this.phpScanner.scanContent(content, filePath ?? 'unknown.php');
      default:
        return [];
    }
  }

  /**
   * Scan a directory for all supported languages
   */
  async scanDirectory(
    rootPath: string,
    options?: MultiLanguageScanOptions
  ): Promise<MultiLanguageScanResult> {
    const startTime = Date.now();
    const allVulnerabilities: Vulnerability[] = [];
    let totalScannedFiles = 0;
    let totalSkippedFiles = 0;

    const byLanguage: Record<SupportedLanguage, { vulnerabilities: Vulnerability[]; scannedFiles: number }> = {
      typescript: { vulnerabilities: [], scannedFiles: 0 },
      javascript: { vulnerabilities: [], scannedFiles: 0 },
      python: { vulnerabilities: [], scannedFiles: 0 },
      php: { vulnerabilities: [], scannedFiles: 0 },
    };

    const enabledLanguages = options?.languages ?? this.getSupportedLanguages();

    const scanDir = async (dirPath: string) => {
      let entries: Dirent[];
      try {
        entries = await fs.readdir(dirPath, { withFileTypes: true });
      } catch {
        return;
      }

      for (const entry of entries) {
        const fullPath = path.join(dirPath, entry.name);

        if (entry.isDirectory()) {
          // Skip common non-source directories
          const skipDirs = [
            '.git', 'node_modules', '__pycache__', 'venv', '.venv', 
            'env', '.env', 'vendor', 'cache', 'tmp', 'dist', 'build',
            '.next', '.nuxt', 'coverage', '.nyc_output'
          ];
          if (skipDirs.includes(entry.name)) {
            continue;
          }
          await scanDir(fullPath);
        } else if (entry.isFile()) {
          const language = this.detectLanguage(fullPath);
          if (!language || !enabledLanguages.includes(language)) {
            continue;
          }

          // Apply exclude patterns
          if (options?.excludePatterns?.some(p => fullPath.includes(p))) {
            totalSkippedFiles++;
            continue;
          }

          try {
            const vulns = await this.scanFile(fullPath);
            allVulnerabilities.push(...vulns);
            byLanguage[language].vulnerabilities.push(...vulns);
            byLanguage[language].scannedFiles++;
            totalScannedFiles++;
          } catch (error) {
            console.warn(`Warning: Failed to scan ${fullPath}: ${error}`);
            totalSkippedFiles++;
          }
        }
      }
    };

    await scanDir(rootPath);

    const duration = Date.now() - startTime;

    return {
      vulnerabilities: allVulnerabilities,
      scannedFiles: totalScannedFiles,
      skippedFiles: totalSkippedFiles,
      duration,
      timestamp: new Date(),
      options: options ?? {},
      summary: {
        critical: allVulnerabilities.filter(v => v.severity === 'critical').length,
        high: allVulnerabilities.filter(v => v.severity === 'high').length,
        medium: allVulnerabilities.filter(v => v.severity === 'medium').length,
        low: allVulnerabilities.filter(v => v.severity === 'low').length,
        info: allVulnerabilities.filter(v => v.severity === 'info').length,
        total: allVulnerabilities.length,
      },
      byLanguage,
    };
  }

  /**
   * Get rule count by language
   */
  getRuleCountByLanguage(): Record<SupportedLanguage, number> {
    return {
      typescript: this.tsScanner.getRuleCount(),
      javascript: this.tsScanner.getRuleCount(), // Same as TypeScript
      python: this.pythonScanner.getRuleCount(),
      php: this.phpScanner.getRuleCount(),
    };
  }

  /**
   * Get total rule count
   */
  getTotalRuleCount(): number {
    const counts = this.getRuleCountByLanguage();
    // TypeScript and JavaScript share rules, so count only once
    return counts.typescript + counts.python + counts.php;
  }

  /**
   * Get CWE coverage
   */
  getCWECoverage(): string[] {
    const cwes = new Set<string>();

    // TypeScript/JavaScript CWEs
    const tsRules = [
      'CWE-89', 'CWE-79', 'CWE-78', 'CWE-22', 'CWE-327', 'CWE-798',
      'CWE-918', 'CWE-502', 'CWE-611', 'CWE-90', 'CWE-1333', 'CWE-362'
    ];
    tsRules.forEach(cwe => cwes.add(cwe));

    // Python CWEs
    const pythonRules = [
      'CWE-89', 'CWE-78', 'CWE-94', 'CWE-95', 'CWE-22', 'CWE-502',
      'CWE-611', 'CWE-918', 'CWE-90', 'CWE-798', 'CWE-327', 'CWE-328',
      'CWE-489', 'CWE-1333', 'CWE-1336', 'CWE-617'
    ];
    pythonRules.forEach(cwe => cwes.add(cwe));

    // PHP CWEs
    const phpRules = [
      'CWE-89', 'CWE-79', 'CWE-78', 'CWE-94', 'CWE-95', 'CWE-98',
      'CWE-22', 'CWE-502', 'CWE-918', 'CWE-611', 'CWE-90', 'CWE-798',
      'CWE-327', 'CWE-328', 'CWE-384', 'CWE-601', 'CWE-209', 'CWE-614',
      'CWE-1004'
    ];
    phpRules.forEach(cwe => cwes.add(cwe));

    return Array.from(cwes).sort();
  }
}

/**
 * Create multi-language scanner
 */
export function createMultiLanguageScanner(): MultiLanguageScanner {
  return new MultiLanguageScanner();
}
