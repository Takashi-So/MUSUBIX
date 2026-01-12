/**
 * SecurityRunner - Security Extractor integration for watch mode
 * 
 * Implements: TSK-WATCH-006, DES-WATCH-005, REQ-WATCH-005
 */

import { extname } from 'node:path';
import type { TaskRunner, Issue } from '../types.js';

/**
 * Language to extension mapping
 */
const LANGUAGE_EXTENSIONS: Record<string, string[]> = {
  typescript: ['.ts', '.tsx'],
  javascript: ['.js', '.jsx', '.mjs', '.cjs'],
  python: ['.py'],
  ruby: ['.rb'],
  rust: ['.rs'],
  c: ['.c', '.h'],
  go: ['.go'],
};

/**
 * All supported extensions
 */
const ALL_EXTENSIONS = Object.values(LANGUAGE_EXTENSIONS).flat();

/**
 * SecurityRunner class
 */
export class SecurityRunner implements TaskRunner {
  readonly name = 'security';
  
  private securityPackage: typeof import('@nahisaho/musubix-security') | null = null;

  /**
   * Check if runner supports the file
   */
  supports(file: string): boolean {
    const ext = extname(file);
    return ALL_EXTENSIONS.includes(ext);
  }

  /**
   * Get language from extension
   */
  private getLanguage(file: string): string | null {
    const ext = extname(file);
    for (const [lang, extensions] of Object.entries(LANGUAGE_EXTENSIONS)) {
      if (extensions.includes(ext)) {
        return lang;
      }
    }
    return null;
  }

  /**
   * Dynamically import security package
   */
  private async getSecurityPackage(): Promise<typeof import('@nahisaho/musubix-security') | null> {
    if (this.securityPackage) {
      return this.securityPackage;
    }

    try {
      this.securityPackage = await import('@nahisaho/musubix-security');
      return this.securityPackage;
    } catch {
      return null;
    }
  }

  /**
   * Run security scan on files
   */
  async run(files: string[]): Promise<Issue[]> {
    if (files.length === 0) return [];

    const issues: Issue[] = [];
    const security = await this.getSecurityPackage();

    if (!security) {
      return [{
        severity: 'warning',
        message: 'Security package (@nahisaho/musubix-security) not available',
        file: files[0],
      }];
    }

    // Group files by language
    const filesByLanguage = new Map<string, string[]>();
    for (const file of files) {
      const lang = this.getLanguage(file);
      if (lang) {
        const existing = filesByLanguage.get(lang) ?? [];
        existing.push(file);
        filesByLanguage.set(lang, existing);
      }
    }

    // Scan each language group
    for (const [language, langFiles] of filesByLanguage) {
      try {
        const langIssues = await this.scanFiles(security, language, langFiles);
        issues.push(...langIssues);
      } catch (error) {
        issues.push({
          severity: 'warning',
          message: `Security scan failed for ${language}: ${error instanceof Error ? error.message : String(error)}`,
          file: langFiles[0],
        });
      }
    }

    return issues;
  }

  /**
   * Scan files with security extractor
   */
  private async scanFiles(
    security: typeof import('@nahisaho/musubix-security'),
    language: string,
    files: string[]
  ): Promise<Issue[]> {
    const issues: Issue[] = [];

    // Use createExtractor if available
    if ('createExtractor' in security) {
      for (const file of files) {
        try {
          const { readFile } = await import('node:fs/promises');
          const content = await readFile(file, 'utf-8');
          
          const extractor = (security.createExtractor as Function)(language);
          if (!extractor) continue;

          const result = await extractor.extract(content, file);
          
          // Convert security findings to issues
          if (result.sources) {
            for (const source of result.sources) {
              issues.push({
                severity: 'warning',
                message: `Potential taint source: ${source.type}`,
                file,
                line: source.location?.line,
                column: source.location?.column,
                ruleId: `security-source-${source.type}`,
                context: { source },
              });
            }
          }

          if (result.sinks) {
            for (const sink of result.sinks) {
              issues.push({
                severity: 'error',
                message: `Potential security sink: ${sink.type}`,
                file,
                line: sink.location?.line,
                column: sink.location?.column,
                ruleId: `security-sink-${sink.type}`,
                context: { sink },
              });
            }
          }
        } catch (error) {
          issues.push({
            severity: 'warning',
            message: `Failed to scan ${file}: ${error instanceof Error ? error.message : String(error)}`,
            file,
          });
        }
      }
    }

    return issues;
  }
}

/**
 * Create a SecurityRunner instance
 */
export function createSecurityRunner(): SecurityRunner {
  return new SecurityRunner();
}
