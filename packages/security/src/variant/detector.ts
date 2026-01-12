/**
 * @fileoverview Taint Analysis Detector
 * @module @nahisaho/musubix-security/variant/detector
 * @trace TSK-024, REQ-SEC-VARIANT-002
 * 
 * NOTE: v3.0.11 - Simplified implementation without CodeDB dependency
 */

import type {
  VulnerabilityModel,
  VulnerabilityFinding,
  TaintPathInfo,
  PatternMatcher,
} from '../types/variant.js';
import { VulnerabilityModelManager, defaultModelManager } from './model.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Detector options
 */
export interface DetectorOptions {
  /** Model manager */
  modelManager?: VulnerabilityModelManager;
  /** Max path length */
  maxPathLength?: number;
  /** Timeout per file (ms) */
  timeout?: number;
  /** Enable pattern-based detection */
  enablePatternDetection?: boolean;
}

/**
 * Detector result
 */
export interface DetectorResult {
  /** Findings */
  findings: VulnerabilityFinding[];
  /** Errors */
  errors: string[];
  /** Statistics */
  stats: {
    modelsChecked: number;
    sourcesFound: number;
    sinksFound: number;
    pathsAnalyzed: number;
    duration: number;
  };
}

/**
 * File content with metadata
 */
interface FileContent {
  path: string;
  content: string;
  lines: string[];
}

// ============================================================================
// Detector
// ============================================================================

/**
 * Taint Analysis Detector (v3.0.11 - File-based implementation)
 */
export class TaintDetector {
  private modelManager: VulnerabilityModelManager;
  private enablePatternDetection: boolean;
  private findingId = 0;
  
  /** Max path length for taint analysis (reserved for future use) */
  readonly maxPathLength: number;

  constructor(options: DetectorOptions = {}) {
    this.modelManager = options.modelManager ?? defaultModelManager;
    this.maxPathLength = options.maxPathLength ?? 20;
    this.enablePatternDetection = options.enablePatternDetection ?? true;
  }

  /**
   * Reset finding ID counter (for testing)
   */
  resetIdCounter(): void {
    this.findingId = 0;
  }

  /**
   * Detect vulnerabilities in files
   */
  async detectInFiles(files: FileContent[], language?: string): Promise<DetectorResult> {
    const startTime = Date.now();
    const findings: VulnerabilityFinding[] = [];
    const errors: string[] = [];
    let modelsChecked = 0;
    let sourcesFound = 0;
    let sinksFound = 0;

    const models = language
      ? this.modelManager.getModelsByLanguage(language).filter((m) => this.modelManager.isEnabled(m.id))
      : this.modelManager.getEnabledModels();

    for (const model of models) {
      modelsChecked++;

      try {
        // Pattern-based detection
        if (this.enablePatternDetection && model.patterns && model.patterns.length > 0) {
          for (const file of files) {
            const patternFindings = this.detectPatternsInFile(file, model);
            findings.push(...patternFindings);
          }
          continue;
        }

        // Source/sink detection based on patterns
        for (const file of files) {
          const sourceMatches = this.findSourcesInFile(file, model);
          sourcesFound += sourceMatches.length;

          const sinkMatches = this.findSinksInFile(file, model);
          sinksFound += sinkMatches.length;

          // For each source-sink pair, create a potential finding
          for (const source of sourceMatches) {
            for (const sink of sinkMatches) {
              if (source.line <= sink.line) {
                const finding = this.createFinding(model, file.path, source, sink);
                findings.push(finding);
              }
            }
          }
        }
      } catch (error) {
        errors.push(`Error checking model ${model.id}: ${error}`);
      }
    }

    return {
      findings,
      errors,
      stats: {
        modelsChecked,
        sourcesFound,
        sinksFound,
        pathsAnalyzed: sourcesFound * sinksFound,
        duration: Date.now() - startTime,
      },
    };
  }

  /**
   * Detect patterns in a file
   */
  private detectPatternsInFile(file: FileContent, model: VulnerabilityModel): VulnerabilityFinding[] {
    const findings: VulnerabilityFinding[] = [];

    if (!model.patterns) return findings;

    for (const pattern of model.patterns) {
      let lineNum = 0;
      for (const line of file.lines) {
        lineNum++;
        if (pattern.test(line)) {
          findings.push({
            id: `VULN-${++this.findingId}`,
            ruleId: model.id,
            ruleName: model.name,
            cwe: model.cwe,
            severity: model.severity,
            message: model.messageTemplate?.replace('{location}', `${file.path}:${lineNum}`) 
              ?? `Potential ${model.name} vulnerability detected`,
            location: {
              file: file.path,
              startLine: lineNum,
              endLine: lineNum,
              startColumn: 1,
              endColumn: line.length,
              snippet: line.trim(),
            },
            confidence: 0.7,
            status: 'open',
          });
        }
      }
    }

    return findings;
  }

  /**
   * Find sources in a file
   */
  private findSourcesInFile(file: FileContent, model: VulnerabilityModel): Array<{ line: number; column: number; snippet: string }> {
    const matches: Array<{ line: number; column: number; snippet: string }> = [];

    for (const source of model.sources) {
      const regex = this.matcherToRegex(source.matcher);
      if (!regex) continue;

      let lineNum = 0;
      for (const line of file.lines) {
        lineNum++;
        const match = regex.exec(line);
        if (match) {
          matches.push({
            line: lineNum,
            column: match.index + 1,
            snippet: line.trim(),
          });
        }
      }
    }

    return matches;
  }

  /**
   * Find sinks in a file
   */
  private findSinksInFile(file: FileContent, model: VulnerabilityModel): Array<{ line: number; column: number; snippet: string }> {
    const matches: Array<{ line: number; column: number; snippet: string }> = [];

    for (const sink of model.sinks) {
      const regex = this.matcherToRegex(sink.matcher);
      if (!regex) continue;

      let lineNum = 0;
      for (const line of file.lines) {
        lineNum++;
        const match = regex.exec(line);
        if (match) {
          matches.push({
            line: lineNum,
            column: match.index + 1,
            snippet: line.trim(),
          });
        }
      }
    }

    return matches;
  }

  /**
   * Convert pattern matcher to regex
   */
  private matcherToRegex(matcher: PatternMatcher): RegExp | null {
    switch (matcher.type) {
      case 'exact':
        return new RegExp(
          matcher.value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'),
          matcher.caseSensitive === false ? 'i' : ''
        );
      case 'regex':
        return new RegExp(matcher.pattern, matcher.flags ?? '');
      case 'glob':
        // Simple glob to regex conversion
        const regexPattern = matcher.pattern
          .replace(/[.+^${}()|[\]\\]/g, '\\$&')
          .replace(/\*/g, '.*')
          .replace(/\?/g, '.');
        return new RegExp(regexPattern);
      default:
        return null;
    }
  }

  /**
   * Create a vulnerability finding
   */
  private createFinding(
    model: VulnerabilityModel,
    filePath: string,
    source: { line: number; column: number; snippet: string },
    sink: { line: number; column: number; snippet: string }
  ): VulnerabilityFinding {
    const taintPath: TaintPathInfo = {
      source: {
        id: `source-${source.line}`,
        type: 'source',
        location: {
          file: filePath,
          startLine: source.line,
          endLine: source.line,
          startColumn: source.column,
          endColumn: source.column + 10,
          snippet: source.snippet,
        },
        snippet: source.snippet,
        labels: ['tainted'],
      },
      sink: {
        id: `sink-${sink.line}`,
        type: 'sink',
        location: {
          file: filePath,
          startLine: sink.line,
          endLine: sink.line,
          startColumn: sink.column,
          endColumn: sink.column + 10,
          snippet: sink.snippet,
        },
        snippet: sink.snippet,
        labels: ['vulnerable'],
      },
      path: [],
      length: sink.line - source.line + 1,
    };

    return {
      id: `VULN-${++this.findingId}`,
      ruleId: model.id,
      ruleName: model.name,
      cwe: model.cwe,
      severity: model.severity,
      message: model.messageTemplate?.replace('{location}', `${filePath}:${sink.line}`)
        ?? `Potential ${model.name}: tainted data flows from line ${source.line} to line ${sink.line}`,
      location: {
        file: filePath,
        startLine: sink.line,
        endLine: sink.line,
        startColumn: sink.column,
        endColumn: sink.column + 10,
        snippet: sink.snippet,
      },
      taintPath,
      confidence: 0.6,
      status: 'open',
    };
  }
}

/**
 * Create a taint detector instance
 */
export function createDetector(options?: DetectorOptions): TaintDetector {
  return new TaintDetector(options);
}
