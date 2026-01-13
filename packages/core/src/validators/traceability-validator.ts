/**
 * Traceability Validator
 *
 * Validates traceability between requirements (REQ-*) and designs (DES-*).
 *
 * @packageDocumentation
 * @module validators/traceability-validator
 *
 * @see REQ-VAL-002 - 設計トレーサビリティ検証
 * @see TSK-VAL-002 - 設計トレーサビリティタスク
 * @see Article V - Traceability
 */

import { readFile, readdir } from 'fs/promises';
import { join, extname } from 'path';

/**
 * Artifact reference
 */
export interface ArtifactRef {
  /** Artifact ID (e.g., REQ-001, DES-001) */
  id: string;
  /** Artifact type */
  type: 'requirement' | 'design' | 'task' | 'code' | 'test';
  /** Source file path */
  filePath: string;
  /** Line number where defined */
  lineNumber: number;
  /** Title or name */
  title?: string;
}

/**
 * Traceability link
 */
export interface TraceLink {
  /** Source artifact ID */
  source: string;
  /** Target artifact ID */
  target: string;
  /** Link type */
  type: 'traces-to' | 'implements' | 'tests' | 'derived-from';
  /** Source file where link was found */
  filePath: string;
  /** Line number */
  lineNumber: number;
}

/**
 * Traceability validation result
 */
export interface TraceabilityValidationResult {
  /** Whether traceability is complete */
  valid: boolean;
  /** Requirements found */
  requirements: ArtifactRef[];
  /** Designs found */
  designs: ArtifactRef[];
  /** Trace links found */
  links: TraceLink[];
  /** Orphan requirements (no design traces to them) */
  orphanRequirements: ArtifactRef[];
  /** Orphan designs (don't trace to any requirement) */
  orphanDesigns: ArtifactRef[];
  /** Coverage percentage */
  coverage: {
    requirementsCovered: number;
    requirementsTotal: number;
    percentage: number;
  };
  /** Issues found */
  issues: TraceabilityIssue[];
}

/**
 * Traceability issue
 */
export interface TraceabilityIssue {
  /** Issue severity */
  severity: 'error' | 'warning' | 'info';
  /** Issue code */
  code: string;
  /** Issue message */
  message: string;
  /** Related artifact ID */
  artifactId?: string;
  /** File path */
  filePath?: string;
  /** Line number */
  lineNumber?: number;
}

/**
 * Validator options
 */
export interface TraceabilityValidatorOptions {
  /** Path to specs directory */
  specsDir?: string;
  /** Path to design directory */
  designDir?: string;
  /** Require 100% coverage */
  requireFullCoverage?: boolean;
  /** Minimum coverage percentage */
  minCoverage?: number;
}

const DEFAULT_OPTIONS: Required<TraceabilityValidatorOptions> = {
  specsDir: 'storage/specs',
  designDir: 'storage/design',
  requireFullCoverage: false,
  minCoverage: 80,
};

// Regex patterns for artifact IDs
const REQ_PATTERN = /\b(REQ-[A-Z0-9]+-?\d*)\b/g;
const DES_PATTERN = /\b(DES-[A-Z0-9]+-?\d*)\b/g;
// TSK_PATTERN is reserved for future task traceability features
// Uncomment when task traceability is implemented:
// const TSK_PATTERN = /\b(TSK-[A-Z0-9]+-?\d*)\b/g;

/**
 * Traceability Validator
 *
 * Validates that requirements have corresponding designs and vice versa.
 */
export class TraceabilityValidator {
  private options: Required<TraceabilityValidatorOptions>;

  constructor(options?: TraceabilityValidatorOptions) {
    this.options = { ...DEFAULT_OPTIONS, ...options };
  }

  /**
   * Validate traceability from a project root
   *
   * @param projectRoot - Project root directory
   * @returns Validation result
   */
  async validate(projectRoot: string): Promise<TraceabilityValidationResult> {
    const specsDir = join(projectRoot, this.options.specsDir);
    const designDir = join(projectRoot, this.options.designDir);

    // Extract artifacts from directories
    const requirements = await this.extractArtifacts(specsDir, 'requirement');
    const designs = await this.extractArtifacts(designDir, 'design');

    // Extract links from design files
    const links = await this.extractLinks(designDir, designs);

    // Find orphans
    const coveredReqIds = new Set(links.map((l) => l.target));
    const orphanRequirements = requirements.filter(
      (r) => !coveredReqIds.has(r.id)
    );

    const orphanDesigns = designs.filter((d) => {
      // A design is orphan if it doesn't link to any requirement
      const hasLink = links.some((l) => l.source === d.id);
      return !hasLink;
    });

    // Calculate coverage
    const requirementsCovered = requirements.length - orphanRequirements.length;
    const coverage = {
      requirementsCovered,
      requirementsTotal: requirements.length,
      percentage:
        requirements.length > 0
          ? Math.round((requirementsCovered / requirements.length) * 100)
          : 100,
    };

    // Generate issues
    const issues = this.generateIssues(
      orphanRequirements,
      orphanDesigns,
      coverage
    );

    // Determine validity
    const valid =
      issues.filter((i) => i.severity === 'error').length === 0 &&
      coverage.percentage >= this.options.minCoverage;

    return {
      valid,
      requirements,
      designs,
      links,
      orphanRequirements,
      orphanDesigns,
      coverage,
      issues,
    };
  }

  /**
   * Validate a single design file
   *
   * @param designFilePath - Path to design file
   * @param requirements - Known requirements to validate against
   * @returns Validation result for the file
   */
  async validateDesignFile(
    designFilePath: string,
    requirements: ArtifactRef[]
  ): Promise<TraceabilityValidationResult> {
    const content = await readFile(designFilePath, 'utf-8');
    const designs = this.extractArtifactsFromContent(
      content,
      designFilePath,
      'design'
    );
    const links = this.extractLinksFromContent(content, designFilePath, designs);

    const coveredReqIds = new Set(links.map((l) => l.target));
    const orphanRequirements = requirements.filter(
      (r) => !coveredReqIds.has(r.id)
    );

    const orphanDesigns = designs.filter((d) => {
      const hasLink = links.some((l) => l.source === d.id);
      return !hasLink;
    });

    const requirementsCovered = requirements.length - orphanRequirements.length;
    const coverage = {
      requirementsCovered,
      requirementsTotal: requirements.length,
      percentage:
        requirements.length > 0
          ? Math.round((requirementsCovered / requirements.length) * 100)
          : 100,
    };

    const issues = this.generateIssues(
      orphanRequirements,
      orphanDesigns,
      coverage
    );

    const valid =
      issues.filter((i) => i.severity === 'error').length === 0 &&
      coverage.percentage >= this.options.minCoverage;

    return {
      valid,
      requirements,
      designs,
      links,
      orphanRequirements,
      orphanDesigns,
      coverage,
      issues,
    };
  }

  /**
   * Extract artifacts from directory
   */
  private async extractArtifacts(
    dirPath: string,
    type: 'requirement' | 'design'
  ): Promise<ArtifactRef[]> {
    const artifacts: ArtifactRef[] = [];

    try {
      const files = await readdir(dirPath);

      for (const file of files) {
        if (extname(file) !== '.md') continue;

        const filePath = join(dirPath, file);
        const content = await readFile(filePath, 'utf-8');
        const extracted = this.extractArtifactsFromContent(
          content,
          filePath,
          type
        );
        artifacts.push(...extracted);
      }
    } catch {
      // Directory doesn't exist, return empty
    }

    return artifacts;
  }

  /**
   * Extract artifacts from content
   */
  private extractArtifactsFromContent(
    content: string,
    filePath: string,
    type: 'requirement' | 'design'
  ): ArtifactRef[] {
    const artifacts: ArtifactRef[] = [];
    const pattern = type === 'requirement' ? REQ_PATTERN : DES_PATTERN;
    const lines = content.split('\n');
    const seenIds = new Set<string>();

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      const matches = line.matchAll(pattern);

      for (const match of matches) {
        const id = match[0];
        // Only add first occurrence (definition)
        if (seenIds.has(id)) continue;
        seenIds.add(id);

        // Try to extract title from same line or next line
        let title: string | undefined;
        const titleMatch = line.match(/[#|]\s*\**(.+?)\**/);
        if (titleMatch) {
          title = titleMatch[1].replace(id, '').replace(/[:|]/, '').trim();
        }

        artifacts.push({
          id,
          type,
          filePath,
          lineNumber: i + 1,
          title: title || undefined,
        });
      }
    }

    return artifacts;
  }

  /**
   * Extract links from design directory
   */
  private async extractLinks(
    designDir: string,
    designs: ArtifactRef[]
  ): Promise<TraceLink[]> {
    const links: TraceLink[] = [];

    try {
      const files = await readdir(designDir);

      for (const file of files) {
        if (extname(file) !== '.md') continue;

        const filePath = join(designDir, file);
        const content = await readFile(filePath, 'utf-8');
        const fileLinks = this.extractLinksFromContent(content, filePath, designs);
        links.push(...fileLinks);
      }
    } catch {
      // Directory doesn't exist
    }

    return links;
  }

  /**
   * Extract links from content
   */
  private extractLinksFromContent(
    content: string,
    filePath: string,
    designs: ArtifactRef[]
  ): TraceLink[] {
    const links: TraceLink[] = [];
    const lines = content.split('\n');

    // Build a map of design IDs for quick lookup
    const designIds = new Set(designs.map((d) => d.id));

    // Track current design context
    let currentDesignId: string | null = null;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];

      // Check if this line defines a design
      const desMatch = line.match(DES_PATTERN);
      if (desMatch && designIds.has(desMatch[0])) {
        currentDesignId = desMatch[0];
      }

      // Check for requirement references
      const reqMatches = line.matchAll(REQ_PATTERN);
      for (const match of reqMatches) {
        const reqId = match[0];

        // Determine link source
        const sourceId = currentDesignId ?? 'UNKNOWN';

        links.push({
          source: sourceId,
          target: reqId,
          type: 'traces-to',
          filePath,
          lineNumber: i + 1,
        });
      }
    }

    return links;
  }

  /**
   * Generate issues from orphans and coverage
   */
  private generateIssues(
    orphanRequirements: ArtifactRef[],
    orphanDesigns: ArtifactRef[],
    coverage: { percentage: number }
  ): TraceabilityIssue[] {
    const issues: TraceabilityIssue[] = [];

    // Orphan requirements
    for (const req of orphanRequirements) {
      issues.push({
        severity: 'warning',
        code: 'ORPHAN_REQUIREMENT',
        message: `Requirement ${req.id} has no design tracing to it`,
        artifactId: req.id,
        filePath: req.filePath,
        lineNumber: req.lineNumber,
      });
    }

    // Orphan designs
    for (const des of orphanDesigns) {
      issues.push({
        severity: 'warning',
        code: 'ORPHAN_DESIGN',
        message: `Design ${des.id} does not trace to any requirement`,
        artifactId: des.id,
        filePath: des.filePath,
        lineNumber: des.lineNumber,
      });
    }

    // Coverage below threshold
    if (
      this.options.requireFullCoverage &&
      coverage.percentage < 100
    ) {
      issues.push({
        severity: 'error',
        code: 'INCOMPLETE_COVERAGE',
        message: `Traceability coverage is ${coverage.percentage}%, but 100% is required`,
      });
    } else if (coverage.percentage < this.options.minCoverage) {
      issues.push({
        severity: 'error',
        code: 'LOW_COVERAGE',
        message: `Traceability coverage is ${coverage.percentage}%, below minimum of ${this.options.minCoverage}%`,
      });
    }

    return issues;
  }

  /**
   * Generate a report from validation result
   */
  generateReport(result: TraceabilityValidationResult): string {
    const lines: string[] = [
      '# Traceability Validation Report',
      '',
      `**Status**: ${result.valid ? '✅ PASSED' : '❌ FAILED'}`,
      '',
      '## Coverage',
      '',
      `- Requirements covered: ${result.coverage.requirementsCovered}/${result.coverage.requirementsTotal}`,
      `- Coverage: ${result.coverage.percentage}%`,
      '',
    ];

    if (result.orphanRequirements.length > 0) {
      lines.push('## Orphan Requirements (No Design)');
      lines.push('');
      for (const req of result.orphanRequirements) {
        lines.push(`- ${req.id}${req.title ? `: ${req.title}` : ''}`);
      }
      lines.push('');
    }

    if (result.orphanDesigns.length > 0) {
      lines.push('## Orphan Designs (No Requirement Link)');
      lines.push('');
      for (const des of result.orphanDesigns) {
        lines.push(`- ${des.id}${des.title ? `: ${des.title}` : ''}`);
      }
      lines.push('');
    }

    if (result.issues.length > 0) {
      lines.push('## Issues');
      lines.push('');
      for (const issue of result.issues) {
        const icon =
          issue.severity === 'error'
            ? '❌'
            : issue.severity === 'warning'
            ? '⚠️'
            : 'ℹ️';
        lines.push(`${icon} [${issue.code}] ${issue.message}`);
      }
      lines.push('');
    }

    return lines.join('\n');
  }
}

/**
 * Convenience function to validate traceability
 *
 * @param projectRoot - Project root directory
 * @param options - Validator options
 * @returns Validation result
 */
export async function validateTraceability(
  projectRoot: string,
  options?: TraceabilityValidatorOptions
): Promise<TraceabilityValidationResult> {
  const validator = new TraceabilityValidator(options);
  return validator.validate(projectRoot);
}
