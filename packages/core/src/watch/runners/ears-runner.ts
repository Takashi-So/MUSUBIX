/**
 * EARSRunner - EARS requirement validation for watch mode
 * 
 * Implements: TSK-WATCH-004 (partial), DES-WATCH-004, REQ-WATCH-004
 */

import { readFile } from 'node:fs/promises';
import { extname } from 'node:path';
import type { TaskRunner, Issue } from '../types.js';

/**
 * EARS pattern definitions
 */
const EARS_PATTERNS = [
  {
    name: 'event-driven',
    regex: /WHEN\s+.+,\s+THE\s+.+\s+SHALL\s+.+/i,
    description: 'Event-driven requirement',
  },
  {
    name: 'state-driven',
    regex: /WHILE\s+.+,\s+THE\s+.+\s+SHALL\s+.+/i,
    description: 'State-driven requirement',
  },
  {
    name: 'unwanted',
    regex: /THE\s+.+\s+SHALL\s+NOT\s+.+/i,
    description: 'Unwanted behavior requirement',
  },
  {
    name: 'optional',
    regex: /WHERE\s+.+,\s+THE\s+.+\s+SHALL\s+.+/i,
    description: 'Optional feature requirement',
  },
  {
    name: 'ubiquitous',
    regex: /THE\s+.+\s+SHALL\s+.+/i,
    description: 'Ubiquitous requirement',
  },
];

/**
 * EARSRunner class
 */
export class EARSRunner implements TaskRunner {
  readonly name = 'ears';

  /**
   * Check if runner supports the file
   */
  supports(file: string): boolean {
    const ext = extname(file);
    return ext === '.md';
  }

  /**
   * Run EARS validation on files
   */
  async run(files: string[]): Promise<Issue[]> {
    const issues: Issue[] = [];

    for (const file of files) {
      const fileIssues = await this.validateFile(file);
      issues.push(...fileIssues);
    }

    return issues;
  }

  /**
   * Validate a single file
   */
  private async validateFile(file: string): Promise<Issue[]> {
    const issues: Issue[] = [];

    try {
      const content = await readFile(file, 'utf-8');
      const lines = content.split('\n');

      // Track requirement counts
      let requirementCount = 0;
      let validRequirementCount = 0;

      for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        const lineNum = i + 1;

        // Check for requirements section header (for future use)
        if (/^#+\s*.*(要件|requirement|REQ)/i.test(line)) {
          continue;
        }

        // Check for requirement block (blockquote with bold)
        if (line.startsWith('>') && line.includes('**')) {
          requirementCount++;
          
          // Extract requirement text
          const reqMatch = line.match(/>\s*\*\*(.+?)\*\*:?\s*(.+)/);
          if (reqMatch) {
            const reqText = reqMatch[2].trim();
            
            // Check if it matches any EARS pattern
            const matchedPattern = this.matchEARSPattern(reqText);
            
            if (matchedPattern) {
              validRequirementCount++;
            } else if (reqText.toLowerCase().includes('shall')) {
              // Contains SHALL but doesn't match pattern
              issues.push({
                severity: 'warning',
                message: `Requirement may not fully conform to EARS pattern: "${reqText.slice(0, 50)}..."`,
                file,
                line: lineNum,
                ruleId: 'ears-partial-match',
              });
            } else {
              // Doesn't contain SHALL
              issues.push({
                severity: 'error',
                message: `Requirement must contain "SHALL": "${reqText.slice(0, 50)}..."`,
                file,
                line: lineNum,
                ruleId: 'ears-missing-shall',
              });
            }
          }
        }

        // Check for REQ-* ID without proper EARS format
        if (/REQ-\w+-\d+/i.test(line) && !line.startsWith('>') && !line.startsWith('#')) {
          const nextLine = lines[i + 1] || '';
          if (nextLine.startsWith('>')) {
            // Has requirement block, check it
            const reqText = nextLine.replace(/^>\s*/, '');
            if (!reqText.toLowerCase().includes('shall')) {
              issues.push({
                severity: 'warning',
                message: `Requirement block should use EARS format with SHALL`,
                file,
                line: lineNum + 1,
                ruleId: 'ears-format-suggestion',
              });
            }
          }
        }
      }

      // Summary if requirements found
      if (requirementCount > 0 && validRequirementCount < requirementCount) {
        issues.push({
          severity: 'info',
          message: `EARS validation: ${validRequirementCount}/${requirementCount} requirements conform to EARS patterns`,
          file,
          ruleId: 'ears-summary',
        });
      }
    } catch (error) {
      issues.push({
        severity: 'error',
        message: `Failed to read file: ${error instanceof Error ? error.message : String(error)}`,
        file,
        ruleId: 'ears-read-error',
      });
    }

    return issues;
  }

  /**
   * Match text against EARS patterns
   */
  private matchEARSPattern(text: string): { name: string; description: string } | null {
    for (const pattern of EARS_PATTERNS) {
      if (pattern.regex.test(text)) {
        return { name: pattern.name, description: pattern.description };
      }
    }
    return null;
  }
}

/**
 * Create an EARSRunner instance
 */
export function createEARSRunner(): EARSRunner {
  return new EARSRunner();
}
