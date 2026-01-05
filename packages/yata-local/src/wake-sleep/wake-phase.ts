/**
 * @fileoverview Wake Phase Implementation for YATA Local
 * @module @nahisaho/yata-local/wake-sleep
 * @version 0.1.0
 * @license MIT
 * 
 * Trace: REQ-WSL-001, TSK-WSL-001
 */

import { randomUUID } from 'crypto';
import * as fs from 'fs/promises';
import * as path from 'path';
import type {
  LocalPatternCandidate,
  LocalPatternType,
  WakeObserveOptions,
  WakeObserveResult,
} from './types.js';

/**
 * Wake Phase - Pattern Observation and Extraction
 * 
 * Responsible for:
 * - Scanning source files
 * - Extracting pattern candidates
 * - Computing initial confidence scores
 */
export class LocalWakePhase {
  private readonly options: Required<WakeObserveOptions>;

  constructor(options: Partial<WakeObserveOptions> = {}) {
    this.options = {
      extensions: options.extensions ?? ['.ts', '.tsx', '.js', '.jsx'],
      excludeDirs: options.excludeDirs ?? ['node_modules', 'dist', 'build', '.git'],
      minConfidence: options.minConfidence ?? 0.3,
      maxCandidates: options.maxCandidates ?? 1000,
      includePrivate: options.includePrivate ?? false,
    };
  }

  /**
   * Observe a single file and extract pattern candidates
   */
  async observe(filePath: string): Promise<LocalPatternCandidate[]> {
    const candidates: LocalPatternCandidate[] = [];

    try {
      const content = await fs.readFile(filePath, 'utf-8');
      const language = this.detectLanguage(filePath);
      const extracted = this.extractPatterns(content, filePath, language);
      
      for (const pattern of extracted) {
        if (pattern.confidence >= this.options.minConfidence) {
          candidates.push(pattern);
        }
      }
    } catch (_error) {
      // File read error - skip silently
    }

    return candidates.slice(0, this.options.maxCandidates);
  }

  /**
   * Observe a directory recursively
   */
  async observeDirectory(dirPath: string): Promise<WakeObserveResult> {
    const startTime = Date.now();
    const candidates: LocalPatternCandidate[] = [];
    const errors: Array<{ file: string; error: string }> = [];
    let filesScanned = 0;
    let skippedFiles = 0;

    const processDir = async (currentPath: string): Promise<void> => {
      try {
        const entries = await fs.readdir(currentPath, { withFileTypes: true });

        for (const entry of entries) {
          const fullPath = path.join(currentPath, entry.name);

          if (entry.isDirectory()) {
            if (!this.options.excludeDirs.includes(entry.name)) {
              await processDir(fullPath);
            } else {
              skippedFiles++;
            }
          } else if (entry.isFile()) {
            const ext = path.extname(entry.name);
            if (this.options.extensions.includes(ext)) {
              try {
                const filePatterns = await this.observe(fullPath);
                candidates.push(...filePatterns);
                filesScanned++;
              } catch (error) {
                errors.push({
                  file: fullPath,
                  error: error instanceof Error ? error.message : String(error),
                });
              }
            } else {
              skippedFiles++;
            }
          }
        }
      } catch (error) {
        errors.push({
          file: currentPath,
          error: error instanceof Error ? error.message : String(error),
        });
      }
    };

    await processDir(dirPath);

    // Limit total candidates
    const limitedCandidates = candidates.slice(0, this.options.maxCandidates);

    return {
      candidates: limitedCandidates,
      stats: {
        filesScanned,
        candidatesFound: limitedCandidates.length,
        skippedFiles,
        processingTimeMs: Date.now() - startTime,
      },
      errors,
    };
  }

  /**
   * Detect language from file extension
   */
  private detectLanguage(filePath: string): LocalPatternCandidate['language'] {
    const ext = path.extname(filePath).toLowerCase();
    switch (ext) {
      case '.ts':
      case '.tsx':
        return 'typescript';
      case '.js':
      case '.jsx':
        return 'javascript';
      case '.py':
        return 'python';
      default:
        return 'other';
    }
  }

  /**
   * Extract patterns from source content
   * Uses simple regex-based parsing for lightweight extraction
   */
  private extractPatterns(
    content: string,
    filePath: string,
    language: LocalPatternCandidate['language']
  ): LocalPatternCandidate[] {
    const patterns: LocalPatternCandidate[] = [];
    const lines = content.split('\n');

    // Extract functions/methods
    patterns.push(...this.extractFunctions(lines, filePath, language));

    // Extract classes
    patterns.push(...this.extractClasses(lines, filePath, language));

    // Extract interfaces (TypeScript)
    if (language === 'typescript') {
      patterns.push(...this.extractInterfaces(lines, filePath, language));
      patterns.push(...this.extractTypes(lines, filePath, language));
    }

    // Extract imports
    patterns.push(...this.extractImports(lines, filePath, language));

    // Extract exports
    patterns.push(...this.extractExports(lines, filePath, language));

    return patterns;
  }

  /**
   * Extract function patterns
   */
  private extractFunctions(
    lines: string[],
    filePath: string,
    language: LocalPatternCandidate['language']
  ): LocalPatternCandidate[] {
    const patterns: LocalPatternCandidate[] = [];
    
    // Match: function name(), async function name(), const name = () =>, etc.
    const functionPatterns = [
      /^(?:export\s+)?(?:async\s+)?function\s+(\w+)/,
      /^(?:export\s+)?const\s+(\w+)\s*=\s*(?:async\s+)?(?:\([^)]*\)|[a-zA-Z_]\w*)\s*=>/,
      /^(?:export\s+)?(?:async\s+)?(\w+)\s*\([^)]*\)\s*(?::\s*\S+)?\s*\{/,
    ];

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i].trim();
      
      for (const pattern of functionPatterns) {
        const match = line.match(pattern);
        if (match) {
          const name = match[1];
          if (!this.options.includePrivate && name.startsWith('_')) continue;

          // Find function end (simple brace counting)
          const { endLine, content } = this.extractBlock(lines, i);
          
          patterns.push(this.createCandidate({
            type: 'function_signature',
            name,
            content,
            sourcePath: filePath,
            lineRange: { start: i + 1, end: endLine + 1 },
            language,
            confidence: this.calculateConfidence('function_signature', content),
          }));
          break;
        }
      }
    }

    return patterns;
  }

  /**
   * Extract class patterns
   */
  private extractClasses(
    lines: string[],
    filePath: string,
    language: LocalPatternCandidate['language']
  ): LocalPatternCandidate[] {
    const patterns: LocalPatternCandidate[] = [];
    const classPattern = /^(?:export\s+)?(?:abstract\s+)?class\s+(\w+)/;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i].trim();
      const match = line.match(classPattern);
      
      if (match) {
        const name = match[1];
        const { endLine, content } = this.extractBlock(lines, i);
        
        // Determine class type
        let type: LocalPatternType = 'class_structure';
        if (name.endsWith('Repository')) type = 'repository_pattern';
        else if (name.endsWith('Service')) type = 'service_pattern';
        else if (name.endsWith('Factory')) type = 'factory_pattern';
        else if (name.endsWith('Entity')) type = 'entity';
        else if (name.endsWith('ValueObject') || content.includes('readonly')) type = 'value_object';
        
        patterns.push(this.createCandidate({
          type,
          name,
          content,
          sourcePath: filePath,
          lineRange: { start: i + 1, end: endLine + 1 },
          language,
          confidence: this.calculateConfidence(type, content),
        }));
      }
    }

    return patterns;
  }

  /**
   * Extract interface patterns (TypeScript)
   */
  private extractInterfaces(
    lines: string[],
    filePath: string,
    language: LocalPatternCandidate['language']
  ): LocalPatternCandidate[] {
    const patterns: LocalPatternCandidate[] = [];
    const interfacePattern = /^(?:export\s+)?interface\s+(\w+)/;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i].trim();
      const match = line.match(interfacePattern);
      
      if (match) {
        const name = match[1];
        const { endLine, content } = this.extractBlock(lines, i);
        
        patterns.push(this.createCandidate({
          type: 'interface_definition',
          name,
          content,
          sourcePath: filePath,
          lineRange: { start: i + 1, end: endLine + 1 },
          language,
          confidence: this.calculateConfidence('interface_definition', content),
        }));
      }
    }

    return patterns;
  }

  /**
   * Extract type patterns (TypeScript)
   */
  private extractTypes(
    lines: string[],
    filePath: string,
    language: LocalPatternCandidate['language']
  ): LocalPatternCandidate[] {
    const patterns: LocalPatternCandidate[] = [];
    const typePattern = /^(?:export\s+)?type\s+(\w+)\s*=/;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i].trim();
      const match = line.match(typePattern);
      
      if (match) {
        const name = match[1];
        // Types can be single line or multiline
        let endLine = i;
        let content = line;
        
        // Check if multiline (ends with = but no semicolon)
        if (!line.endsWith(';')) {
          const result = this.extractBlock(lines, i, true);
          endLine = result.endLine;
          content = result.content;
        }
        
        patterns.push(this.createCandidate({
          type: 'type_definition',
          name,
          content,
          sourcePath: filePath,
          lineRange: { start: i + 1, end: endLine + 1 },
          language,
          confidence: this.calculateConfidence('type_definition', content),
        }));
      }
    }

    return patterns;
  }

  /**
   * Extract import patterns
   */
  private extractImports(
    lines: string[],
    filePath: string,
    language: LocalPatternCandidate['language']
  ): LocalPatternCandidate[] {
    const patterns: LocalPatternCandidate[] = [];
    const importPattern = /^import\s+(?:{[^}]+}|\*\s+as\s+\w+|\w+)\s+from\s+['"]([^'"]+)['"]/;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i].trim();
      const match = line.match(importPattern);
      
      if (match) {
        patterns.push(this.createCandidate({
          type: 'import_pattern',
          name: `import:${match[1]}`,
          content: line,
          sourcePath: filePath,
          lineRange: { start: i + 1, end: i + 1 },
          language,
          confidence: 0.5, // Lower confidence for imports
        }));
      }
    }

    return patterns;
  }

  /**
   * Extract export patterns
   */
  private extractExports(
    lines: string[],
    filePath: string,
    language: LocalPatternCandidate['language']
  ): LocalPatternCandidate[] {
    const patterns: LocalPatternCandidate[] = [];
    const exportPattern = /^export\s+(?:default\s+)?(?:{[^}]+}|(?:const|let|var|function|class|interface|type)\s+(\w+))/;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i].trim();
      const match = line.match(exportPattern);
      
      if (match && match[1]) {
        patterns.push(this.createCandidate({
          type: 'export_pattern',
          name: `export:${match[1]}`,
          content: line,
          sourcePath: filePath,
          lineRange: { start: i + 1, end: i + 1 },
          language,
          confidence: 0.5, // Lower confidence for exports
        }));
      }
    }

    return patterns;
  }

  /**
   * Extract a code block (braces-delimited)
   */
  private extractBlock(
    lines: string[],
    startLine: number,
    isType: boolean = false
  ): { endLine: number; content: string } {
    let braceCount = 0;
    let parenCount = 0;
    let endLine = startLine;
    const contentLines: string[] = [];

    for (let i = startLine; i < lines.length; i++) {
      const line = lines[i];
      contentLines.push(line);

      for (const char of line) {
        if (char === '{') braceCount++;
        else if (char === '}') braceCount--;
        else if (char === '(') parenCount++;
        else if (char === ')') parenCount--;
      }

      endLine = i;

      // For types, also check for semicolon
      if (isType && line.trim().endsWith(';')) {
        break;
      }

      // End when braces are balanced and we've seen at least one open brace
      if (braceCount === 0 && contentLines.length > 1) {
        break;
      }

      // Safety limit
      if (contentLines.length > 500) {
        break;
      }
    }

    return {
      endLine,
      content: contentLines.join('\n'),
    };
  }

  /**
   * Calculate confidence score for a pattern
   */
  private calculateConfidence(type: LocalPatternType, content: string): number {
    let confidence = 0.5; // Base confidence

    // Boost for well-documented code
    if (content.includes('/**') || content.includes('* @')) {
      confidence += 0.1;
    }

    // Boost for type annotations
    if (content.includes(': ') || content.includes('<') || content.includes('>')) {
      confidence += 0.1;
    }

    // Boost for error handling
    if (content.includes('try') || content.includes('catch') || content.includes('Result<')) {
      confidence += 0.1;
    }

    // Boost for tests
    if (content.includes('describe') || content.includes('it(') || content.includes('expect(')) {
      confidence += 0.1;
    }

    // Type-specific adjustments
    switch (type) {
      case 'repository_pattern':
      case 'service_pattern':
      case 'factory_pattern':
        confidence += 0.15; // Design patterns are valuable
        break;
      case 'value_object':
      case 'entity':
        confidence += 0.1; // DDD patterns
        break;
      case 'test_pattern':
        confidence += 0.05;
        break;
    }

    // Content length bonus (but not too long)
    const lineCount = content.split('\n').length;
    if (lineCount >= 5 && lineCount <= 50) {
      confidence += 0.05;
    }

    return Math.min(1.0, Math.max(0.0, confidence));
  }

  /**
   * Create a pattern candidate with computed signature
   */
  private createCandidate(
    params: Omit<LocalPatternCandidate, 'tempId' | 'signature' | 'extractedAt'>
  ): LocalPatternCandidate {
    return {
      ...params,
      tempId: `TEMP-${Date.now()}-${randomUUID().substring(0, 8)}`,
      signature: this.computeSignature(params.content, params.type),
      extractedAt: new Date(),
    };
  }

  /**
   * Compute a signature for similarity matching
   */
  private computeSignature(content: string, type: LocalPatternType): string {
    // Remove comments and whitespace for normalization
    const normalized = content
      .replace(/\/\*[\s\S]*?\*\//g, '') // Block comments
      .replace(/\/\/.*$/gm, '') // Line comments
      .replace(/\s+/g, ' ') // Normalize whitespace
      .trim();

    // Extract structural elements
    const tokens: string[] = [];
    
    // Extract keywords
    const keywords = normalized.match(/\b(function|class|interface|type|const|let|var|async|await|export|import|extends|implements|return|if|else|for|while|try|catch|throw)\b/g);
    if (keywords) {
      tokens.push(...keywords);
    }

    // Extract type annotations (simplified)
    const types = normalized.match(/:\s*(\w+(?:<[^>]+>)?)/g);
    if (types) {
      tokens.push(...types.map(t => t.replace(/:\s*/, 'T:')));
    }

    return `${type}:${tokens.join('|')}`;
  }
}

/**
 * Factory function to create a LocalWakePhase instance
 */
export function createLocalWakePhase(options?: Partial<WakeObserveOptions>): LocalWakePhase {
  return new LocalWakePhase(options);
}
