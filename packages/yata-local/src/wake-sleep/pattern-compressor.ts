/**
 * @fileoverview Pattern Compressor Implementation for YATA Local
 * @module @nahisaho/yata-local/wake-sleep
 * @version 0.1.0
 * @license MIT
 * 
 * Trace: REQ-WSL-003, TSK-WSL-003
 */

import { randomUUID } from 'crypto';
import type {
  LocalPatternCluster,
  LocalConsolidatedPattern,
  LocalPatternType,
  CompressOptions,
} from './types.js';

/**
 * Pattern Compressor - Abstraction and Compression
 * 
 * Responsible for:
 * - Creating abstract templates from pattern clusters
 * - Compressing patterns for efficient storage
 * - Managing pattern metadata
 */
export class LocalPatternCompressor {
  private readonly options: Required<CompressOptions>;

  constructor(options: Partial<CompressOptions> = {}) {
    this.options = {
      level: options.level ?? 5,
      preserveNames: options.preserveNames ?? false,
      includeTypes: options.includeTypes ?? true,
    };
  }

  /**
   * Compress a cluster into a consolidated pattern
   */
  compress(cluster: LocalPatternCluster): LocalConsolidatedPattern {
    const representative = cluster.representative;
    const template = this.createTemplate(cluster);
    const compressed = this.compressTemplate(template);

    return {
      id: this.generatePatternId(representative.type),
      name: this.generatePatternName(cluster),
      type: representative.type,
      template,
      compressed,
      confidence: this.calculateAverageConfidence(cluster),
      sourceCount: cluster.patterns.length,
      usageCount: 0,
      createdAt: new Date(),
      lastUsedAt: null,
      sources: [...new Set(cluster.patterns.map(p => p.sourcePath))],
    };
  }

  /**
   * Compress multiple clusters
   */
  compressAll(clusters: LocalPatternCluster[]): LocalConsolidatedPattern[] {
    return clusters.map(cluster => this.compress(cluster));
  }

  /**
   * Create an abstract template from a cluster
   */
  private createTemplate(cluster: LocalPatternCluster): string {
    const representative = cluster.representative;
    let template = representative.content;

    // Normalize whitespace
    template = this.normalizeWhitespace(template);

    // Replace specific identifiers with placeholders
    if (!this.options.preserveNames) {
      template = this.replaceIdentifiers(template, representative.type);
    }

    // Optionally remove type annotations
    if (!this.options.includeTypes) {
      template = this.removeTypeAnnotations(template);
    }

    // Remove implementation details based on compression level
    template = this.simplifyImplementation(template, this.options.level);

    return template;
  }

  /**
   * Compress the template for storage
   */
  private compressTemplate(template: string): string {
    // For now, just minify
    return template
      .replace(/\/\*[\s\S]*?\*\//g, '') // Remove block comments
      .replace(/\/\/.*$/gm, '') // Remove line comments
      .replace(/\s+/g, ' ') // Collapse whitespace
      .trim();
  }

  /**
   * Normalize whitespace
   */
  private normalizeWhitespace(code: string): string {
    const lines = code.split('\n');
    
    // Find minimum indentation
    let minIndent = Infinity;
    for (const line of lines) {
      if (line.trim().length === 0) continue;
      const indent = line.match(/^(\s*)/)?.[1].length ?? 0;
      minIndent = Math.min(minIndent, indent);
    }

    // Remove minimum indentation
    if (minIndent > 0 && minIndent !== Infinity) {
      return lines
        .map(line => line.slice(minIndent))
        .join('\n');
    }

    return code;
  }

  /**
   * Replace specific identifiers with generic placeholders
   */
  private replaceIdentifiers(code: string, type: LocalPatternType): string {
    let result = code;

    // Map of identifier patterns based on type
    const replacements: Array<{ pattern: RegExp; replacement: string }> = [];

    switch (type) {
      case 'function_signature':
        // Replace function names (but not keywords)
        replacements.push({
          pattern: /\bfunction\s+(\w+)/g,
          replacement: 'function $FUNC_NAME',
        });
        replacements.push({
          pattern: /\bconst\s+(\w+)\s*=/g,
          replacement: 'const $FUNC_NAME =',
        });
        break;

      case 'class_structure':
      case 'repository_pattern':
      case 'service_pattern':
      case 'factory_pattern':
        // Replace class names
        replacements.push({
          pattern: /\bclass\s+(\w+)/g,
          replacement: 'class $CLASS_NAME',
        });
        break;

      case 'interface_definition':
        // Replace interface names
        replacements.push({
          pattern: /\binterface\s+(\w+)/g,
          replacement: 'interface $INTERFACE_NAME',
        });
        break;

      case 'type_definition':
        // Replace type names
        replacements.push({
          pattern: /\btype\s+(\w+)/g,
          replacement: 'type $TYPE_NAME',
        });
        break;

      case 'value_object':
      case 'entity':
        // Replace both class and interface names
        replacements.push({
          pattern: /\bclass\s+(\w+)/g,
          replacement: 'class $ENTITY_NAME',
        });
        replacements.push({
          pattern: /\binterface\s+(\w+)/g,
          replacement: 'interface $ENTITY_NAME',
        });
        break;
    }

    // Apply replacements
    for (const { pattern, replacement } of replacements) {
      result = result.replace(pattern, replacement);
    }

    return result;
  }

  /**
   * Remove type annotations
   */
  private removeTypeAnnotations(code: string): string {
    return code
      // Remove return type annotations
      .replace(/\):\s*[A-Za-z<>\[\]\|&,\s]+\s*{/g, ') {')
      // Remove parameter type annotations (simplified)
      .replace(/(\w+):\s*[A-Za-z<>\[\]\|&]+/g, '$1');
  }

  /**
   * Simplify implementation based on compression level
   */
  private simplifyImplementation(code: string, level: number): string {
    if (level <= 3) {
      // Keep full implementation
      return code;
    }

    if (level <= 6) {
      // Replace implementation bodies with placeholders
      return this.replaceMethodBodies(code);
    }

    // High compression: keep only signature
    return this.extractSignatureOnly(code);
  }

  /**
   * Replace method bodies with placeholders
   */
  private replaceMethodBodies(code: string): string {
    const lines = code.split('\n');
    const result: string[] = [];
    let braceDepth = 0;
    let inBody = false;
    let bodyStartDepth = 0;

    for (const line of lines) {
      // Count braces
      for (const char of line) {
        if (char === '{') {
          if (!inBody && braceDepth > 0) {
            inBody = true;
            bodyStartDepth = braceDepth;
          }
          braceDepth++;
        } else if (char === '}') {
          braceDepth--;
          if (inBody && braceDepth <= bodyStartDepth) {
            inBody = false;
            result.push('  // ... implementation');
          }
        }
      }

      if (!inBody || braceDepth === bodyStartDepth + 1) {
        result.push(line);
      }
    }

    return result.join('\n');
  }

  /**
   * Extract only the signature
   */
  private extractSignatureOnly(code: string): string {
    const lines = code.split('\n');
    const result: string[] = [];
    let braceDepth = 0;
    let foundFirstBrace = false;

    for (const line of lines) {
      for (const char of line) {
        if (char === '{') {
          braceDepth++;
          foundFirstBrace = true;
        } else if (char === '}') {
          braceDepth--;
        }
      }

      // Keep lines until first opening brace
      if (!foundFirstBrace) {
        result.push(line);
      } else if (braceDepth === 0) {
        // Add closing brace
        result.push('}');
        break;
      } else if (braceDepth === 1 && line.includes('{')) {
        // First line with opening brace
        result.push(line.substring(0, line.indexOf('{') + 1));
        result.push('  // ... implementation');
      }
    }

    return result.join('\n');
  }

  /**
   * Generate a pattern ID
   */
  private generatePatternId(type: LocalPatternType): string {
    const prefix = this.getTypePrefix(type);
    const timestamp = new Date().toISOString().slice(0, 10).replace(/-/g, '');
    const suffix = randomUUID().substring(0, 4).toUpperCase();
    return `PAT-${prefix}-${timestamp}-${suffix}`;
  }

  /**
   * Get type prefix for ID generation
   */
  private getTypePrefix(type: LocalPatternType): string {
    const prefixMap: Record<LocalPatternType, string> = {
      function_signature: 'FN',
      class_structure: 'CLS',
      interface_definition: 'ITF',
      type_definition: 'TYP',
      import_pattern: 'IMP',
      export_pattern: 'EXP',
      error_handling: 'ERR',
      async_pattern: 'ASY',
      factory_pattern: 'FAC',
      repository_pattern: 'REP',
      service_pattern: 'SVC',
      value_object: 'VO',
      entity: 'ENT',
      aggregate: 'AGG',
      event_handler: 'EVT',
      middleware: 'MID',
      decorator: 'DEC',
      hook: 'HK',
      test_pattern: 'TST',
      other: 'OTH',
    };
    return prefixMap[type] ?? 'OTH';
  }

  /**
   * Generate a pattern name from cluster
   */
  private generatePatternName(cluster: LocalPatternCluster): string {
    const rep = cluster.representative;
    
    // Extract the name from the content if possible
    const nameMatch = rep.content.match(
      /(?:function|class|interface|type|const)\s+(\w+)/
    );

    if (nameMatch) {
      return `${this.formatTypeName(rep.type)}: ${nameMatch[1]}`;
    }

    return `${this.formatTypeName(rep.type)}: ${rep.name}`;
  }

  /**
   * Format type name for display
   */
  private formatTypeName(type: LocalPatternType): string {
    return type
      .split('_')
      .map(word => word.charAt(0).toUpperCase() + word.slice(1))
      .join(' ');
  }

  /**
   * Calculate average confidence from cluster
   */
  private calculateAverageConfidence(cluster: LocalPatternCluster): number {
    const sum = cluster.patterns.reduce((acc, p) => acc + p.confidence, 0);
    return sum / cluster.patterns.length;
  }
}

/**
 * Factory function to create a LocalPatternCompressor instance
 */
export function createLocalPatternCompressor(
  options?: Partial<CompressOptions>
): LocalPatternCompressor {
  return new LocalPatternCompressor(options);
}
