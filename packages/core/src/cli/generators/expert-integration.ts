/**
 * Expert Delegation Integration for Scaffold
 *
 * Integrates AI expert delegation with scaffold generation
 *
 * @packageDocumentation
 * @module cli/generators/expert-integration
 *
 * @traceability REQ-EXD-001, REQ-EXD-002
 * @see DES-EXD-001 - Expert Delegation Integration Design
 * @see ADR-v3.3.0-002 - Expert Timeout Handling
 */

import type { GeneratedFile } from './value-object-generator.js';
import type { ExtractedPattern } from './pattern-extractor.js';

/**
 * Expert consultation request
 */
export interface ExpertConsultationRequest {
  /** Expert type to consult */
  expertType: 'architect' | 'code-reviewer' | 'security-analyst';

  /** Content to analyze */
  content: string;

  /** Context information */
  context: {
    domain: string;
    projectName: string;
    generatedFiles: string[];
  };

  /** Timeout in milliseconds (ADR-v3.3.0-002) */
  timeout?: number;
}

/**
 * Expert consultation result
 */
export interface ExpertConsultationResult {
  /** Whether consultation succeeded */
  success: boolean;

  /** Expert recommendations */
  recommendations: ExpertRecommendation[];

  /** Expert analysis */
  analysis?: string;

  /** Patterns suggested */
  suggestedPatterns?: ExtractedPattern[];

  /** Execution time in ms */
  executionTime: number;

  /** Whether timeout occurred */
  timedOut: boolean;

  /** Error message if failed */
  error?: string;
}

/**
 * Expert recommendation
 */
export interface ExpertRecommendation {
  /** Recommendation type */
  type: 'improvement' | 'warning' | 'pattern' | 'best-practice';

  /** Priority (1=highest) */
  priority: 1 | 2 | 3;

  /** Recommendation message */
  message: string;

  /** Related file path */
  relatedFile?: string;

  /** Suggested code change */
  suggestedChange?: string;
}

/**
 * Expert integration configuration
 */
export interface ExpertIntegrationConfig {
  /** Enable expert consultation */
  enabled: boolean;

  /** Default timeout in ms (ADR-v3.3.0-002: 30000ms) */
  defaultTimeout: number;

  /** Enable fallback on timeout */
  fallbackOnTimeout: boolean;

  /** Cache expert results */
  cacheResults: boolean;
}

/**
 * Default configuration (ADR-v3.3.0-002)
 */
export const DEFAULT_EXPERT_CONFIG: ExpertIntegrationConfig = {
  enabled: true,
  defaultTimeout: 30000, // 30 seconds per ADR-v3.3.0-002
  fallbackOnTimeout: true,
  cacheResults: true,
};

/**
 * Expert Integration for Scaffold
 *
 * Provides AI expert consultation for generated code
 */
export class ExpertIntegration {
  private resultCache = new Map<string, ExpertConsultationResult>();

  constructor(private config: ExpertIntegrationConfig = DEFAULT_EXPERT_CONFIG) {}

  /**
   * Consult expert for generated files
   *
   * @param request - Consultation request
   * @returns Consultation result
   */
  async consultExpert(request: ExpertConsultationRequest): Promise<ExpertConsultationResult> {
    if (!this.config.enabled) {
      return this.createDisabledResult();
    }

    const cacheKey = this.createCacheKey(request);
    if (this.config.cacheResults && this.resultCache.has(cacheKey)) {
      return this.resultCache.get(cacheKey)!;
    }

    const startTime = Date.now();
    const timeout = request.timeout ?? this.config.defaultTimeout;

    try {
      // Check if expert-delegation is available
      const expertAvailable = await this.checkExpertAvailability();

      if (!expertAvailable) {
        return this.createFallbackResult(startTime, 'Expert delegation not available');
      }

      // Execute expert consultation with timeout (ADR-v3.3.0-002)
      const result = await this.executeWithTimeout(
        () => this.performConsultation(request),
        timeout
      );

      if (this.config.cacheResults) {
        this.resultCache.set(cacheKey, result);
      }

      return result;
    } catch (error) {
      const executionTime = Date.now() - startTime;

      if (this.isTimeoutError(error)) {
        // ADR-v3.3.0-002: Fallback on timeout
        if (this.config.fallbackOnTimeout) {
          return this.createFallbackResult(executionTime, 'Expert consultation timed out', true);
        }
      }

      return {
        success: false,
        recommendations: [],
        executionTime,
        timedOut: this.isTimeoutError(error),
        error: (error as Error).message,
      };
    }
  }

  /**
   * Generate recommendations for scaffold output
   */
  async generateRecommendations(
    files: GeneratedFile[],
    domain: string,
    projectName: string
  ): Promise<ExpertRecommendation[]> {
    if (!this.config.enabled || files.length === 0) {
      return [];
    }

    const allRecommendations: ExpertRecommendation[] = [];

    // Consult architect for structure
    const architectResult = await this.consultExpert({
      expertType: 'architect',
      content: this.summarizeFiles(files),
      context: {
        domain,
        projectName,
        generatedFiles: files.map((f) => f.path),
      },
    });

    if (architectResult.success) {
      allRecommendations.push(...architectResult.recommendations);
    }

    // Consult code-reviewer for quality
    const reviewerResult = await this.consultExpert({
      expertType: 'code-reviewer',
      content: files.map((f) => f.content).join('\n\n'),
      context: {
        domain,
        projectName,
        generatedFiles: files.map((f) => f.path),
      },
    });

    if (reviewerResult.success) {
      allRecommendations.push(...reviewerResult.recommendations);
    }

    // Sort by priority
    return allRecommendations.sort((a, b) => a.priority - b.priority);
  }

  /**
   * Check if expert delegation is available
   */
  private async checkExpertAvailability(): Promise<boolean> {
    try {
      // Try to dynamically import expert-delegation
      // This will fail gracefully if the package is not available
      // @ts-expect-error - Optional dependency, may not be installed
      const expertModule = await import('@nahisaho/musubix-expert-delegation').catch(() => null);
      return expertModule !== null;
    } catch {
      return false;
    }
  }

  /**
   * Perform actual expert consultation
   */
  private async performConsultation(
    request: ExpertConsultationRequest
  ): Promise<ExpertConsultationResult> {
    const startTime = Date.now();

    try {
      // Dynamic import to avoid hard dependency
      // @ts-expect-error - Optional dependency, may not be installed
      const { createDelegationEngine } = await import('@nahisaho/musubix-expert-delegation');

      const engine = createDelegationEngine({
        mode: 'advisory',
        enableTracing: true,
      });

      const task = {
        type: request.expertType,
        content: request.content,
        context: request.context,
      };

      const result = await engine.execute(task);

      return {
        success: true,
        recommendations: this.parseRecommendations(result.output),
        analysis: result.output,
        executionTime: Date.now() - startTime,
        timedOut: false,
      };
    } catch (error) {
      return {
        success: false,
        recommendations: [],
        executionTime: Date.now() - startTime,
        timedOut: false,
        error: (error as Error).message,
      };
    }
  }

  /**
   * Execute with timeout (ADR-v3.3.0-002)
   */
  private async executeWithTimeout<T>(
    fn: () => Promise<T>,
    timeoutMs: number
  ): Promise<T> {
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        reject(new TimeoutError(`Operation timed out after ${timeoutMs}ms`));
      }, timeoutMs);

      fn()
        .then((result) => {
          clearTimeout(timer);
          resolve(result);
        })
        .catch((error) => {
          clearTimeout(timer);
          reject(error);
        });
    });
  }

  /**
   * Parse recommendations from expert output
   */
  private parseRecommendations(output: string): ExpertRecommendation[] {
    const recommendations: ExpertRecommendation[] = [];

    // Simple parsing - look for recommendation patterns
    const lines = output.split('\n');
    for (const line of lines) {
      if (line.includes('recommend') || line.includes('suggest')) {
        recommendations.push({
          type: 'improvement',
          priority: 2,
          message: line.trim(),
        });
      }
      if (line.includes('warning') || line.includes('caution')) {
        recommendations.push({
          type: 'warning',
          priority: 1,
          message: line.trim(),
        });
      }
      if (line.includes('pattern') || line.includes('best practice')) {
        recommendations.push({
          type: 'best-practice',
          priority: 3,
          message: line.trim(),
        });
      }
    }

    return recommendations;
  }

  /**
   * Create cache key
   */
  private createCacheKey(request: ExpertConsultationRequest): string {
    return `${request.expertType}:${request.context.domain}:${request.content.substring(0, 100)}`;
  }

  /**
   * Create disabled result
   */
  private createDisabledResult(): ExpertConsultationResult {
    return {
      success: true,
      recommendations: [],
      executionTime: 0,
      timedOut: false,
    };
  }

  /**
   * Create fallback result (ADR-v3.3.0-002)
   */
  private createFallbackResult(
    executionTime: number,
    reason: string,
    timedOut = false
  ): ExpertConsultationResult {
    return {
      success: true, // Still success - just without expert input
      recommendations: [
        {
          type: 'warning',
          priority: 3,
          message: `Expert consultation unavailable: ${reason}. Generated code follows default patterns.`,
        },
      ],
      executionTime,
      timedOut,
    };
  }

  /**
   * Check if error is timeout
   */
  private isTimeoutError(error: unknown): boolean {
    return error instanceof TimeoutError;
  }

  /**
   * Summarize files for expert analysis
   */
  private summarizeFiles(files: GeneratedFile[]): string {
    const summary: string[] = [];

    for (const file of files) {
      const lines = file.content.split('\n').length;
      summary.push(`- ${file.path} (${lines} lines, type: ${file.type})`);
    }

    return `Generated files:\n${summary.join('\n')}`;
  }

  /**
   * Clear result cache
   */
  clearCache(): void {
    this.resultCache.clear();
  }
}

/**
 * Timeout error class
 */
class TimeoutError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'TimeoutError';
  }
}

/**
 * Create expert integration instance
 */
export function createExpertIntegration(
  config?: Partial<ExpertIntegrationConfig>
): ExpertIntegration {
  return new ExpertIntegration({
    ...DEFAULT_EXPERT_CONFIG,
    ...config,
  });
}
