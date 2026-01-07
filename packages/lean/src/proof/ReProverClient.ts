/**
 * @fileoverview ReProver client for external proof search
 * @module @nahisaho/musubix-lean/proof
 * @traceability REQ-LEAN-REPROVER-001 to REQ-LEAN-REPROVER-003
 */

import type {
  ReProverConfig,
  ReProverSearchResult,
  ProofState,
  ProofFeedback,
  SearchNode,
} from '../types.js';
import { ReProverConnectionError } from '../errors.js';

/**
 * Default ReProver configuration
 */
const DEFAULT_CONFIG: ReProverConfig = {
  endpoint: 'http://localhost:8000/api/prove',
  timeout: 60000,
  maxDepth: 10,
};

/**
 * ReProver client for neural proof search
 * @traceability REQ-LEAN-REPROVER-001
 */
export class ReProverClient {
  private config: ReProverConfig;
  private connected: boolean = false;

  constructor(config: Partial<ReProverConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  /**
   * Connect to ReProver service
   * @traceability REQ-LEAN-REPROVER-001
   */
  async connect(config?: Partial<ReProverConfig>): Promise<void> {
    if (config) {
      this.config = { ...this.config, ...config };
    }

    try {
      // Health check
      const response = await this.healthCheck();
      if (response) {
        this.connected = true;
      } else {
        throw new Error('Health check failed');
      }
    } catch (error) {
      this.connected = false;
      throw new ReProverConnectionError(
        this.config.endpoint,
        error instanceof Error ? error.message : String(error)
      );
    }
  }

  /**
   * Check if connected to ReProver
   */
  isAvailable(): boolean {
    return this.connected;
  }

  /**
   * Perform health check on ReProver service
   */
  private async healthCheck(): Promise<boolean> {
    try {
      const controller = new AbortController();
      const timeoutId = setTimeout(() => controller.abort(), 5000);

      const healthEndpoint = this.config.endpoint.replace('/api/prove', '/health');
      const response = await fetch(healthEndpoint, {
        method: 'GET',
        signal: controller.signal,
      });

      clearTimeout(timeoutId);
      return response.ok;
    } catch {
      // If fetch fails, ReProver is not available
      return false;
    }
  }

  /**
   * Search for proof using ReProver
   * @traceability REQ-LEAN-REPROVER-002
   */
  async search(
    proofState: ProofState,
    options?: { maxDepth?: number; timeout?: number }
  ): Promise<ReProverSearchResult> {
    if (!this.connected) {
      return {
        found: false,
        proof: null,
        searchPath: [],
        suggestions: ['ReProver is not connected. Use basic proof tactics.'],
      };
    }

    const maxDepth = options?.maxDepth ?? this.config.maxDepth;
    const timeout = options?.timeout ?? this.config.timeout;

    try {
      const controller = new AbortController();
      const timeoutId = setTimeout(() => controller.abort(), timeout);

      const response = await fetch(this.config.endpoint, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          ...(this.config.apiKey && {
            Authorization: `Bearer ${this.config.apiKey}`,
          }),
        },
        body: JSON.stringify({
          proof_state: {
            goals: proofState.goals.map((g) => ({
              id: g.id,
              type: g.type,
              lean_code: g.leanCode,
            })),
            hypotheses: proofState.hypotheses.map((h) => ({
              name: h.name,
              type: h.type,
            })),
            current_goal: proofState.currentGoal,
          },
          max_depth: maxDepth,
        }),
        signal: controller.signal,
      });

      clearTimeout(timeoutId);

      if (!response.ok) {
        throw new Error(`ReProver request failed: ${response.status}`);
      }

      const result = await response.json();
      return this.parseSearchResult(result);
    } catch (error) {
      if (error instanceof Error && error.name === 'AbortError') {
        return {
          found: false,
          proof: null,
          searchPath: [],
          suggestions: [`Proof search timed out after ${timeout}ms`],
        };
      }

      return {
        found: false,
        proof: null,
        searchPath: [],
        suggestions: [
          `ReProver error: ${error instanceof Error ? error.message : String(error)}`,
        ],
      };
    }
  }

  /**
   * Parse ReProver response into SearchResult
   */
  private parseSearchResult(response: unknown): ReProverSearchResult {
    const data = response as Record<string, unknown>;

    if (data.found && data.proof) {
      return {
        found: true,
        proof: String(data.proof),
        searchPath: this.parseSearchPath(data.search_path),
        suggestions: [],
      };
    }

    return {
      found: false,
      proof: null,
      searchPath: this.parseSearchPath(data.search_path),
      suggestions: Array.isArray(data.suggestions)
        ? data.suggestions.map(String)
        : [],
    };
  }

  /**
   * Parse search path from response
   */
  private parseSearchPath(path: unknown): SearchNode[] {
    if (!Array.isArray(path)) {
      return [];
    }

    return path.map((node: unknown) => {
      const n = node as Record<string, unknown>;
      return {
        tactic: String(n.tactic || ''),
        state: {
          goals: [],
          hypotheses: [],
          currentGoal: 0,
        },
        score: Number(n.score || 0),
        children: [],
      };
    });
  }

  /**
   * Get feedback for failed proof attempt
   * @traceability REQ-LEAN-REPROVER-003
   */
  getFeedback(failedState: ProofState): ProofFeedback {
    const guidance: string[] = [];
    const suggestions: string[] = [];

    // Analyze the stuck state
    const currentGoal = failedState.goals[failedState.currentGoal];
    if (currentGoal) {
      const goalType = currentGoal.leanCode;

      // Provide guidance based on goal structure
      if (goalType.includes('∧')) {
        guidance.push('This is a conjunction. Try using "constructor" to split it.');
        suggestions.push('constructor');
      }

      if (goalType.includes('∨')) {
        guidance.push('This is a disjunction. Try "left" or "right" to choose a side.');
        suggestions.push('left', 'right');
      }

      if (goalType.includes('→')) {
        guidance.push('This is an implication. Use "intro h" to assume the antecedent.');
        suggestions.push('intro h');
      }

      if (goalType.includes('∀')) {
        guidance.push('This is a universal statement. Use "intro x" to introduce a variable.');
        suggestions.push('intro x');
      }

      if (goalType.includes('∃')) {
        guidance.push('This is an existential statement. Use "use value" to provide a witness.');
        suggestions.push('use _');
      }

      if (goalType.includes('¬')) {
        guidance.push('This is a negation. Use "intro h" and derive a contradiction.');
        suggestions.push('intro h');
      }

      if (goalType.includes('Nat') || goalType.includes('List')) {
        guidance.push('Consider using induction on the data structure.');
        suggestions.push('induction n', 'cases n');
      }
    }

    // Check hypotheses for applicable tactics
    if (failedState.hypotheses.length > 0) {
      guidance.push('You have hypotheses available. Try "assumption" or "exact h".');
      
      for (const hyp of failedState.hypotheses) {
        if (hyp.type === currentGoal?.type) {
          suggestions.push(`exact ${hyp.name}`);
        }
      }
    }

    if (guidance.length === 0) {
      guidance.push('Try simplification tactics: simp, simp_all, or decide.');
      suggestions.push('simp', 'decide');
    }

    return {
      stuckState: failedState,
      attemptedTactics: [],
      similarTheorems: [], // Would be populated from a theorem database
      guidance,
    };
  }

  /**
   * Disconnect from ReProver
   */
  disconnect(): void {
    this.connected = false;
  }

  /**
   * Get current configuration
   */
  getConfig(): ReProverConfig {
    return { ...this.config };
  }
}
