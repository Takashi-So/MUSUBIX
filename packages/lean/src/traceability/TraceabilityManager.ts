/**
 * @fileoverview Traceability manager for requirement-to-proof mapping
 * @module @nahisaho/musubix-lean/traceability
 * @traceability REQ-LEAN-TRACE-001 to REQ-LEAN-TRACE-003
 */

import type {
  TraceabilityLink,
  TraceabilityArtifact,
  LeanTheorem,
  LeanProof,
  VerificationResult,
} from '../types.js';

/**
 * Traceability link type
 */
export type LinkType =
  | 'requirement_to_theorem'
  | 'theorem_to_proof'
  | 'theorem_to_code'
  | 'requirement_to_code'
  | 'proof_to_verification';

/**
 * Traceability coverage metrics
 */
export interface TraceabilityCoverage {
  totalRequirements: number;
  coveredRequirements: number;
  coveragePercentage: number;
  untraced: string[];
  partiallyTraced: string[];
  fullyTraced: string[];
}

/**
 * Manages requirement-to-proof traceability
 * @traceability REQ-LEAN-TRACE-001
 */
export class TraceabilityManager {
  private links: Map<string, TraceabilityLink> = new Map();
  private artifacts: Map<string, TraceabilityArtifact> = new Map();
  private linkCounter = 0;

  /**
   * Register an artifact (requirement, theorem, proof, code)
   */
  registerArtifact(artifact: Omit<TraceabilityArtifact, 'id'> & { artifactId?: string }): TraceabilityArtifact {
    const id = artifact.artifactId || this.generateArtifactId(artifact.type);
    const fullArtifact: TraceabilityArtifact = {
      id,
      type: artifact.type,
      content: artifact.content,
      name: artifact.name,
      version: artifact.version,
      metadata: artifact.metadata,
    };
    this.artifacts.set(id, fullArtifact);
    return fullArtifact;
  }

  /**
   * Create a traceability link between artifacts
   * @traceability REQ-LEAN-TRACE-002
   */
  createLink(
    sourceId: string,
    targetId: string,
    type: LinkType,
    confidence: number = 1.0,
    metadata?: Record<string, unknown>
  ): TraceabilityLink {
    const id = this.generateLinkId();
    const link: TraceabilityLink = {
      id,
      source: sourceId,
      target: targetId,
      type,
      confidence,
      metadata: metadata || {},
      createdAt: new Date().toISOString(),
    };

    this.links.set(id, link);
    return link;
  }

  /**
   * Link a theorem to its requirement
   */
  linkTheoremToRequirement(theorem: LeanTheorem): TraceabilityLink {
    // Register theorem as artifact
    this.registerArtifact({
      type: 'theorem',
      artifactId: theorem.id,
      name: theorem.name,
      content: theorem.statement,
      metadata: {
        name: theorem.name,
        description: theorem.description,
      },
    });

    return this.createLink(theorem.requirementId, theorem.id, 'requirement_to_theorem', 1.0, {
      theoremName: theorem.name,
    });
  }

  /**
   * Link a proof to its theorem
   */
  linkProofToTheorem(proof: LeanProof, theorem: LeanTheorem): TraceabilityLink {
    // Register proof as artifact
    this.registerArtifact({
      type: 'proof',
      artifactId: proof.id,
      name: `proof-${theorem.name}`,
      content: proof.leanCode,
      metadata: {
        theoremId: proof.theoremId,
        tactics: proof.tactics,
        isComplete: proof.isComplete,
      },
    });

    return this.createLink(theorem.id, proof.id, 'theorem_to_proof', proof.isComplete ? 1.0 : 0.5, {
      isComplete: proof.isComplete,
    });
  }

  /**
   * Record verification result in traceability
   */
  recordVerification(result: VerificationResult): TraceabilityLink | null {
    if (!result.proof) return null;

    return this.createLink(result.proof.id, result.theoremId, 'proof_to_verification', 1.0, {
      status: result.status,
      duration: result.duration,
      errors: result.errors,
    });
  }

  /**
   * Get all links for a source artifact
   */
  getLinksFromSource(sourceId: string): TraceabilityLink[] {
    return Array.from(this.links.values()).filter((link) => link.source === sourceId);
  }

  /**
   * Get all links targeting an artifact
   */
  getLinksToTarget(targetId: string): TraceabilityLink[] {
    return Array.from(this.links.values()).filter((link) => link.target === targetId);
  }

  /**
   * Get all links of a specific type
   */
  getLinksByType(type: LinkType): TraceabilityLink[] {
    return Array.from(this.links.values()).filter((link) => link.type === type);
  }

  /**
   * Calculate traceability coverage
   * @traceability REQ-LEAN-TRACE-003
   */
  calculateCoverage(requirementIds: string[]): TraceabilityCoverage {
    const untraced: string[] = [];
    const partiallyTraced: string[] = [];
    const fullyTraced: string[] = [];

    for (const reqId of requirementIds) {
      const theoremLinks = this.getLinksFromSource(reqId).filter(
        (l) => l.type === 'requirement_to_theorem'
      );

      if (theoremLinks.length === 0) {
        untraced.push(reqId);
        continue;
      }

      // Check if all linked theorems have proofs
      let allProved = true;
      let anyProved = false;

      for (const link of theoremLinks) {
        const proofLinks = this.getLinksFromSource(link.target).filter(
          (l) => l.type === 'theorem_to_proof'
        );

        if (proofLinks.length > 0) {
          const hasCompleteProof = proofLinks.some(
            (pl) => (pl.metadata as Record<string, unknown>)?.isComplete === true
          );
          if (hasCompleteProof) {
            anyProved = true;
          } else {
            allProved = false;
          }
        } else {
          allProved = false;
        }
      }

      if (allProved && anyProved) {
        fullyTraced.push(reqId);
      } else if (anyProved) {
        partiallyTraced.push(reqId);
      } else {
        untraced.push(reqId);
      }
    }

    const coveredCount = fullyTraced.length + partiallyTraced.length;
    const totalCount = requirementIds.length;

    return {
      totalRequirements: totalCount,
      coveredRequirements: coveredCount,
      coveragePercentage: totalCount > 0 ? (coveredCount / totalCount) * 100 : 0,
      untraced,
      partiallyTraced,
      fullyTraced,
    };
  }

  /**
   * Get full traceability chain for a requirement
   */
  getTraceChain(requirementId: string): TraceabilityArtifact[] {
    const chain: TraceabilityArtifact[] = [];
    const visited = new Set<string>();

    const traverse = (artifactId: string): void => {
      if (visited.has(artifactId)) return;
      visited.add(artifactId);

      const artifact = this.artifacts.get(artifactId);
      if (artifact) {
        chain.push(artifact);
      }

      // Follow outgoing links
      const outLinks = this.getLinksFromSource(artifactId);
      for (const link of outLinks) {
        traverse(link.target);
      }
    };

    traverse(requirementId);
    return chain;
  }

  /**
   * Validate traceability integrity
   */
  validateIntegrity(): { valid: boolean; errors: string[] } {
    const errors: string[] = [];

    for (const [linkId, link] of this.links) {
      // Check source exists
      if (!this.artifacts.has(link.source)) {
        errors.push(`Link ${linkId}: source artifact "${link.source}" not found`);
      }

      // Check target exists
      if (!this.artifacts.has(link.target)) {
        errors.push(`Link ${linkId}: target artifact "${link.target}" not found`);
      }

      // Check confidence is valid
      if (link.confidence < 0 || link.confidence > 1) {
        errors.push(`Link ${linkId}: invalid confidence ${link.confidence}`);
      }
    }

    return {
      valid: errors.length === 0,
      errors,
    };
  }

  /**
   * Export traceability matrix
   */
  exportMatrix(): Record<string, Record<string, string>> {
    const matrix: Record<string, Record<string, string>> = {};

    // Group links by source
    for (const link of this.links.values()) {
      if (!matrix[link.source]) {
        matrix[link.source] = {};
      }
      matrix[link.source][link.target] = `${link.type} (${(link.confidence * 100).toFixed(0)}%)`;
    }

    return matrix;
  }

  /**
   * Export to Markdown format
   */
  exportMarkdown(): string {
    const lines: string[] = [];

    lines.push('# Traceability Matrix');
    lines.push('');

    // Coverage summary
    const reqLinks = this.getLinksByType('requirement_to_theorem');
    const requirements = [...new Set(reqLinks.map((l) => l.source))];
    const coverage = this.calculateCoverage(requirements);

    lines.push('## Coverage Summary');
    lines.push('');
    lines.push(`- **Total Requirements**: ${coverage.totalRequirements}`);
    lines.push(`- **Covered Requirements**: ${coverage.coveredRequirements}`);
    lines.push(`- **Coverage**: ${coverage.coveragePercentage.toFixed(1)}%`);
    lines.push('');

    // Links table
    lines.push('## Traceability Links');
    lines.push('');
    lines.push('| Source | Target | Type | Confidence |');
    lines.push('|--------|--------|------|------------|');

    for (const link of this.links.values()) {
      lines.push(
        `| ${link.source} | ${link.target} | ${link.type} | ${(link.confidence * 100).toFixed(0)}% |`
      );
    }

    lines.push('');

    // Untraced requirements
    if (coverage.untraced.length > 0) {
      lines.push('## ⚠️ Untraced Requirements');
      lines.push('');
      for (const req of coverage.untraced) {
        lines.push(`- ${req}`);
      }
      lines.push('');
    }

    return lines.join('\n');
  }

  /**
   * Clear all data
   */
  clear(): void {
    this.links.clear();
    this.artifacts.clear();
    this.linkCounter = 0;
  }

  /**
   * Get statistics
   */
  getStats(): { artifacts: number; links: number; byType: Record<string, number> } {
    const byType: Record<string, number> = {};
    for (const link of this.links.values()) {
      byType[link.type] = (byType[link.type] || 0) + 1;
    }

    return {
      artifacts: this.artifacts.size,
      links: this.links.size,
      byType,
    };
  }

  private generateLinkId(): string {
    this.linkCounter++;
    return `LINK-${this.linkCounter.toString().padStart(4, '0')}`;
  }

  private generateArtifactId(type: string): string {
    const timestamp = Date.now().toString(36);
    return `${type.toUpperCase()}-${timestamp}`;
  }
}
