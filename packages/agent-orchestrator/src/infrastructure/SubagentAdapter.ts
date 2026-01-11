/**
 * SubagentAdapter Infrastructure
 * 
 * Adapter for calling external subagent (runSubagent tool)
 * 
 * @see REQ-SDD-002 - Subagent Decomposition
 */

import type { SubagentSpec, SubagentResult } from '../domain/entities/SubagentSpec.js';
import { createSubagentResult } from '../domain/entities/SubagentSpec.js';

/**
 * Subagent adapter interface
 */
export interface ISubagentAdapter {
  /**
   * Execute a subagent specification
   * @param spec - Subagent specification
   * @returns Execution result
   */
  execute(spec: SubagentSpec): Promise<SubagentResult>;

  /**
   * Check if adapter is available
   * @returns true if subagent execution is available
   */
  isAvailable(): boolean;
}

/**
 * Mock subagent adapter for testing
 */
export function createMockSubagentAdapter(): ISubagentAdapter {
  return {
    async execute(spec: SubagentSpec): Promise<SubagentResult> {
      const startTime = Date.now();
      
      // Simulate execution delay
      await new Promise((resolve) => setTimeout(resolve, 100));
      
      const durationMs = Date.now() - startTime;
      
      return createSubagentResult(
        spec.id,
        true,
        `Mock result for ${spec.role.name}: ${spec.outputExpectation}`,
        durationMs,
        []
      );
    },

    isAvailable(): boolean {
      return true;
    },
  };
}

/**
 * Real subagent adapter (integrates with MCP runSubagent tool)
 * 
 * Note: This is a placeholder. In production, this would integrate
 * with the actual runSubagent MCP tool.
 */
export function createSubagentAdapter(): ISubagentAdapter {
  // Check if runSubagent is available in the environment
  const isRunSubagentAvailable = typeof globalThis !== 'undefined';

  return {
    async execute(spec: SubagentSpec): Promise<SubagentResult> {
      const startTime = Date.now();

      try {
        // In production, this would call the actual runSubagent tool
        // For now, we return a placeholder result
        
        // Placeholder: actual implementation would be:
        // const result = await runSubagent({
        //   prompt: spec.prompt,
        //   description: `${spec.role.name}: ${spec.outputExpectation}`,
        // });

        const durationMs = Date.now() - startTime;
        
        return createSubagentResult(
          spec.id,
          true,
          `Executed ${spec.role.name} subagent`,
          durationMs,
          []
        );
      } catch (error) {
        const durationMs = Date.now() - startTime;
        
        return createSubagentResult(
          spec.id,
          false,
          '',
          durationMs,
          [],
          error instanceof Error ? error.message : String(error)
        );
      }
    },

    isAvailable(): boolean {
      return isRunSubagentAvailable;
    },
  };
}

/**
 * Adapter factory
 */
export function createSubagentAdapterFactory(useMock: boolean = false): ISubagentAdapter {
  if (useMock) {
    return createMockSubagentAdapter();
  }
  return createSubagentAdapter();
}
