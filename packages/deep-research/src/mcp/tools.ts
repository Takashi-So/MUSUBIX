/**
 * @fileoverview MCP Tools for Deep Research
 * @module @nahisaho/musubix-deep-research/mcp
 * @version 1.0.0
 * 
 * REQ: REQ-DR-INT-006 (MCP Integration)
 * TSK: TSK-DR-020 (MCP Tools Integration)
 */

/**
 * MCP Tool: deep_research_start
 * 
 * Start a deep research session on a technical topic.
 * Returns research ID for tracking progress.
 */
export interface DeepResearchStartTool {
  name: 'deep_research_start';
  description: 'Start iterative deep research on a technical topic using search-read-reason cycle';
  inputSchema: {
    type: 'object';
    properties: {
      query: {
        type: 'string';
        description: 'Research question or topic';
      };
      maxIterations: {
        type: 'number';
        description: 'Maximum research iterations (default: 5)';
        minimum: 1;
        maximum: 20;
      };
      tokenBudget: {
        type: 'number';
        description: 'Token budget limit (default: 10000)';
        minimum: 1000;
        maximum: 100000;
      };
      provider: {
        type: 'string';
        enum: ['jina', 'brave', 'duckduckgo'];
        description: 'Search provider (default: jina)';
      };
    };
    required: ['query'];
  };
}

/**
 * MCP Tool: deep_research_status
 * 
 * Get current status of a research session.
 */
export interface DeepResearchStatusTool {
  name: 'deep_research_status';
  description: 'Get current status and progress of a deep research session';
  inputSchema: {
    type: 'object';
    properties: {
      researchId: {
        type: 'string';
        description: 'Research session ID';
      };
    };
    required: ['researchId'];
  };
}

/**
 * MCP Tool: deep_research_report
 * 
 * Get final research report (markdown or JSON).
 */
export interface DeepResearchReportTool {
  name: 'deep_research_report';
  description: 'Get final report from completed deep research session';
  inputSchema: {
    type: 'object';
    properties: {
      researchId: {
        type: 'string';
        description: 'Research session ID';
      };
      format: {
        type: 'string';
        enum: ['markdown', 'json'];
        description: 'Report format (default: markdown)';
      };
    };
    required: ['researchId'];
  };
}

/**
 * Research session state
 */
export interface ResearchSession {
  id: string;
  query: string;
  status: 'running' | 'completed' | 'failed';
  currentIteration: number;
  maxIterations: number;
  tokensUsed: number;
  tokenBudget: number;
  knowledgeCount: number;
  startTime: number;
  endTime?: number;
  error?: string;
  result?: any;
}

/**
 * MCP Tool Handler for Deep Research
 */
export class DeepResearchMCPHandler {
  private sessions: Map<string, ResearchSession> = new Map();
  private sessionCounter = 0;

  /**
   * Handle deep_research_start tool call
   */
  async handleStart(input: {
    query: string;
    maxIterations?: number;
    tokenBudget?: number;
    provider?: string;
  }): Promise<{ researchId: string; status: string }> {
    const sessionId = `research-${++this.sessionCounter}-${Date.now()}`;

    // Create session
    const session: ResearchSession = {
      id: sessionId,
      query: input.query,
      status: 'running',
      currentIteration: 0,
      maxIterations: input.maxIterations ?? 5,
      tokensUsed: 0,
      tokenBudget: input.tokenBudget ?? 10000,
      knowledgeCount: 0,
      startTime: Date.now(),
    };

    this.sessions.set(sessionId, session);

    // Start research asynchronously
    this.executeResearch(sessionId, input).catch((error) => {
      const sess = this.sessions.get(sessionId);
      if (sess) {
        sess.status = 'failed';
        sess.error = error.message;
        sess.endTime = Date.now();
      }
    });

    return {
      researchId: sessionId,
      status: 'Research started. Use deep_research_status to check progress.',
    };
  }

  /**
   * Handle deep_research_status tool call
   */
  async handleStatus(input: { researchId: string }): Promise<ResearchSession | { error: string }> {
    const session = this.sessions.get(input.researchId);
    if (!session) {
      return { error: `Research session not found: ${input.researchId}` };
    }

    return {
      id: session.id,
      query: session.query,
      status: session.status,
      currentIteration: session.currentIteration,
      maxIterations: session.maxIterations,
      tokensUsed: session.tokensUsed,
      tokenBudget: session.tokenBudget,
      knowledgeCount: session.knowledgeCount,
      startTime: session.startTime,
      endTime: session.endTime,
      error: session.error,
    };
  }

  /**
   * Handle deep_research_report tool call
   */
  async handleReport(input: {
    researchId: string;
    format?: string;
  }): Promise<string | { error: string }> {
    const session = this.sessions.get(input.researchId);
    if (!session) {
      return { error: `Research session not found: ${input.researchId}` };
    }

    if (session.status !== 'completed') {
      return { error: `Research not completed yet. Status: ${session.status}` };
    }

    if (!session.result) {
      return { error: 'No result available' };
    }

    const format = input.format ?? 'markdown';
    if (format === 'json') {
      return JSON.stringify(session.result, null, 2);
    } else {
      return this.generateMarkdownReport(session);
    }
  }

  /**
   * Execute research (async)
   */
  private async executeResearch(
    sessionId: string,
    input: {
      query: string;
      maxIterations?: number;
      tokenBudget?: number;
      provider?: string;
    }
  ): Promise<void> {
    const session = this.sessions.get(sessionId);
    if (!session) return;

    try {
      // Import deep-research module
      const deepResearchModule = await import('@nahisaho/musubix-deep-research');
      const { ResearchEngine } = deepResearchModule;
      const createJinaProvider = deepResearchModule.createJinaProvider as any;
      const createBraveProvider = deepResearchModule.createBraveProvider as any;
      const createDuckDuckGoProvider = deepResearchModule.createDuckDuckGoProvider as any;

      // Create provider
      let searchProvider: any;
      const providerName = input.provider ?? 'jina';

      if (providerName === 'jina') {
        const apiKey = process.env.JINA_API_KEY;
        if (!apiKey) throw new Error('JINA_API_KEY not set');
        searchProvider = createJinaProvider({ apiKey });
      } else if (providerName === 'brave') {
        const apiKey = process.env.BRAVE_API_KEY;
        if (!apiKey) throw new Error('BRAVE_API_KEY not set');
        searchProvider = createBraveProvider({ apiKey });
      } else {
        searchProvider = createDuckDuckGoProvider();
      }

      // Create engine
      const engine = new ResearchEngine({
        query: input.query,
        maxIterations: session.maxIterations,
        tokenBudget: session.tokenBudget,
      });

      // Override search method to use provider
      (engine as any).search = async () => {
        return await searchProvider.search(input.query, { maxResults: 10 });
      };

      // Execute research
      const result = await engine.research();

      // Update session
      session.status = 'completed';
      session.currentIteration = session.maxIterations;
      session.tokensUsed = 0; // Would be tracked by tokenTracker
      session.knowledgeCount = 0; // Would be in knowledge base
      session.endTime = Date.now();
      session.result = result;
    } catch (error) {
      session.status = 'failed';
      session.error = error instanceof Error ? error.message : String(error);
      session.endTime = Date.now();
    }
  }

  /**
   * Generate markdown report
   */
  private generateMarkdownReport(session: ResearchSession): string {
    const lines: string[] = [];

    lines.push(`# Deep Research Report: ${session.query}`);
    lines.push('');
    lines.push(`**Research ID**: ${session.id}`);
    lines.push(`**Status**: ${session.status}`);
    lines.push(`**Iterations**: ${session.currentIteration}/${session.maxIterations}`);
    lines.push(`**Tokens**: ${session.tokensUsed}/${session.tokenBudget}`);
    lines.push(`**Duration**: ${((session.endTime! - session.startTime) / 1000).toFixed(2)}s`);
    lines.push('');

    if (session.result?.knowledge) {
      lines.push('## Findings');
      lines.push('');
      for (const [index, item] of session.result.knowledge.entries()) {
        lines.push(`### ${index + 1}. ${item.title || 'Finding'}`);
        lines.push('');
        lines.push(item.content);
        lines.push('');
        if (item.source) {
          lines.push(`**Source**: ${item.source}`);
          lines.push('');
        }
      }
    }

    return lines.join('\n');
  }

  /**
   * Clear old sessions (cleanup)
   */
  clearOldSessions(maxAgeMs: number = 3600000): number {
    const now = Date.now();
    let cleared = 0;

    for (const [id, session] of this.sessions.entries()) {
      const age = now - session.startTime;
      if (session.status !== 'running' && age > maxAgeMs) {
        this.sessions.delete(id);
        cleared++;
      }
    }

    return cleared;
  }
}

/**
 * Global MCP handler instance
 */
let globalHandler: DeepResearchMCPHandler | undefined;

/**
 * Get or create global MCP handler
 */
export function getMCPHandler(): DeepResearchMCPHandler {
  if (!globalHandler) {
    globalHandler = new DeepResearchMCPHandler();
  }
  return globalHandler;
}

/**
 * Tool definitions for MCP server registration
 */
export const DEEP_RESEARCH_TOOLS = [
  {
    name: 'deep_research_start',
    description: 'Start iterative deep research on a technical topic using search-read-reason cycle',
    inputSchema: {
      type: 'object',
      properties: {
        query: {
          type: 'string',
          description: 'Research question or topic',
        },
        maxIterations: {
          type: 'number',
          description: 'Maximum research iterations (default: 5)',
          minimum: 1,
          maximum: 20,
        },
        tokenBudget: {
          type: 'number',
          description: 'Token budget limit (default: 10000)',
          minimum: 1000,
          maximum: 100000,
        },
        provider: {
          type: 'string',
          enum: ['jina', 'brave', 'duckduckgo'],
          description: 'Search provider (default: jina)',
        },
      },
      required: ['query'],
    },
  },
  {
    name: 'deep_research_status',
    description: 'Get current status and progress of a deep research session',
    inputSchema: {
      type: 'object',
      properties: {
        researchId: {
          type: 'string',
          description: 'Research session ID',
        },
      },
      required: ['researchId'],
    },
  },
  {
    name: 'deep_research_report',
    description: 'Get final report from completed deep research session',
    inputSchema: {
      type: 'object',
      properties: {
        researchId: {
          type: 'string',
          description: 'Research session ID',
        },
        format: {
          type: 'string',
          enum: ['markdown', 'json'],
          description: 'Report format (default: markdown)',
        },
      },
      required: ['researchId'],
    },
  },
];
