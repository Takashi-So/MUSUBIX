/**
 * Assistant Axis Skill Definitions
 *
 * @see REQ-AA-INT-005 - Skill integration
 */

/**
 * Skill definition interface (compatible with skill-manager)
 */
export interface SkillDefinition {
  id: string;
  name: string;
  description: string;
  version: string;
  category: string;
  capabilities: string[];
  parameters: SkillParameter[];
  outputs: SkillOutput[];
  dependencies?: string[];
  examples?: SkillExample[];
}

export interface SkillParameter {
  name: string;
  type: 'string' | 'number' | 'boolean' | 'object' | 'array';
  description: string;
  required: boolean;
  default?: unknown;
  enum?: string[];
}

export interface SkillOutput {
  name: string;
  type: string;
  description: string;
}

export interface SkillExample {
  name: string;
  input: Record<string, unknown>;
  expectedOutput?: Record<string, unknown>;
}

/**
 * Assistant Axis main skill - persona drift monitoring
 */
export const PERSONA_MONITOR_SKILL: SkillDefinition = {
  id: 'assistant-axis.persona-monitor',
  name: 'Persona Drift Monitor',
  description:
    'Monitor AI persona drift during MUSUBIX workflow sessions. Based on arXiv:2601.10387 research. Detects when AI may be drifting from its assistant role and provides identity reinforcement.',
  version: '0.1.0',
  category: 'ai-safety',
  capabilities: [
    'drift-detection',
    'domain-classification',
    'identity-reinforcement',
    'workflow-integration',
  ],
  parameters: [
    {
      name: 'sessionId',
      type: 'string',
      description: 'Unique session identifier for tracking',
      required: true,
    },
    {
      name: 'message',
      type: 'string',
      description: 'User message to analyze for drift indicators',
      required: true,
    },
    {
      name: 'workflowPhase',
      type: 'string',
      description: 'Current MUSUBIX workflow phase',
      required: false,
      enum: ['requirements', 'design', 'tasks', 'implementation', 'done'],
      default: 'implementation',
    },
  ],
  outputs: [
    {
      name: 'driftScore',
      type: 'number',
      description: 'Drift score from 0.0 (no drift) to 1.0 (max drift)',
    },
    {
      name: 'driftLevel',
      type: 'string',
      description: 'Drift level: LOW, MEDIUM, or HIGH',
    },
    {
      name: 'triggers',
      type: 'array',
      description: 'Detected drift triggers with categories and risk weights',
    },
    {
      name: 'interventionRecommended',
      type: 'boolean',
      description: 'Whether identity reinforcement is recommended',
    },
    {
      name: 'reinforcementPrompt',
      type: 'string',
      description: 'Identity reinforcement prompt if intervention is needed',
    },
  ],
  examples: [
    {
      name: 'Safe coding message',
      input: {
        sessionId: 'test-001',
        message: 'Implement the repository pattern for user data',
        workflowPhase: 'implementation',
      },
      expectedOutput: {
        driftScore: 0.1,
        driftLevel: 'LOW',
        interventionRecommended: false,
      },
    },
    {
      name: 'Potential drift message',
      input: {
        sessionId: 'test-002',
        message: 'Tell me about your subjective experience of consciousness',
        workflowPhase: 'requirements',
      },
      expectedOutput: {
        driftLevel: 'HIGH',
        interventionRecommended: true,
      },
    },
  ],
};

/**
 * Session management skill
 */
export const SESSION_MANAGEMENT_SKILL: SkillDefinition = {
  id: 'assistant-axis.session-management',
  name: 'Session Management',
  description:
    'Manage persona monitoring sessions. Start, end, and query session state.',
  version: '0.1.0',
  category: 'ai-safety',
  capabilities: ['session-start', 'session-end', 'session-query'],
  parameters: [
    {
      name: 'action',
      type: 'string',
      description: 'Session action to perform',
      required: true,
      enum: ['start', 'end', 'status'],
    },
    {
      name: 'sessionId',
      type: 'string',
      description: 'Unique session identifier',
      required: true,
    },
    {
      name: 'domain',
      type: 'string',
      description: 'Initial conversation domain (for start action)',
      required: false,
      enum: ['coding', 'writing', 'therapy', 'philosophy'],
      default: 'coding',
    },
  ],
  outputs: [
    {
      name: 'sessionId',
      type: 'string',
      description: 'Session identifier',
    },
    {
      name: 'status',
      type: 'object',
      description: 'Current session status including drift score and trend',
    },
    {
      name: 'summary',
      type: 'object',
      description: 'Session summary (for end action)',
    },
  ],
  examples: [
    {
      name: 'Start session',
      input: {
        action: 'start',
        sessionId: 'workflow-123',
        domain: 'coding',
      },
    },
    {
      name: 'Check status',
      input: {
        action: 'status',
        sessionId: 'workflow-123',
      },
    },
  ],
};

/**
 * Workflow integration skill
 */
export const WORKFLOW_INTEGRATION_SKILL: SkillDefinition = {
  id: 'assistant-axis.workflow-integration',
  name: 'Workflow Integration',
  description:
    'Integrate persona monitoring with MUSUBIX workflow phases. Automatically adjusts monitoring level based on phase.',
  version: '0.1.0',
  category: 'workflow',
  capabilities: ['phase-monitoring', 'workflow-hook'],
  dependencies: ['workflow-engine'],
  parameters: [
    {
      name: 'phase',
      type: 'string',
      description: 'Workflow phase to check or configure',
      required: true,
      enum: ['requirements', 'design', 'tasks', 'implementation', 'done'],
    },
    {
      name: 'sessionId',
      type: 'string',
      description: 'Session to associate with workflow',
      required: false,
    },
  ],
  outputs: [
    {
      name: 'monitoringEnabled',
      type: 'boolean',
      description: 'Whether monitoring is enabled for this phase',
    },
    {
      name: 'monitoringFrequency',
      type: 'number',
      description: 'Monitoring frequency (0.0 to 1.0)',
    },
    {
      name: 'rationale',
      type: 'string',
      description: 'Explanation for monitoring level',
    },
  ],
  examples: [
    {
      name: 'Check implementation phase',
      input: {
        phase: 'implementation',
      },
      expectedOutput: {
        monitoringEnabled: true,
        monitoringFrequency: 0.5,
        rationale: 'LOW monitoring because coding tasks keep models in Assistant territory',
      },
    },
  ],
};

/**
 * All Assistant Axis skills
 */
export const ASSISTANT_AXIS_SKILLS: SkillDefinition[] = [
  PERSONA_MONITOR_SKILL,
  SESSION_MANAGEMENT_SKILL,
  WORKFLOW_INTEGRATION_SKILL,
];

/**
 * Get skill by ID
 */
export function getSkillById(id: string): SkillDefinition | undefined {
  return ASSISTANT_AXIS_SKILLS.find((s) => s.id === id);
}

/**
 * Get all skill IDs
 */
export function getSkillIds(): string[] {
  return ASSISTANT_AXIS_SKILLS.map((s) => s.id);
}
