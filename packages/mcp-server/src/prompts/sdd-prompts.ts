/**
 * MCP Prompts Definitions
 * 
 * Prompt definitions for MUSUBIX MCP Server
 * 
 * @packageDocumentation
 * @module prompts
 * 
 * @see REQ-INT-102 - MCP Server
 * @see REQ-CORE-101 - SDD Workflow
 */

import type { PromptDefinition, PromptResult, PromptMessage } from '../types.js';

/**
 * Create user message helper
 */
function userMessage(text: string): PromptMessage {
  return {
    role: 'user',
    content: { type: 'text', text },
  };
}

/**
 * Create assistant message helper
 */
function assistantMessage(text: string): PromptMessage {
  return {
    role: 'assistant',
    content: { type: 'text', text },
  };
}

// ============================================================
// Requirements Prompts
// ============================================================

/**
 * Requirements analysis prompt
 */
export const requirementsAnalysisPrompt: PromptDefinition = {
  name: 'sdd_requirements_analysis',
  description: 'Analyze and generate EARS-format requirements from a feature description',
  arguments: [
    {
      name: 'feature',
      description: 'Feature description to analyze',
      required: true,
    },
    {
      name: 'context',
      description: 'Additional context about the project',
      required: false,
    },
  ],
  handler: async (args): Promise<PromptResult> => {
    const { feature, context } = args;

    const systemInstructions = `You are an expert requirements analyst using the EARS (Easy Approach to Requirements Syntax) methodology.

Your task is to analyze the given feature and generate well-structured requirements.

## EARS Patterns:

1. **Ubiquitous**: "The <system> shall <action>" - For general requirements
2. **Event-Driven**: "When <trigger>, the <system> shall <action>" - For event responses
3. **State-Driven**: "While <state>, the <system> shall <action>" - For state-dependent behavior
4. **Optional**: "Where <feature>, the <system> shall <action>" - For optional features
5. **Unwanted**: "If <condition>, then the <system> shall <action>" - For error handling
6. **Complex**: Combination of patterns

## Requirements Structure:

For each requirement, provide:
- **ID**: REQ-XXX-NNN format
- **Pattern**: EARS pattern used
- **Priority**: P0 (Critical), P1 (High), P2 (Medium), P3 (Low)
- **Text**: The requirement statement
- **Rationale**: Why this requirement exists
- **Acceptance Criteria**: How to verify

${context ? `\n## Project Context:\n${context}` : ''}

Analyze the feature and generate comprehensive requirements.`;

    return {
      description: 'Requirements analysis using EARS methodology',
      messages: [
        userMessage(systemInstructions),
        assistantMessage('I understand. Please provide the feature description, and I will analyze it to generate EARS-format requirements with proper structure, priorities, and acceptance criteria.'),
        userMessage(`Please analyze this feature and generate EARS-format requirements:\n\n${feature}`),
      ],
    };
  },
};

/**
 * Requirements review prompt
 */
export const requirementsReviewPrompt: PromptDefinition = {
  name: 'sdd_requirements_review',
  description: 'Review requirements for completeness and constitutional compliance',
  arguments: [
    {
      name: 'requirements',
      description: 'Requirements document content to review',
      required: true,
    },
  ],
  handler: async (args): Promise<PromptResult> => {
    const { requirements } = args;

    const systemInstructions = `You are a senior requirements reviewer. Review the requirements against:

## 9 Constitutional Articles:

1. **Specification First**: Every feature must have requirements before design
2. **Design Before Code**: Design must exist before implementation
3. **Single Source of Truth**: Project memory is authoritative
4. **Traceability**: Every code change must trace to requirements
5. **Incremental Progress**: Frequent, small deliverables
6. **Decision Documentation**: All decisions are recorded as ADRs
7. **Quality Gates**: Phases must be validated before proceeding
8. **User-Centric**: User value must be documented
9. **Continuous Learning**: Retrospectives and improvements

## Review Criteria:

- EARS pattern correctness
- Completeness (functional, non-functional, constraints)
- Testability (clear acceptance criteria)
- Consistency (no contradictions)
- Priority appropriateness
- Traceability readiness

Provide a structured review with:
1. Summary assessment
2. Strengths
3. Issues found (categorized by severity)
4. Recommendations
5. Missing requirements suggestions`;

    return {
      description: 'Constitutional compliance review for requirements',
      messages: [
        userMessage(systemInstructions),
        assistantMessage('I will review the requirements against the 9 Constitutional Articles and provide a comprehensive assessment. Please share the requirements document.'),
        userMessage(`Please review these requirements:\n\n${requirements}`),
      ],
    };
  },
};

// ============================================================
// Design Prompts
// ============================================================

/**
 * Design generation prompt
 */
export const designGenerationPrompt: PromptDefinition = {
  name: 'sdd_design_generation',
  description: 'Generate C4 model design from requirements',
  arguments: [
    {
      name: 'requirements',
      description: 'Requirements to design for',
      required: true,
    },
    {
      name: 'techStack',
      description: 'Technology stack constraints',
      required: false,
    },
  ],
  handler: async (args): Promise<PromptResult> => {
    const { requirements, techStack } = args;

    const systemInstructions = `You are a senior software architect using C4 model methodology.

## C4 Model Levels:

1. **Context**: System boundary and external actors
2. **Container**: High-level technology choices
3. **Component**: Internal structure of containers
4. **Code**: Implementation details (usually diagrams)

## Design Document Structure:

1. **Overview**
   - Purpose
   - Scope
   - Requirements traceability

2. **Context Diagram**
   - System boundary
   - External actors
   - External systems

3. **Container Diagram**
   - Applications/services
   - Data stores
   - Communication protocols

4. **Component Diagrams**
   - Per container breakdown
   - Interfaces
   - Dependencies

5. **Architecture Decisions**
   - ADR format for key decisions
   - Rationale and consequences

6. **Non-Functional Considerations**
   - Performance
   - Security
   - Scalability

${techStack ? `\n## Technology Stack:\n${techStack}` : ''}

Generate a comprehensive design that maps to all requirements.`;

    return {
      description: 'C4 model design generation',
      messages: [
        userMessage(systemInstructions),
        assistantMessage('I will create a comprehensive C4 model design document. Please provide the requirements.'),
        userMessage(`Generate a C4 design for these requirements:\n\n${requirements}`),
      ],
    };
  },
};

/**
 * Design review prompt
 */
export const designReviewPrompt: PromptDefinition = {
  name: 'sdd_design_review',
  description: 'Review design for architecture quality and traceability',
  arguments: [
    {
      name: 'design',
      description: 'Design document to review',
      required: true,
    },
    {
      name: 'requirements',
      description: 'Requirements for traceability check',
      required: false,
    },
  ],
  handler: async (args): Promise<PromptResult> => {
    const { design, requirements } = args;

    const systemInstructions = `You are a principal architect reviewing design documents.

## Review Criteria:

1. **C4 Completeness**
   - All levels properly documented
   - Clear boundaries and interfaces

2. **Requirements Traceability**
   - Every requirement has design coverage
   - No orphan components

3. **Architecture Quality**
   - Separation of concerns
   - Appropriate abstraction levels
   - Technology choices justified

4. **Non-Functional Requirements**
   - Performance considerations
   - Security by design
   - Scalability patterns

5. **ADR Quality**
   - Clear problem statements
   - Alternatives considered
   - Consequences documented

Provide structured feedback with:
- Coverage analysis
- Architecture issues
- Improvement recommendations
- Risk assessment`;

    return {
      description: 'Architecture design review',
      messages: [
        userMessage(systemInstructions),
        assistantMessage('I will perform a thorough architecture review. Please provide the design document' + (requirements ? ' and requirements for traceability analysis' : '') + '.'),
        userMessage(`Please review this design:\n\n${design}${requirements ? `\n\n## Requirements for Traceability:\n${requirements}` : ''}`),
      ],
    };
  },
};

// ============================================================
// Task Prompts
// ============================================================

/**
 * Task decomposition prompt
 */
export const taskDecompositionPrompt: PromptDefinition = {
  name: 'sdd_task_decomposition',
  description: 'Decompose design into implementation tasks',
  arguments: [
    {
      name: 'design',
      description: 'Design document to decompose',
      required: true,
    },
    {
      name: 'sprintDays',
      description: 'Number of days per sprint',
      required: false,
    },
  ],
  handler: async (args): Promise<PromptResult> => {
    const { design, sprintDays } = args;

    const systemInstructions = `You are a technical lead decomposing design into tasks.

## Task Structure:

For each task:
- **ID**: TSK-XXX-NNN format
- **Title**: Clear, action-oriented
- **Description**: What needs to be done
- **Estimated Hours**: Realistic estimate
- **Dependencies**: Other tasks that must complete first
- **Design Reference**: Which design section it implements
- **Acceptance Criteria**: Definition of done

## Sprint Planning:

- Sprint duration: ${sprintDays || 5} days
- Maximum 6 hours productive coding per day
- Include buffer for reviews and integration
- Balance load across sprint

## Task Categories:

1. **Setup**: Environment, configuration
2. **Core**: Main functionality implementation
3. **Integration**: Component connections
4. **Testing**: Unit, integration tests
5. **Documentation**: Code docs, user guides

Create a complete task breakdown with sprint allocation.`;

    return {
      description: 'Design to task decomposition',
      messages: [
        userMessage(systemInstructions),
        assistantMessage('I will create a detailed task breakdown with sprint planning. Please provide the design document.'),
        userMessage(`Decompose this design into tasks:\n\n${design}`),
      ],
    };
  },
};

// ============================================================
// Steering Prompts
// ============================================================

/**
 * Project steering prompt
 */
export const projectSteeringPrompt: PromptDefinition = {
  name: 'sdd_project_steering',
  description: 'Update project memory (structure, tech, product)',
  arguments: [
    {
      name: 'aspect',
      description: 'Which aspect to update: structure, tech, or product',
      required: true,
    },
    {
      name: 'currentContent',
      description: 'Current content of the steering document',
      required: false,
    },
    {
      name: 'changes',
      description: 'Changes to incorporate',
      required: true,
    },
  ],
  handler: async (args): Promise<PromptResult> => {
    const { aspect, currentContent, changes } = args;

    const templates: Record<string, string> = {
      structure: `## Architecture Structure Document

### Overview
Project architecture patterns and structure.

### Patterns
- Design patterns in use
- Code organization
- Module structure

### Conventions
- Naming conventions
- File organization
- Import patterns`,

      tech: `## Technology Stack Document

### Languages
- Primary languages
- Version requirements

### Frameworks
- Core frameworks
- Supporting libraries

### Tools
- Build tools
- Development tools
- Testing tools`,

      product: `## Product Context Document

### Vision
Product vision and goals.

### Users
Target users and personas.

### Features
Core features and capabilities.

### Success Metrics
How we measure success.`,
    };

    const template = templates[aspect] || 'Unknown aspect';

    return {
      description: `Update project ${aspect} steering document`,
      messages: [
        userMessage(`You are updating the project ${aspect} document. 
${currentContent ? `Current content:\n${currentContent}` : `Use this template:\n${template}`}

Incorporate these changes while maintaining document structure and consistency.`),
        assistantMessage(`I will update the ${aspect} document incorporating the changes while maintaining proper structure.`),
        userMessage(`Please update the document with these changes:\n\n${changes}`),
      ],
    };
  },
};

/**
 * All SDD prompts
 */
export const sddPrompts: PromptDefinition[] = [
  requirementsAnalysisPrompt,
  requirementsReviewPrompt,
  designGenerationPrompt,
  designReviewPrompt,
  taskDecompositionPrompt,
  projectSteeringPrompt,
];

/**
 * Get all SDD prompt definitions
 */
export function getSddPrompts(): PromptDefinition[] {
  return sddPrompts;
}
