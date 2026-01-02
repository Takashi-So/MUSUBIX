/**
 * MCP Resources Definitions
 * 
 * Resource definitions for MUSUBIX MCP Server
 * 
 * @packageDocumentation
 * @module resources
 * 
 * @see REQ-INT-102 - MCP Server
 * @see REQ-CORE-101 - SDD Workflow
 */

import type {
  ResourceDefinition,
  ResourceTemplateDefinition,
  ResourceResult,
} from '../types.js';

// ============================================================
// Static Resources
// ============================================================

/**
 * Constitution resource - The 9 Articles
 */
export const constitutionResource: ResourceDefinition = {
  uri: 'musubix://constitution',
  name: 'Constitutional Articles',
  description: 'The 9 Constitutional Articles governing MUSUBIX SDD workflow',
  mimeType: 'text/markdown',
  handler: async (): Promise<ResourceResult> => {
    const constitution = `# MUSUBIX Constitution

## The 9 Constitutional Articles

### Article 1: Specification First
Every feature MUST have a requirements specification before design begins.
- Requirements use EARS format
- Each requirement has unique ID
- Acceptance criteria are mandatory

### Article 2: Design Before Code
Design documentation MUST exist before implementation starts.
- C4 model diagrams required
- ADRs document key decisions
- All requirements must map to design elements

### Article 3: Single Source of Truth
Project memory (steering/) is the authoritative source for:
- Architecture decisions (structure.md)
- Technology stack (tech.md)
- Product context (product.md)
- Governance rules (rules/constitution.md)

### Article 4: Traceability
Every code change MUST trace back to:
- A requirement ID
- A design component
- An implementation task

### Article 5: Incremental Progress
Work proceeds in small, validated increments:
- Maximum 2-week sprints
- Daily progress checkpoints
- Frequent integration

### Article 6: Decision Documentation
All significant decisions are recorded as:
- Architecture Decision Records (ADRs)
- With context, alternatives, and consequences
- Including date and status

### Article 7: Quality Gates
Each phase requires validation before proceeding:
- Requirements → Review → Approved
- Design → Review → Approved
- Tasks → Review → Approved
- Implementation → Test → Verified

### Article 8: User-Centric
User value MUST be documented:
- User stories with acceptance criteria
- Clear definition of done
- Measurable outcomes

### Article 9: Continuous Learning
Improvement through retrospectives:
- After each sprint
- Document lessons learned
- Update processes accordingly
`;

    return {
      contents: [
        {
          uri: 'musubix://constitution',
          mimeType: 'text/markdown',
          text: constitution,
        },
      ],
    };
  },
};

/**
 * EARS patterns resource
 */
export const earsPatternsResource: ResourceDefinition = {
  uri: 'musubix://patterns/ears',
  name: 'EARS Patterns',
  description: 'Easy Approach to Requirements Syntax patterns and examples',
  mimeType: 'text/markdown',
  handler: async (): Promise<ResourceResult> => {
    const ears = `# EARS Requirement Patterns

## Overview
EARS (Easy Approach to Requirements Syntax) provides structured patterns for writing clear, testable requirements.

## Patterns

### 1. Ubiquitous Requirements
General requirements that always apply.

**Template:** The <system> shall <action>.

**Example:**
\`\`\`
REQ-SYS-001: The system shall encrypt all stored passwords using bcrypt.
\`\`\`

### 2. Event-Driven Requirements
Requirements triggered by specific events.

**Template:** When <trigger>, the <system> shall <action>.

**Example:**
\`\`\`
REQ-AUTH-001: When a user submits login credentials, the system shall validate them within 2 seconds.
\`\`\`

### 3. State-Driven Requirements
Requirements dependent on system state.

**Template:** While <state>, the <system> shall <action>.

**Example:**
\`\`\`
REQ-CONN-001: While connected to the network, the system shall sync data every 5 minutes.
\`\`\`

### 4. Optional Feature Requirements
Requirements for configurable features.

**Template:** Where <feature is enabled>, the <system> shall <action>.

**Example:**
\`\`\`
REQ-LOG-001: Where debug logging is enabled, the system shall log all API requests.
\`\`\`

### 5. Unwanted Behavior Requirements
Requirements for handling errors or exceptions.

**Template:** If <condition>, then the <system> shall <action>.

**Example:**
\`\`\`
REQ-ERR-001: If database connection fails, then the system shall retry 3 times before alerting.
\`\`\`

### 6. Complex Requirements
Combining multiple patterns.

**Template:** While <state>, when <trigger>, the <system> shall <action>.

**Example:**
\`\`\`
REQ-PERF-001: While under high load, when a request exceeds timeout, the system shall queue the request for retry.
\`\`\`

## Best Practices

1. **One requirement per statement** - Avoid compound requirements
2. **Measurable actions** - Use specific, testable terms
3. **Consistent terminology** - Define terms in glossary
4. **Unique identifiers** - Use systematic ID scheme
5. **Clear rationale** - Document why each requirement exists
`;

    return {
      contents: [
        {
          uri: 'musubix://patterns/ears',
          mimeType: 'text/markdown',
          text: ears,
        },
      ],
    };
  },
};

/**
 * C4 model patterns resource
 */
export const c4PatternsResource: ResourceDefinition = {
  uri: 'musubix://patterns/c4',
  name: 'C4 Model Patterns',
  description: 'C4 architecture model patterns and templates',
  mimeType: 'text/markdown',
  handler: async (): Promise<ResourceResult> => {
    const c4 = `# C4 Model Architecture Patterns

## Overview
C4 model provides four levels of abstraction for describing software architecture.

## Levels

### Level 1: Context Diagram
Shows the system in its environment.

**Elements:**
- System under design (center)
- Users/Actors
- External systems
- Relationships

**Template:**
\`\`\`mermaid
C4Context
    title System Context Diagram
    
    Person(user, "User", "Description")
    System(system, "System", "Description")
    System_Ext(external, "External System", "Description")
    
    Rel(user, system, "Uses")
    Rel(system, external, "Calls")
\`\`\`

### Level 2: Container Diagram
Shows high-level technology choices.

**Elements:**
- Containers (applications, data stores)
- Technologies
- Communication protocols

**Template:**
\`\`\`mermaid
C4Container
    title Container Diagram
    
    Container(web, "Web App", "React", "User interface")
    Container(api, "API", "Node.js", "Business logic")
    ContainerDb(db, "Database", "PostgreSQL", "Stores data")
    
    Rel(web, api, "REST/JSON")
    Rel(api, db, "SQL")
\`\`\`

### Level 3: Component Diagram
Shows internal structure of containers.

**Elements:**
- Components/modules
- Interfaces
- Dependencies

**Template:**
\`\`\`mermaid
C4Component
    title Component Diagram - API Container
    
    Component(auth, "Auth Service", "Handles authentication")
    Component(users, "User Service", "User management")
    Component(data, "Data Access", "Database operations")
    
    Rel(auth, users, "Validates")
    Rel(users, data, "Queries")
\`\`\`

### Level 4: Code
Detailed class/module diagrams.

**Note:** Usually generated from code, not hand-drawn.

## Best Practices

1. **Start with context** - Always begin at level 1
2. **Progressive detail** - Add detail only where needed
3. **Consistent notation** - Use standard C4 shapes
4. **Clear labels** - Name, technology, description
5. **Show relationships** - Label all connections
`;

    return {
      contents: [
        {
          uri: 'musubix://patterns/c4',
          mimeType: 'text/markdown',
          text: c4,
        },
      ],
    };
  },
};

/**
 * ADR template resource
 */
export const adrTemplateResource: ResourceDefinition = {
  uri: 'musubix://templates/adr',
  name: 'ADR Template',
  description: 'Architecture Decision Record template',
  mimeType: 'text/markdown',
  handler: async (): Promise<ResourceResult> => {
    const adr = `# ADR-NNN: Title

## Status
Proposed | Accepted | Deprecated | Superseded by ADR-XXX

## Date
YYYY-MM-DD

## Context
What is the issue that we're seeing that is motivating this decision or change?

## Decision
What is the change that we're proposing and/or doing?

## Consequences

### Positive
- Benefit 1
- Benefit 2

### Negative
- Trade-off 1
- Trade-off 2

### Neutral
- Side effect 1

## Alternatives Considered

### Alternative 1
- Description
- Pros
- Cons
- Why not chosen

### Alternative 2
- Description
- Pros
- Cons
- Why not chosen

## References
- Related documents
- External resources
`;

    return {
      contents: [
        {
          uri: 'musubix://templates/adr',
          mimeType: 'text/markdown',
          text: adr,
        },
      ],
    };
  },
};

// ============================================================
// Resource Templates (Dynamic)
// ============================================================

/**
 * Requirement document template
 */
export const requirementDocTemplate: ResourceTemplateDefinition = {
  uriTemplate: 'musubix://specs/{projectId}/requirements',
  name: 'Requirements Document',
  description: 'Project requirements document',
  mimeType: 'text/markdown',
  handler: async (uri, params): Promise<ResourceResult> => {
    const { projectId } = params;

    const template = `# Requirements Document: ${projectId}

## Document Information
- **Project**: ${projectId}
- **Version**: 1.0
- **Status**: Draft
- **Created**: ${new Date().toISOString().split('T')[0]}

## 1. Overview

### 1.1 Purpose
[Describe the purpose of this requirements document]

### 1.2 Scope
[Define the scope of the feature/system]

### 1.3 Definitions
| Term | Definition |
|------|------------|
| | |

## 2. Functional Requirements

### 2.1 [Category Name]

#### REQ-XXX-001 [Requirement Title]
- **Pattern**: [EARS Pattern]
- **Priority**: P0/P1/P2/P3
- **Text**: [Requirement statement]
- **Rationale**: [Why this requirement exists]
- **Acceptance Criteria**:
  - [ ] Criterion 1
  - [ ] Criterion 2

## 3. Non-Functional Requirements

### 3.1 Performance

### 3.2 Security

### 3.3 Usability

## 4. Constraints

## 5. Assumptions

## 6. Approval History
| Version | Date | Reviewer | Status |
|---------|------|----------|--------|
| | | | |
`;

    return {
      contents: [
        {
          uri,
          mimeType: 'text/markdown',
          text: template,
        },
      ],
    };
  },
};

/**
 * Design document template
 */
export const designDocTemplate: ResourceTemplateDefinition = {
  uriTemplate: 'musubix://specs/{projectId}/design',
  name: 'Design Document',
  description: 'Project design document',
  mimeType: 'text/markdown',
  handler: async (uri, params): Promise<ResourceResult> => {
    const { projectId } = params;

    const template = `# Design Document: ${projectId}

## Document Information
- **Project**: ${projectId}
- **Version**: 1.0
- **Status**: Draft
- **Created**: ${new Date().toISOString().split('T')[0]}

## 1. Overview

### 1.1 Purpose
[Describe the purpose of this design]

### 1.2 Requirements Traceability
| Requirement | Design Element | Coverage |
|-------------|----------------|----------|
| | | |

## 2. System Context (C4 Level 1)

### 2.1 Context Diagram
\`\`\`mermaid
C4Context
    title System Context
\`\`\`

### 2.2 Actors and External Systems
| Actor/System | Description | Interactions |
|--------------|-------------|--------------|
| | | |

## 3. Container View (C4 Level 2)

### 3.1 Container Diagram
\`\`\`mermaid
C4Container
    title Container Diagram
\`\`\`

### 3.2 Container Descriptions
| Container | Technology | Responsibility |
|-----------|------------|----------------|
| | | |

## 4. Component View (C4 Level 3)

### 4.1 [Container Name] Components
\`\`\`mermaid
C4Component
    title Component Diagram
\`\`\`

## 5. Architecture Decisions

### ADR-001: [Decision Title]
- **Status**: Proposed
- **Context**: [Context]
- **Decision**: [Decision]
- **Consequences**: [Consequences]

## 6. Approval History
| Version | Date | Reviewer | Status |
|---------|------|----------|--------|
| | | | |
`;

    return {
      contents: [
        {
          uri,
          mimeType: 'text/markdown',
          text: template,
        },
      ],
    };
  },
};

/**
 * Task document template
 */
export const taskDocTemplate: ResourceTemplateDefinition = {
  uriTemplate: 'musubix://specs/{projectId}/tasks',
  name: 'Task Document',
  description: 'Project task breakdown document',
  mimeType: 'text/markdown',
  handler: async (uri, params): Promise<ResourceResult> => {
    const { projectId } = params;

    const template = `# Task Breakdown: ${projectId}

## Document Information
- **Project**: ${projectId}
- **Version**: 1.0
- **Status**: Draft
- **Created**: ${new Date().toISOString().split('T')[0]}

## 1. Overview

### 1.1 Sprint Planning
- **Sprint Duration**: 5 days
- **Daily Capacity**: 6 hours
- **Total Sprints**: TBD

### 1.2 Design Traceability
| Design Element | Tasks | Coverage |
|----------------|-------|----------|
| | | |

## 2. Sprint 1: [Sprint Name]

### Summary
- **Duration**: X days
- **Total Hours**: X hours
- **Tasks**: X tasks

### Tasks

#### TSK-001: [Task Title]
- **Estimated Hours**: X
- **Dependencies**: None
- **Design Reference**: [Component]
- **Description**: [What needs to be done]
- **Acceptance Criteria**:
  - [ ] Criterion 1
  - [ ] Criterion 2

## 3. Sprint 2: [Sprint Name]

### Summary
- **Duration**: X days
- **Total Hours**: X hours
- **Tasks**: X tasks

### Tasks
[Tasks listed here]

## 4. Risk Assessment

| Risk | Impact | Mitigation |
|------|--------|------------|
| | | |

## 5. Approval History
| Version | Date | Reviewer | Status |
|---------|------|----------|--------|
| | | | |
`;

    return {
      contents: [
        {
          uri,
          mimeType: 'text/markdown',
          text: template,
        },
      ],
    };
  },
};

/**
 * All static SDD resources
 */
export const sddResources: ResourceDefinition[] = [
  constitutionResource,
  earsPatternsResource,
  c4PatternsResource,
  adrTemplateResource,
];

/**
 * All SDD resource templates
 */
export const sddResourceTemplates: ResourceTemplateDefinition[] = [
  requirementDocTemplate,
  designDocTemplate,
  taskDocTemplate,
];

/**
 * Get all SDD resource definitions
 */
export function getSddResources(): ResourceDefinition[] {
  return sddResources;
}

/**
 * Get all SDD resource template definitions
 */
export function getSddResourceTemplates(): ResourceTemplateDefinition[] {
  return sddResourceTemplates;
}
