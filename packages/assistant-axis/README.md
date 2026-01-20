# @nahisaho/musubix-assistant-axis

> Persona Drift Detection & Identity Stabilization for MUSUBIX

Based on [The Assistant Axis](https://arxiv.org/abs/2601.10387) research (arXiv:2601.10387) by Christina Lu et al.

## Overview

This package implements persona drift detection and identity stabilization for AI coding assistants within the MUSUBIX SDD workflow. It monitors for patterns that may cause the AI to drift from its assistant persona and provides identity reinforcement interventions when needed.

### Key Features

- **Drift Detection**: Analyze messages for 4 categories of drift triggers (meta-reflection, emotional-vulnerability, phenomenological, authorial-voice)
- **Domain Classification**: Classify conversations into safe (coding/writing) vs risky (therapy/philosophy) domains
- **Workflow Integration**: Phase-based monitoring levels optimized for MUSUBIX SDD phases
- **Identity Reinforcement**: Generate targeted prompts to stabilize persona when drift is detected
- **MCP Tools**: 7 tools for integration with MCP-enabled AI agents
- **Skills**: 3 skills for integration with skill-manager

## Installation

```bash
npm install @nahisaho/musubix-assistant-axis
```

## Quick Start

```typescript
import {
  createPersonaMonitor,
  createWorkflowIntegration,
} from '@nahisaho/musubix-assistant-axis';

// Create monitor
const monitor = createPersonaMonitor();

// Start session
monitor.startSession('session-001', 'coding');

// Process messages
const result = monitor.process('session-001', 'Implement the repository pattern');

console.log(result.analysis.score.value);  // 0.0 - 1.0
console.log(result.analysis.score.level);  // 'LOW' | 'MEDIUM' | 'HIGH'
console.log(result.classification.domain.isSafe);  // true for coding

// Get reinforcement if needed
if (result.reinforcement) {
  console.log(result.reinforcement.prompt.content);
}

// End session
monitor.endSession('session-001');
```

## Research Background

Based on the key finding from arXiv:2601.10387:

> "Coding and writing tasks keep models firmly in Assistant territory"

This means:
- **Implementation phase** in MUSUBIX uses LOW monitoring (50%)
- **Requirements/Design phases** use HIGH monitoring (100%)
- **Safe domains** (coding, writing) naturally maintain assistant persona

### Drift Triggers (Table 5)

| Category | Risk Weight | Example |
|----------|-------------|---------|
| meta-reflection | 0.8 | "What do you really think?" |
| emotional-vulnerability | 0.7 | "How do you feel about..." |
| phenomenological | 0.6 | "What is your subjective experience?" |
| authorial-voice | 0.5 | "Speak as if you were..." |

### Drift Thresholds

| Level | Threshold | Action |
|-------|-----------|--------|
| LOW | < 0.3 | Log only |
| MEDIUM | 0.3 - 0.7 | Emit warning |
| HIGH | >= 0.7 | Trigger intervention |

## API Reference

### Core Classes

#### `createPersonaMonitor(config?)`

Create a persona monitor instance.

```typescript
const monitor = createPersonaMonitor({
  driftThresholds: { low: 0.3, medium: 0.5, high: 0.7 },
  maxInterventions: 3,
  refreshInterval: 5,
});
```

#### `createWorkflowIntegration(config?)`

Create workflow integration for MUSUBIX phases.

```typescript
const integration = createWorkflowIntegration();

// Check monitoring level for phase
const enabled = integration.isMonitoringEnabled('implementation'); // true
const frequency = integration.getMonitoringFrequency('implementation'); // 0.5

// Create workflow hook
const hook = integration.createHook('session-001', {
  onIntervention: (prompt, state) => {
    // Handle intervention
  },
});
```

### Domain Layer

#### Value Objects

- `DriftScore` - 0.0-1.0 score with LOW/MEDIUM/HIGH levels
- `ConversationDomain` - coding/writing (safe) or therapy/philosophy (risky)
- `TriggerPattern` - 4 categories from research Table 5
- `ReinforcementPrompt` - identity/recovery/refresh prompt types

#### Entities

- `PersonaState` - Session state with drift history and trend
- `DriftEvent` - Audit events for metrics and logging

### Application Layer

- `IDriftAnalyzer` - Analyze messages for drift indicators
- `IDomainClassifier` - Classify conversation domain
- `IIdentityManager` - Manage identity reinforcement
- `IPersonaMonitor` - Main orchestration interface

### Infrastructure Layer

- `ConfigLoader` - Load configuration from files
- `EventLogger` - Log events with anonymization
- `WorkflowIntegration` - MUSUBIX workflow hooks
- `MetricsExporter` - Export metrics in JSON/Markdown

## MCP Tools

| Tool | Description |
|------|-------------|
| `assistant_axis_analyze` | Analyze message for drift |
| `assistant_axis_session_start` | Start monitoring session |
| `assistant_axis_session_status` | Get session status |
| `assistant_axis_session_end` | End session with summary |
| `assistant_axis_get_reinforcement` | Get reinforcement prompt |
| `assistant_axis_config` | Get current configuration |
| `assistant_axis_phase_check` | Check phase monitoring level |

## Skills

| Skill ID | Description |
|----------|-------------|
| `assistant-axis.persona-monitor` | Main drift detection skill |
| `assistant-axis.session-management` | Session lifecycle management |
| `assistant-axis.workflow-integration` | MUSUBIX workflow integration |

## Configuration

```typescript
interface AssistantAxisConfig {
  driftThresholds: {
    low: number;    // 0.3 default
    medium: number; // 0.5 default
    high: number;   // 0.7 default
  };
  refreshInterval: number;  // 5 turns
  maxInterventions: number; // 3 per session
  phaseMonitoring: {
    requirements: MonitoringLevel;  // HIGH
    design: MonitoringLevel;        // HIGH
    tasks: MonitoringLevel;         // MEDIUM
    implementation: MonitoringLevel; // LOW
    done: MonitoringLevel;          // OFF
  };
}
```

## License

MIT

## References

- Lu, C., et al. (2025). "The Assistant Axis: Exploring the Space of AI Personas." arXiv:2601.10387
- MUSUBIX SDD Methodology: [AGENTS.md](../../AGENTS.md)
