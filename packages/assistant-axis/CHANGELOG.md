# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] - 2026-01-20

### Added

#### Domain Layer
- **DriftScore** value object (0.0-1.0 with LOW/MEDIUM/HIGH levels)
- **ConversationDomain** value object (coding/writing=safe, therapy/philosophy=risky)
- **TriggerPattern** value object (4 categories from arXiv:2601.10387 Table 5)
- **ReinforcementPrompt** value object (identity/recovery/refresh types)
- **PersonaState** entity (session state with drift history and trend)
- **DriftEvent** entity (7 event types for audit logging)

#### Application Layer
- **DriftAnalyzer** service - analyze messages for drift indicators
- **DomainClassifier** service - classify conversation domains
- **IdentityManager** service - manage identity reinforcement interventions
- **PersonaMonitor** service - main orchestration combining all services

#### Infrastructure Layer
- **ConfigLoader** - load configuration from files and environment
- **EventLogger** - log events with anonymization support
- **WorkflowIntegration** - MUSUBIX workflow phase hooks
- **MetricsExporter** - export metrics in JSON/Markdown formats

#### CLI Commands
- `analyze <message>` - analyze message for drift indicators
- `session start|end|status` - manage monitoring sessions
- `config` - show current configuration
- `metrics` - export metrics
- `phase <name>` - check phase monitoring level
- `reset` - reset all sessions

#### MCP Tools (7 tools)
- `assistant_axis_analyze` - analyze message for drift
- `assistant_axis_session_start` - start monitoring session
- `assistant_axis_session_status` - get session status
- `assistant_axis_session_end` - end session with summary
- `assistant_axis_get_reinforcement` - get reinforcement prompt
- `assistant_axis_config` - get current configuration
- `assistant_axis_phase_check` - check phase monitoring level

#### Skills (3 skills)
- `assistant-axis.persona-monitor` - main drift detection skill
- `assistant-axis.session-management` - session lifecycle management
- `assistant-axis.workflow-integration` - MUSUBIX workflow integration

#### Configuration
- Research-based default thresholds (low=0.3, medium=0.5, high=0.7)
- Phase-based monitoring levels (implementation=LOW based on paper finding)
- Privacy-first logging (anonymize=true by default)

### Research Foundation

Based on "The Assistant Axis" (arXiv:2601.10387) by Christina Lu et al.

Key findings implemented:
- "Coding and writing tasks keep models firmly in Assistant territory"
- 4 trigger categories with risk weights from Table 5
- Identity reinforcement prompts based on Assistant traits (Figure 3, Table 2)

### Tests

- 113 passing tests
- Full coverage of domain, application, infrastructure layers
- MCP tool handler tests
- Skill executor tests

### Documentation

- Comprehensive README with API reference
- Inline JSDoc comments with research citations
- Requirements specification (REQ-ASSISTANT-AXIS-v0.1.0)
- Design document (DES-ASSISTANT-AXIS-v0.1.0)
- Task breakdown (TSK-ASSISTANT-AXIS-v0.1.0)
