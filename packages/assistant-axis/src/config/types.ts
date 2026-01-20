/**
 * Assistant Axis Configuration Types
 *
 * @see REQ-AA-NFR-003 - Configuration
 * @see DES-ASSISTANT-AXIS-v0.1.0 Section 5.5, 7.1
 */

/**
 * Drift level classification
 */
export type DriftLevel = 'LOW' | 'MEDIUM' | 'HIGH';

/**
 * Monitoring level based on workflow phase
 */
export type MonitoringLevel = 'OFF' | 'LOW' | 'MEDIUM' | 'HIGH';

/**
 * Drift threshold configuration
 *
 * @see REQ-AA-DRIFT-004 - Threshold alerts
 */
export interface DriftThresholds {
  /** Threshold for LOW level (default: 0.3) */
  readonly low: number;
  /** Threshold for MEDIUM level (default: 0.5) */
  readonly medium: number;
  /** Threshold for HIGH level - triggers intervention (default: 0.7) */
  readonly high: number;
}

/**
 * Monitoring frequency configuration by domain safety
 *
 * @see REQ-AA-DRIFT-005 - Safe domain detection
 */
export interface MonitoringFrequencyConfig {
  /** Frequency for safe domains (coding/writing) - default: 0.5 (50%) */
  readonly safeDomain: number;
  /** Frequency for risky domains (therapy/philosophy) - default: 1.0 (100%) */
  readonly riskyDomain: number;
}

/**
 * Phase monitoring level mapping
 *
 * @see REQ-AA-INT-002 - Workflow integration
 */
export interface PhaseMonitoringConfig {
  readonly requirements: MonitoringLevel;
  readonly design: MonitoringLevel;
  readonly tasks: MonitoringLevel;
  readonly implementation: MonitoringLevel;
  readonly done: MonitoringLevel;
}

/**
 * Logging configuration
 *
 * @see REQ-AA-EVAL-003 - Event logging
 * @see REQ-AA-NFR-002 - Privacy
 */
export interface LoggingConfig {
  /** Enable/disable logging */
  readonly enabled: boolean;
  /** Log level */
  readonly level: 'debug' | 'info' | 'warn' | 'error';
  /** Anonymize user messages in logs */
  readonly anonymize: boolean;
}

/**
 * Metrics configuration
 *
 * @see REQ-AA-INT-005 - Telemetry integration
 */
export interface MetricsConfig {
  /** Enable/disable metrics export */
  readonly enabled: boolean;
  /** OpenTelemetry endpoint (optional) */
  readonly endpoint?: string;
}

/**
 * Custom prompts configuration
 *
 * @see REQ-AA-STAB-001 - Identity reinforcement
 * @see REQ-AA-STAB-004 - Recovery prompts
 */
export interface PromptsConfig {
  /** Identity reinforcement prompt */
  readonly identityReinforcement: string;
  /** Recovery prompt for drifting sessions */
  readonly recovery: string;
}

/**
 * Complete Assistant Axis configuration
 *
 * @see REQ-AA-NFR-003 - Configuration
 */
export interface AssistantAxisConfig {
  /** Drift detection thresholds */
  readonly driftThresholds: DriftThresholds;
  /** Identity refresh interval in turns */
  readonly refreshInterval: number;
  /** Maximum interventions per session */
  readonly maxInterventions: number;
  /** Monitoring frequency by domain */
  readonly monitoringFrequency: MonitoringFrequencyConfig;
  /** Monitoring level by workflow phase */
  readonly phaseMonitoring: PhaseMonitoringConfig;
  /** Custom prompts */
  readonly prompts: PromptsConfig;
  /** Logging configuration */
  readonly logging: LoggingConfig;
  /** Metrics configuration */
  readonly metrics: MetricsConfig;
}

/**
 * Partial configuration for overrides
 */
export type PartialAssistantAxisConfig = {
  readonly [K in keyof AssistantAxisConfig]?: AssistantAxisConfig[K] extends object
    ? Partial<AssistantAxisConfig[K]>
    : AssistantAxisConfig[K];
};
