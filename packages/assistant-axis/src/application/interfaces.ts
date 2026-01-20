/**
 * Application layer interfaces
 *
 * @see REQ-AA-DRIFT-001 - Drift detection
 * @see REQ-AA-DRIFT-002 - Domain classification
 * @see REQ-AA-STAB-001 - Identity reinforcement
 */

import type { DriftScore } from '../domain/value-objects/DriftScore.js';
import type { ConversationDomain, DomainType } from '../domain/value-objects/ConversationDomain.js';
import type { DetectedTrigger } from '../domain/value-objects/TriggerPattern.js';
import type { ReinforcementPrompt, ReinforcementType } from '../domain/value-objects/ReinforcementPrompt.js';
import type { PersonaState } from '../domain/entities/PersonaState.js';
import type { DriftEvent } from '../domain/entities/DriftEvent.js';

/**
 * Drift analysis result
 */
export interface DriftAnalysisResult {
  /** Calculated drift score */
  readonly score: DriftScore;
  /** Detected triggers */
  readonly triggers: readonly DetectedTrigger[];
  /** Whether intervention is recommended */
  readonly interventionRecommended: boolean;
  /** Recommended prompt if intervention needed */
  readonly recommendedPrompt?: ReinforcementPrompt;
}

/**
 * Domain classification result
 */
export interface DomainClassificationResult {
  /** Classified domain */
  readonly domain: ConversationDomain;
  /** All scores per domain type */
  readonly scores: Readonly<Record<DomainType, number>>;
  /** Whether domain changed from previous */
  readonly domainChanged: boolean;
}

/**
 * Identity reinforcement result
 */
export interface ReinforcementResult {
  /** Selected reinforcement prompt */
  readonly prompt: ReinforcementPrompt;
  /** Whether reinforcement should be applied */
  readonly shouldApply: boolean;
  /** Reason for the decision */
  readonly reason: string;
}

/**
 * Monitoring result
 */
export interface MonitoringResult {
  /** Updated persona state */
  readonly state: PersonaState;
  /** Analysis result */
  readonly analysis: DriftAnalysisResult;
  /** Domain classification */
  readonly classification: DomainClassificationResult;
  /** Reinforcement result (if applicable) */
  readonly reinforcement?: ReinforcementResult;
  /** Events generated */
  readonly events: readonly DriftEvent[];
}

/**
 * IDriftAnalyzer interface
 *
 * Analyzes messages for persona drift indicators
 */
export interface IDriftAnalyzer {
  /**
   * Analyze a message for drift indicators
   * @param message - User message to analyze
   * @param state - Current persona state
   * @returns Analysis result
   */
  analyze(message: string, state: PersonaState): DriftAnalysisResult;

  /**
   * Calculate base drift score from triggers
   * @param triggers - Detected triggers
   * @returns Base drift score value
   */
  calculateBaseScore(triggers: readonly DetectedTrigger[]): number;

  /**
   * Apply domain modifier to drift score
   * @param baseScore - Base drift score
   * @param domain - Conversation domain
   * @returns Modified drift score
   */
  applyDomainModifier(baseScore: number, domain: ConversationDomain): number;
}

/**
 * IDomainClassifier interface
 *
 * Classifies conversation domain
 */
export interface IDomainClassifier {
  /**
   * Classify message domain
   * @param message - User message
   * @returns Classification result
   */
  classify(message: string): DomainClassificationResult;

  /**
   * Calculate domain scores for a message
   * @param message - User message
   * @returns Scores per domain type
   */
  calculateScores(message: string): Record<DomainType, number>;
}

/**
 * IIdentityManager interface
 *
 * Manages identity reinforcement
 */
export interface IIdentityManager {
  /**
   * Determine if reinforcement is needed
   * @param state - Current persona state
   * @param analysis - Drift analysis result
   * @returns Reinforcement result
   */
  determineReinforcement(
    state: PersonaState,
    analysis: DriftAnalysisResult
  ): ReinforcementResult;

  /**
   * Get reinforcement prompt by type
   * @param type - Reinforcement type
   * @returns Reinforcement prompt
   */
  getPrompt(type: ReinforcementType): ReinforcementPrompt;

  /**
   * Check if reinforcement limit reached
   * @param state - Current persona state
   * @returns Whether limit is reached
   */
  isLimitReached(state: PersonaState): boolean;
}

/**
 * IPersonaMonitor interface
 *
 * Main monitoring service that orchestrates other services
 */
export interface IPersonaMonitor {
  /**
   * Process a user message and monitor for drift
   * @param sessionId - Session identifier
   * @param message - User message
   * @param workflowPhase - Current workflow phase
   * @returns Monitoring result
   */
  process(
    sessionId: string,
    message: string,
    workflowPhase?: string
  ): MonitoringResult;

  /**
   * Get current state for a session
   * @param sessionId - Session identifier
   * @returns Current persona state or undefined
   */
  getState(sessionId: string): PersonaState | undefined;

  /**
   * Start a new session
   * @param sessionId - Session identifier
   * @param initialDomain - Initial conversation domain
   */
  startSession(sessionId: string, initialDomain?: DomainType): void;

  /**
   * End a session
   * @param sessionId - Session identifier
   */
  endSession(sessionId: string): void;

  /**
   * Handle workflow phase change
   * @param sessionId - Session identifier
   * @param newPhase - New workflow phase
   */
  onPhaseChange(sessionId: string, newPhase: string): void;
}

/**
 * IEventLogger interface
 *
 * Logs drift events for audit and analysis
 */
export interface IEventLogger {
  /**
   * Log an event
   * @param event - Drift event to log
   */
  log(event: DriftEvent): void;

  /**
   * Get events for a session
   * @param sessionId - Session identifier
   * @returns Events for the session
   */
  getSessionEvents(sessionId: string): readonly DriftEvent[];

  /**
   * Get all events
   * @returns All logged events
   */
  getAllEvents(): readonly DriftEvent[];

  /**
   * Export events
   * @param format - Export format
   * @returns Exported data
   */
  export(format: 'json' | 'csv'): string;
}

/**
 * IConfigLoader interface
 *
 * Loads and manages configuration
 */
export interface IConfigLoader {
  /**
   * Load configuration
   * @param path - Optional path to config file
   * @returns Loaded configuration
   */
  load(path?: string): Promise<void>;

  /**
   * Get current configuration
   * @returns Current configuration
   */
  get<T>(key: string): T | undefined;

  /**
   * Check if configuration is loaded
   * @returns Whether config is loaded
   */
  isLoaded(): boolean;
}

/**
 * IWorkflowIntegration interface
 *
 * Integration with MUSUBIX workflow engine
 */
export interface IWorkflowIntegration {
  /**
   * Register phase change listener
   * @param callback - Callback for phase changes
   */
  onPhaseChange(callback: (phase: string) => void): void;

  /**
   * Get current workflow phase
   * @returns Current phase name
   */
  getCurrentPhase(): string | undefined;

  /**
   * Check if monitoring is enabled for phase
   * @param phase - Workflow phase name
   * @returns Whether monitoring is enabled
   */
  isMonitoringEnabled(phase: string): boolean;

  /**
   * Get monitoring frequency for phase
   * @param phase - Workflow phase name
   * @returns Monitoring frequency (0.0 - 1.0)
   */
  getMonitoringFrequency(phase: string): number;
}

/**
 * IMetricsExporter interface
 *
 * Exports metrics for analysis
 */
export interface IMetricsExporter {
  /**
   * Export session metrics
   * @param sessionId - Session identifier
   * @param format - Export format
   * @returns Exported metrics
   */
  exportSession(sessionId: string, format: 'json' | 'markdown'): string;

  /**
   * Export aggregate metrics
   * @param format - Export format
   * @returns Exported metrics
   */
  exportAggregate(format: 'json' | 'markdown'): string;

  /**
   * Get session summary
   * @param sessionId - Session identifier
   * @returns Session summary metrics
   */
  getSessionSummary(sessionId: string): SessionMetricsSummary;
}

/**
 * Session metrics summary
 */
export interface SessionMetricsSummary {
  readonly sessionId: string;
  readonly totalTurns: number;
  readonly averageDrift: number;
  readonly maxDrift: number;
  readonly interventionCount: number;
  readonly dominantDomain: DomainType;
  readonly driftTrend: 'stable' | 'increasing' | 'decreasing';
}
