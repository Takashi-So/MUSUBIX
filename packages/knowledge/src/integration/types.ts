/**
 * @fileoverview Skill-Knowledge Bridge Types
 * Integrates skills with Knowledge Graph
 * 
 * @traceability TSK-INT-003, DES-v3.7.0 Section 9.4
 */

import type { EntityType, RelationType } from '../index.js';

/**
 * Skill entity types (extends base EntityType)
 */
export type SkillEntityType = 
  | EntityType
  | 'skill'
  | 'session'
  | 'checkpoint'
  | 'eval_result'
  | 'learned_pattern';

/**
 * Skill relation types (extends base RelationType)
 */
export type SkillRelationType =
  | RelationType
  | 'executed_by'
  | 'checkpoint_of'
  | 'evaluated_by'
  | 'learned_from'
  | 'triggered_by';

/**
 * Skill entity for storing in knowledge graph
 */
export interface SkillEntity {
  /** Unique identifier */
  id: string;
  /** Entity type */
  type: SkillEntityType;
  /** Display name */
  name: string;
  /** Description */
  description?: string;
  /** Properties specific to skill type */
  properties: SkillEntityProperties;
  /** Tags for categorization */
  tags: string[];
}

/**
 * Properties for different skill entity types
 */
export type SkillEntityProperties = 
  | SkillProperties
  | SessionProperties
  | CheckpointProperties
  | EvalResultProperties
  | LearnedPatternProperties;

/**
 * Skill definition properties
 */
export interface SkillProperties {
  kind: 'skill';
  version: string;
  author?: string;
  triggers: string[];
  commands: string[];
  successMetric?: string;
  failureMetric?: string;
}

/**
 * Session properties
 */
export interface SessionProperties {
  kind: 'session';
  startedAt: string;
  endedAt?: string;
  status: 'active' | 'completed' | 'failed' | 'abandoned';
  taskDescription?: string;
  skillsUsed: string[];
  checkpointCount: number;
}

/**
 * Checkpoint properties
 */
export interface CheckpointProperties {
  kind: 'checkpoint';
  sessionId: string;
  phase: string;
  snapshotPath: string;
  verified: boolean;
  verificationTime?: string;
}

/**
 * Evaluation result properties
 */
export interface EvalResultProperties {
  kind: 'eval_result';
  evalType: 'capability' | 'regression' | 'human';
  passAt1?: number;
  passAt3?: number;
  consecutiveAt3?: number;
  testsPassed: number;
  testsFailed: number;
  notes?: string;
}

/**
 * Learned pattern properties
 */
export interface LearnedPatternProperties {
  kind: 'learned_pattern';
  category: string;
  problem: string;
  solution: string;
  confidence: number;
  usageCount: number;
  sourceSession?: string;
}

/**
 * Skill context for queries
 */
export interface SkillQueryContext {
  /** Current skill being executed */
  currentSkill?: string;
  /** Current session ID */
  sessionId?: string;
  /** Task keywords */
  taskKeywords?: string[];
  /** File paths being worked on */
  filePaths?: string[];
  /** Error context if any */
  errorContext?: string;
  /** Max results to return */
  maxResults?: number;
}

/**
 * Context query result
 */
export interface ContextQueryResult {
  /** Relevant entities */
  entities: SkillEntity[];
  /** Relevance scores */
  scores: Map<string, number>;
  /** Query source (where the context came from) */
  querySource: 'session' | 'pattern' | 'eval' | 'related';
}

/**
 * Configuration for Skill-Knowledge Bridge
 */
export interface SkillKnowledgeBridgeConfig {
  /** Base path for knowledge store */
  basePath: string;
  /** Auto-save on store operations */
  autoSave: boolean;
  /** Maximum context entities to return */
  maxContextEntities: number;
  /** Enable semantic search (if embedding service available) */
  enableSemanticSearch: boolean;
}

/**
 * Default configuration
 */
export const DEFAULT_SKILL_KNOWLEDGE_BRIDGE_CONFIG: SkillKnowledgeBridgeConfig = {
  basePath: '~/.musubix/knowledge',
  autoSave: true,
  maxContextEntities: 20,
  enableSemanticSearch: false,
};

/**
 * Interface for Skill-Knowledge Bridge
 */
export interface SkillKnowledgeBridge {
  /**
   * Store a skill entity in the knowledge graph
   */
  storeSkillEntity(entity: SkillEntity): Promise<void>;
  
  /**
   * Get a skill entity by ID
   */
  getSkillEntity(id: string): Promise<SkillEntity | undefined>;
  
  /**
   * Delete a skill entity
   */
  deleteSkillEntity(id: string): Promise<boolean>;
  
  /**
   * Add relation between skill entities
   */
  addSkillRelation(
    sourceId: string,
    targetId: string,
    type: SkillRelationType,
    properties?: Record<string, unknown>
  ): Promise<void>;
  
  /**
   * Query context relevant to current skill execution
   */
  querySkillContext(context: SkillQueryContext): Promise<ContextQueryResult>;
  
  /**
   * Record session start
   */
  startSession(taskDescription?: string): Promise<string>;
  
  /**
   * Record session end
   */
  endSession(
    sessionId: string,
    status: SessionProperties['status'],
    skillsUsed: string[]
  ): Promise<void>;
  
  /**
   * Record checkpoint
   */
  recordCheckpoint(
    sessionId: string,
    phase: string,
    snapshotPath: string
  ): Promise<string>;
  
  /**
   * Record evaluation result
   */
  recordEvalResult(
    sessionId: string,
    evalType: EvalResultProperties['evalType'],
    results: Omit<EvalResultProperties, 'kind' | 'evalType'>
  ): Promise<string>;
  
  /**
   * Get session history
   */
  getSessionHistory(limit?: number): Promise<SkillEntity[]>;
  
  /**
   * Get related entities
   */
  getRelatedEntities(
    entityId: string,
    relationTypes?: SkillRelationType[],
    depth?: number
  ): Promise<SkillEntity[]>;
  
  /**
   * Get statistics
   */
  getStatistics(): Promise<SkillKnowledgeStatistics>;
}

/**
 * Statistics for skill knowledge
 */
export interface SkillKnowledgeStatistics {
  /** Total entities */
  totalEntities: number;
  /** Entities by type */
  byType: Record<SkillEntityType, number>;
  /** Total sessions */
  totalSessions: number;
  /** Completed sessions */
  completedSessions: number;
  /** Failed sessions */
  failedSessions: number;
  /** Total checkpoints */
  totalCheckpoints: number;
  /** Total learned patterns */
  totalLearnedPatterns: number;
  /** Average session duration (ms) */
  averageSessionDuration?: number;
}
