/**
 * @fileoverview Skill-Knowledge Bridge Implementation
 * Integrates skills with Knowledge Graph
 * 
 * @traceability TSK-INT-003, DES-v3.7.0 Section 9.4
 */

import type { Entity, EntityType, Relation, RelationType } from '../index.js';
import { createKnowledgeStore } from '../index.js';
import {
  DEFAULT_SKILL_KNOWLEDGE_BRIDGE_CONFIG,
} from './types.js';
import type {
  SkillKnowledgeBridge,
  SkillKnowledgeBridgeConfig,
  SkillEntity,
  SkillEntityType,
  SkillRelationType,
  SkillQueryContext,
  ContextQueryResult,
  SessionProperties,
  CheckpointProperties,
  EvalResultProperties,
  LearnedPatternProperties,
  SkillKnowledgeStatistics,
} from './types.js';

/**
 * Create a Skill-Knowledge Bridge instance
 */
export function createSkillKnowledgeBridge(
  config: Partial<SkillKnowledgeBridgeConfig> = {}
): SkillKnowledgeBridge {
  const fullConfig: SkillKnowledgeBridgeConfig = {
    ...DEFAULT_SKILL_KNOWLEDGE_BRIDGE_CONFIG,
    ...config,
  };

  // Resolve home directory
  const basePath = fullConfig.basePath.replace(/^~/, process.env.HOME ?? '');
  const store = createKnowledgeStore(basePath);

  /**
   * Generate unique ID with prefix
   */
  function generateId(prefix: string): string {
    const timestamp = Date.now().toString(36);
    const random = Math.random().toString(36).substring(2, 8);
    return `${prefix}-${timestamp}-${random}`;
  }

  /**
   * Convert SkillEntity to base Entity
   */
  function toBaseEntity(skill: SkillEntity): Entity {
    // Map SkillEntityType to EntityType (use 'code' as fallback for skill-specific types)
    const baseType: EntityType = 
      ['requirement', 'design', 'task', 'code', 'decision', 'pattern', 'constraint'].includes(skill.type as string)
        ? (skill.type as EntityType)
        : 'code'; // Use 'code' as generic fallback

    return {
      id: skill.id,
      type: baseType,
      name: skill.name,
      description: skill.description,
      properties: {
        ...skill.properties,
        skillEntityType: skill.type, // Preserve original type
      },
      tags: skill.tags,
      createdAt: '',
      updatedAt: '',
    };
  }

  /**
   * Convert base Entity to SkillEntity
   */
  function fromBaseEntity(entity: Entity): SkillEntity {
    const skillType = (entity.properties.skillEntityType as SkillEntityType) ?? entity.type;
    // eslint-disable-next-line @typescript-eslint/no-unused-vars
    const { skillEntityType, ...properties } = entity.properties;

    return {
      id: entity.id,
      type: skillType,
      name: entity.name,
      description: entity.description,
      properties: properties as unknown as SkillEntity['properties'],
      tags: entity.tags,
    };
  }

  /**
   * Calculate relevance score for context query
   */
  function calculateRelevance(entity: SkillEntity, context: SkillQueryContext): number {
    let score = 0;

    // Session match
    if (context.sessionId && entity.properties.kind === 'session') {
      if (entity.id === context.sessionId) {
        score += 0.5;
      }
    }

    // Skill match
    if (context.currentSkill && entity.properties.kind === 'skill') {
      if (entity.name.toLowerCase().includes(context.currentSkill.toLowerCase())) {
        score += 0.4;
      }
    }

    // Keyword match
    if (context.taskKeywords && context.taskKeywords.length > 0) {
      const entityText = `${entity.name} ${entity.description ?? ''} ${JSON.stringify(entity.properties)}`.toLowerCase();
      const matchedKeywords = context.taskKeywords.filter(k => 
        entityText.includes(k.toLowerCase())
      );
      score += 0.1 * matchedKeywords.length;
    }

    // Error context match for patterns
    if (context.errorContext && entity.properties.kind === 'learned_pattern') {
      const patternProps = entity.properties as LearnedPatternProperties;
      if (patternProps.problem.toLowerCase().includes(context.errorContext.toLowerCase())) {
        score += 0.6;
      }
    }

    // Recency boost for sessions
    if (entity.properties.kind === 'session') {
      const props = entity.properties as SessionProperties;
      const age = Date.now() - new Date(props.startedAt).getTime();
      const dayMs = 24 * 60 * 60 * 1000;
      if (age < dayMs) {
        score += 0.2;
      } else if (age < 7 * dayMs) {
        score += 0.1;
      }
    }

    return Math.min(1, score);
  }

  return {
    async storeSkillEntity(entity: SkillEntity): Promise<void> {
      await store.putEntity(toBaseEntity(entity));
      if (fullConfig.autoSave) {
        await store.save();
      }
    },

    async getSkillEntity(id: string): Promise<SkillEntity | undefined> {
      const entity = await store.getEntity(id);
      return entity ? fromBaseEntity(entity) : undefined;
    },

    async deleteSkillEntity(id: string): Promise<boolean> {
      const result = await store.deleteEntity(id);
      if (result && fullConfig.autoSave) {
        await store.save();
      }
      return result;
    },

    async addSkillRelation(
      sourceId: string,
      targetId: string,
      type: SkillRelationType,
      properties?: Record<string, unknown>
    ): Promise<void> {
      // Map to base relation type
      const baseType: RelationType = 
        ['implements', 'depends_on', 'traces_to', 'related_to', 'derives_from', 'conflicts_with'].includes(type)
          ? (type as RelationType)
          : 'related_to';

      const relationId = `rel-${Date.now().toString(36)}-${Math.random().toString(36).substring(2, 8)}`;
      const relation: Relation = {
        id: relationId,
        source: sourceId,
        target: targetId,
        type: baseType,
        properties: {
          ...properties,
          skillRelationType: type, // Preserve original type
        },
      };

      await store.addRelation(relation);
      if (fullConfig.autoSave) {
        await store.save();
      }
    },

    async querySkillContext(context: SkillQueryContext): Promise<ContextQueryResult> {
      const maxResults = context.maxResults ?? fullConfig.maxContextEntities;
      const allEntities = await store.query({});
      
      const scored: Array<{ entity: SkillEntity; score: number }> = [];
      
      for (const entity of allEntities) {
        const skillEntity = fromBaseEntity(entity);
        const score = calculateRelevance(skillEntity, context);
        
        if (score > 0) {
          scored.push({ entity: skillEntity, score });
        }
      }

      // Sort by score and limit
      scored.sort((a, b) => b.score - a.score);
      const limited = scored.slice(0, maxResults);

      // Determine query source
      let querySource: ContextQueryResult['querySource'] = 'related';
      if (context.sessionId) {
        querySource = 'session';
      } else if (context.errorContext) {
        querySource = 'pattern';
      }

      return {
        entities: limited.map(s => s.entity),
        scores: new Map(limited.map(s => [s.entity.id, s.score])),
        querySource,
      };
    },

    async startSession(taskDescription?: string): Promise<string> {
      const sessionId = generateId('session');
      const now = new Date().toISOString();

      const session: SkillEntity = {
        id: sessionId,
        type: 'session',
        name: `Session ${sessionId}`,
        description: taskDescription,
        properties: {
          kind: 'session',
          startedAt: now,
          status: 'active',
          taskDescription,
          skillsUsed: [],
          checkpointCount: 0,
        } as SessionProperties,
        tags: ['session', 'active'],
      };

      await this.storeSkillEntity(session);
      return sessionId;
    },

    async endSession(
      sessionId: string,
      status: SessionProperties['status'],
      skillsUsed: string[]
    ): Promise<void> {
      const session = await this.getSkillEntity(sessionId);
      if (!session) {
        throw new Error(`Session not found: ${sessionId}`);
      }

      const now = new Date().toISOString();
      const props = session.properties as SessionProperties;

      const updated: SkillEntity = {
        ...session,
        properties: {
          ...props,
          endedAt: now,
          status,
          skillsUsed,
        },
        tags: session.tags.filter(t => t !== 'active').concat(status),
      };

      await this.storeSkillEntity(updated);
    },

    async recordCheckpoint(
      sessionId: string,
      phase: string,
      snapshotPath: string
    ): Promise<string> {
      const checkpointId = generateId('checkpoint');

      const checkpoint: SkillEntity = {
        id: checkpointId,
        type: 'checkpoint',
        name: `Checkpoint: ${phase}`,
        description: `Checkpoint at phase ${phase} for session ${sessionId}`,
        properties: {
          kind: 'checkpoint',
          sessionId,
          phase,
          snapshotPath,
          verified: false,
        } as CheckpointProperties,
        tags: ['checkpoint', phase],
      };

      await this.storeSkillEntity(checkpoint);
      await this.addSkillRelation(checkpointId, sessionId, 'checkpoint_of');

      // Update session checkpoint count
      const session = await this.getSkillEntity(sessionId);
      if (session) {
        const props = session.properties as SessionProperties;
        props.checkpointCount += 1;
        await this.storeSkillEntity(session);
      }

      return checkpointId;
    },

    async recordEvalResult(
      sessionId: string,
      evalType: EvalResultProperties['evalType'],
      results: Omit<EvalResultProperties, 'kind' | 'evalType'>
    ): Promise<string> {
      const evalId = generateId('eval');

      const evalResult: SkillEntity = {
        id: evalId,
        type: 'eval_result',
        name: `${evalType} Evaluation`,
        description: `${evalType} evaluation result for session ${sessionId}`,
        properties: {
          kind: 'eval_result',
          evalType,
          ...results,
        } as EvalResultProperties,
        tags: ['eval', evalType],
      };

      await this.storeSkillEntity(evalResult);
      await this.addSkillRelation(evalId, sessionId, 'evaluated_by');

      return evalId;
    },

    async getSessionHistory(limit: number = 10): Promise<SkillEntity[]> {
      const allEntities = await store.query({});
      
      const sessions = allEntities
        .map(fromBaseEntity)
        .filter(e => e.type === 'session')
        .sort((a, b) => {
          const aTime = (a.properties as SessionProperties).startedAt;
          const bTime = (b.properties as SessionProperties).startedAt;
          return new Date(bTime).getTime() - new Date(aTime).getTime();
        })
        .slice(0, limit);

      return sessions;
    },

    async getRelatedEntities(
      entityId: string,
      relationTypes?: SkillRelationType[],
      depth: number = 1
    ): Promise<SkillEntity[]> {
      const related = await store.traverse(entityId, {
        direction: 'both',
        depth: depth,
      });

      const entities = related.map(fromBaseEntity);

      if (relationTypes && relationTypes.length > 0) {
        // Filter would need relation data - for now return all
        return entities;
      }

      return entities;
    },

    async getStatistics(): Promise<SkillKnowledgeStatistics> {
      const allEntities = await store.query({});
      const skillEntities = allEntities.map(fromBaseEntity);

      const byType: Record<string, number> = {};
      let completedSessions = 0;
      let failedSessions = 0;
      let totalCheckpoints = 0;
      let totalLearnedPatterns = 0;
      let totalSessionDuration = 0;
      let sessionCount = 0;

      for (const entity of skillEntities) {
        byType[entity.type] = (byType[entity.type] ?? 0) + 1;

        if (entity.type === 'session') {
          const props = entity.properties as SessionProperties;
          sessionCount++;
          
          if (props.status === 'completed') completedSessions++;
          if (props.status === 'failed') failedSessions++;
          
          if (props.endedAt) {
            totalSessionDuration += 
              new Date(props.endedAt).getTime() - new Date(props.startedAt).getTime();
          }
        } else if (entity.type === 'checkpoint') {
          totalCheckpoints++;
        } else if (entity.type === 'learned_pattern') {
          totalLearnedPatterns++;
        }
      }

      return {
        totalEntities: skillEntities.length,
        byType: byType as Record<SkillEntityType, number>,
        totalSessions: sessionCount,
        completedSessions,
        failedSessions,
        totalCheckpoints,
        totalLearnedPatterns,
        averageSessionDuration: sessionCount > 0 
          ? totalSessionDuration / sessionCount 
          : undefined,
      };
    },
  };
}

/**
 * Format session as markdown for display
 */
export function formatSessionAsMarkdown(session: SkillEntity): string {
  if (session.type !== 'session') {
    throw new Error('Entity is not a session');
  }

  const props = session.properties as SessionProperties;
  const lines = [
    `# 📋 Session: ${session.id}`,
    '',
    `**Status**: ${props.status}`,
    `**Started**: ${props.startedAt}`,
  ];

  if (props.endedAt) {
    lines.push(`**Ended**: ${props.endedAt}`);
    const duration = new Date(props.endedAt).getTime() - new Date(props.startedAt).getTime();
    const minutes = Math.round(duration / 60000);
    lines.push(`**Duration**: ${minutes} minutes`);
  }

  if (props.taskDescription) {
    lines.push('', '## Task', props.taskDescription);
  }

  if (props.skillsUsed.length > 0) {
    lines.push('', '## Skills Used');
    props.skillsUsed.forEach(s => lines.push(`- ${s}`));
  }

  lines.push('', `**Checkpoints**: ${props.checkpointCount}`);

  return lines.join('\n');
}

/**
 * Format context query result as markdown
 */
export function formatContextAsMarkdown(result: ContextQueryResult): string {
  if (result.entities.length === 0) {
    return '📝 No relevant context found.\n';
  }

  const lines = [
    `# 🔍 Context Query Result (${result.querySource})`,
    '',
    `Found ${result.entities.length} relevant entities:`,
    '',
  ];

  for (const entity of result.entities) {
    const score = result.scores.get(entity.id) ?? 0;
    lines.push(`## ${entity.name}`);
    lines.push(`- **Type**: ${entity.type}`);
    lines.push(`- **Relevance**: ${(score * 100).toFixed(1)}%`);
    if (entity.description) {
      lines.push(`- **Description**: ${entity.description}`);
    }
    lines.push('');
  }

  return lines.join('\n');
}
