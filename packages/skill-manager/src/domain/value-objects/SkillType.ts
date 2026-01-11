/**
 * SkillType Value Object
 * 
 * Represents the type of a skill
 * 
 * @see REQ-SKILL-001 - Skill Loading
 * @see DES-SKILL-001 - SkillManager
 */

/**
 * Skill type enum
 */
export type SkillType = 
  | 'file-operation'     // File read/write/edit
  | 'code-analysis'      // AST parsing, static analysis
  | 'code-generation'    // Code synthesis
  | 'requirements'       // Requirements analysis (EARS)
  | 'design'             // Design generation (C4)
  | 'testing'            // Test generation
  | 'knowledge-graph'    // Knowledge Store operations (@musubix/knowledge)
  | 'orchestration'      // Agent orchestration
  | 'security'           // Security analysis
  | 'documentation'      // Documentation generation
  | 'custom';            // Custom skills

/**
 * Skill type metadata
 */
export interface SkillTypeMetadata {
  readonly type: SkillType;
  readonly label: string;
  readonly description: string;
  readonly icon: string;
}

/**
 * Skill type definitions
 */
export const SKILL_TYPES: ReadonlyMap<SkillType, SkillTypeMetadata> = new Map([
  ['file-operation', {
    type: 'file-operation',
    label: 'ファイル操作',
    description: 'ファイルの読み書き・編集',
    icon: '📁',
  }],
  ['code-analysis', {
    type: 'code-analysis',
    label: 'コード分析',
    description: 'AST解析・静的解析',
    icon: '🔍',
  }],
  ['code-generation', {
    type: 'code-generation',
    label: 'コード生成',
    description: 'コード合成・スケルトン生成',
    icon: '⚙️',
  }],
  ['requirements', {
    type: 'requirements',
    label: '要件分析',
    description: 'EARS形式の要件分析',
    icon: '📋',
  }],
  ['design', {
    type: 'design',
    label: '設計',
    description: 'C4モデル設計',
    icon: '🏗️',
  }],
  ['testing', {
    type: 'testing',
    label: 'テスト',
    description: 'テスト生成・実行',
    icon: '🧪',
  }],
  ['knowledge-graph', {
    type: 'knowledge-graph',
    label: '知識グラフ',
    description: '@musubix/knowledge グラフ操作',
    icon: '🕸️',
  }],
  ['orchestration', {
    type: 'orchestration',
    label: 'オーケストレーション',
    description: 'エージェント調整',
    icon: '🎭',
  }],
  ['security', {
    type: 'security',
    label: 'セキュリティ',
    description: 'セキュリティ分析',
    icon: '🔒',
  }],
  ['documentation', {
    type: 'documentation',
    label: 'ドキュメント',
    description: 'ドキュメント生成',
    icon: '📝',
  }],
  ['custom', {
    type: 'custom',
    label: 'カスタム',
    description: 'カスタムスキル',
    icon: '🔧',
  }],
]);

/**
 * Get skill type metadata
 * 
 * @param type - Skill type
 * @returns Skill type metadata
 */
export function getSkillTypeMetadata(type: SkillType): SkillTypeMetadata {
  const metadata = SKILL_TYPES.get(type);
  if (!metadata) {
    throw new Error(`Invalid skill type: ${type}`);
  }
  return metadata;
}

/**
 * Get all skill types
 * 
 * @returns All skill types
 */
export function getAllSkillTypes(): SkillType[] {
  return Array.from(SKILL_TYPES.keys());
}

/**
 * Get skill type icon
 * 
 * @param type - Skill type
 * @returns Emoji icon
 */
export function getSkillTypeIcon(type: SkillType): string {
  return getSkillTypeMetadata(type).icon;
}
