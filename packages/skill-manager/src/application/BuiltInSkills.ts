/**
 * BuiltInSkills - Pre-defined skills
 * 
 * Built-in skills for MUSUBIX
 * 
 * @see REQ-SKILL-001 - Skill Loading
 */

import {
  type Skill,
  type SkillContext,
  type SkillResult,
  createSkill,
  createSkillMetadata,
  createSkillParameter,
  createNoOpResult,
} from '../domain/index.js';

/**
 * Create requirements analysis skill
 * 
 * @returns Skill
 */
export function createRequirementsAnalysisSkill(): Skill {
  const metadata = createSkillMetadata({
    id: 'SKILL-REQ-EARS-001',
    name: 'EARS Requirements Analysis',
    description: '自然言語をEARS形式の要件に変換',
    type: 'requirements',
    parameters: [
      createSkillParameter({
        name: 'input',
        type: 'string',
        required: true,
        description: '分析する自然言語テキスト',
      }),
      createSkillParameter({
        name: 'outputFormat',
        type: 'string',
        required: false,
        description: '出力形式 (markdown, json)',
        default: 'markdown',
      }),
    ],
    tags: ['ears', 'requirements', 'analysis'],
  });
  
  const executor = async (context: SkillContext): Promise<SkillResult> => {
    const input = context.parameters.input as string;
    // Placeholder implementation
    return createNoOpResult(`Analyzed requirements from: ${input.substring(0, 50)}...`);
  };
  
  return createSkill(metadata, executor);
}

/**
 * Create design generation skill
 * 
 * @returns Skill
 */
export function createDesignGenerationSkill(): Skill {
  const metadata = createSkillMetadata({
    id: 'SKILL-DES-C4-001',
    name: 'C4 Design Generation',
    description: '要件からC4モデル設計を生成',
    type: 'design',
    parameters: [
      createSkillParameter({
        name: 'requirements',
        type: 'array',
        required: true,
        description: '設計対象の要件リスト',
      }),
      createSkillParameter({
        name: 'level',
        type: 'string',
        required: false,
        description: 'C4レベル (context, container, component, code)',
        default: 'component',
      }),
    ],
    tags: ['c4', 'design', 'generation'],
  });
  
  const executor = async (context: SkillContext): Promise<SkillResult> => {
    const requirements = context.parameters.requirements as unknown[];
    return createNoOpResult(`Generated design for ${requirements.length} requirements`);
  };
  
  return createSkill(metadata, executor);
}

/**
 * Create code analysis skill
 * 
 * @returns Skill
 */
export function createCodeAnalysisSkill(): Skill {
  const metadata = createSkillMetadata({
    id: 'SKILL-CODE-ANALYZE-001',
    name: 'Code Analysis',
    description: 'コードの静的解析を実行',
    type: 'code-analysis',
    parameters: [
      createSkillParameter({
        name: 'filePath',
        type: 'string',
        required: true,
        description: '解析対象のファイルパス',
      }),
      createSkillParameter({
        name: 'analysisType',
        type: 'string',
        required: false,
        description: '解析タイプ (ast, complexity, dependencies)',
        default: 'ast',
      }),
    ],
    tags: ['code', 'analysis', 'ast'],
  });
  
  const executor = async (context: SkillContext): Promise<SkillResult> => {
    const filePath = context.parameters.filePath as string;
    return createNoOpResult(`Analyzed code at: ${filePath}`);
  };
  
  return createSkill(metadata, executor);
}

/**
 * Create test generation skill
 * 
 * @returns Skill
 */
export function createTestGenerationSkill(): Skill {
  const metadata = createSkillMetadata({
    id: 'SKILL-TEST-GEN-001',
    name: 'Test Generation',
    description: 'コードからテストを自動生成',
    type: 'testing',
    parameters: [
      createSkillParameter({
        name: 'sourceCode',
        type: 'string',
        required: true,
        description: 'テスト対象のソースコード',
      }),
      createSkillParameter({
        name: 'framework',
        type: 'string',
        required: false,
        description: 'テストフレームワーク (vitest, jest)',
        default: 'vitest',
      }),
    ],
    tags: ['test', 'generation', 'vitest'],
  });
  
  const executor = async (context: SkillContext): Promise<SkillResult> => {
    const sourceCode = context.parameters.sourceCode as string;
    return createNoOpResult(`Generated tests for code with ${sourceCode.length} characters`);
  };
  
  return createSkill(metadata, executor);
}

/**
 * Create knowledge graph query skill
 * 
 * @returns Skill
 */
export function createKnowledgeGraphQuerySkill(): Skill {
  const metadata = createSkillMetadata({
    id: 'SKILL-KG-QUERY-001',
    name: 'Knowledge Graph Query',
    description: 'YATA知識グラフへのクエリ実行',
    type: 'knowledge-graph',
    parameters: [
      createSkillParameter({
        name: 'query',
        type: 'string',
        required: true,
        description: 'SPARQLクエリまたは自然言語クエリ',
      }),
      createSkillParameter({
        name: 'namespace',
        type: 'string',
        required: false,
        description: '検索対象の名前空間',
        default: 'default',
      }),
    ],
    tags: ['yata', 'knowledge-graph', 'query'],
  });
  
  const executor = async (context: SkillContext): Promise<SkillResult> => {
    const query = context.parameters.query as string;
    return createNoOpResult(`Queried knowledge graph: ${query.substring(0, 50)}...`);
  };
  
  return createSkill(metadata, executor);
}

/**
 * Get all built-in skills
 * 
 * @returns Array of built-in skills
 */
export function getBuiltInSkills(): Skill[] {
  return [
    createRequirementsAnalysisSkill(),
    createDesignGenerationSkill(),
    createCodeAnalysisSkill(),
    createTestGenerationSkill(),
    createKnowledgeGraphQuerySkill(),
  ];
}

/**
 * Register all built-in skills with a manager
 * 
 * @param registerFn - Registration function
 */
export function registerBuiltInSkills(
  registerFn: (skill: Skill) => void
): void {
  for (const skill of getBuiltInSkills()) {
    registerFn(skill);
  }
}
