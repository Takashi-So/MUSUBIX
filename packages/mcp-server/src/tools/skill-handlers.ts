/**
 * Skill Tool Handlers
 * 
 * Handlers for skill_* MCP tools
 * 
 * @see TSK-MCP-003 - skill_* MCP Tools
 * @see REQ-SKILL-001 - Skill Loading
 */

import type {
  SkillListInput,
  SkillExecuteInput,
  SkillValidateInput,
  SkillInfoInput,
  SkillRegisterInput,
} from './skill-tools.js';

/**
 * Skill type labels
 */
const SKILL_TYPE_LABELS: Record<string, { label: string; icon: string }> = {
  'file-operation': { label: 'ファイル操作', icon: '📁' },
  'code-analysis': { label: 'コード分析', icon: '🔍' },
  'code-generation': { label: 'コード生成', icon: '⚙️' },
  'requirements': { label: '要件分析', icon: '📋' },
  'design': { label: '設計', icon: '🏗️' },
  'testing': { label: 'テスト', icon: '🧪' },
  'knowledge-graph': { label: '知識グラフ', icon: '🕸️' },
  'orchestration': { label: 'オーケストレーション', icon: '🎭' },
  'security': { label: 'セキュリティ', icon: '🔒' },
  'documentation': { label: 'ドキュメント', icon: '📝' },
  'custom': { label: 'カスタム', icon: '🔧' },
};

/**
 * Built-in skills
 */
interface BuiltInSkill {
  id: string;
  name: string;
  description: string;
  type: string;
  enabled: boolean;
  parameters: Array<{
    name: string;
    type: string;
    required: boolean;
    description: string;
  }>;
  tags: string[];
}

const builtInSkills: BuiltInSkill[] = [
  {
    id: 'SKILL-REQ-EARS-001',
    name: 'EARS Requirements Analysis',
    description: '自然言語をEARS形式の要件に変換',
    type: 'requirements',
    enabled: true,
    parameters: [
      { name: 'input', type: 'string', required: true, description: '分析する自然言語テキスト' },
      { name: 'outputFormat', type: 'string', required: false, description: '出力形式 (markdown, json)' },
    ],
    tags: ['ears', 'requirements', 'analysis'],
  },
  {
    id: 'SKILL-DES-C4-001',
    name: 'C4 Design Generation',
    description: '要件からC4モデル設計を生成',
    type: 'design',
    enabled: true,
    parameters: [
      { name: 'requirements', type: 'array', required: true, description: '設計対象の要件リスト' },
      { name: 'level', type: 'string', required: false, description: 'C4レベル (context, container, component, code)' },
    ],
    tags: ['c4', 'design', 'generation'],
  },
  {
    id: 'SKILL-CODE-ANALYZE-001',
    name: 'Code Analysis',
    description: 'コードの静的解析を実行',
    type: 'code-analysis',
    enabled: true,
    parameters: [
      { name: 'filePath', type: 'string', required: true, description: '解析対象のファイルパス' },
      { name: 'analysisType', type: 'string', required: false, description: '解析タイプ (ast, complexity, dependencies)' },
    ],
    tags: ['code', 'analysis', 'ast'],
  },
  {
    id: 'SKILL-TEST-GEN-001',
    name: 'Test Generation',
    description: 'コードからテストを自動生成',
    type: 'testing',
    enabled: true,
    parameters: [
      { name: 'sourceCode', type: 'string', required: true, description: 'テスト対象のソースコード' },
      { name: 'framework', type: 'string', required: false, description: 'テストフレームワーク (vitest, jest)' },
    ],
    tags: ['test', 'generation', 'vitest'],
  },
  {
    id: 'SKILL-KG-QUERY-001',
    name: 'Knowledge Graph Query',
    description: 'Knowledge Graph へのクエリ実行',
    type: 'knowledge-graph',
    enabled: true,
    parameters: [
      { name: 'query', type: 'string', required: true, description: 'クエリ文字列' },
      { name: 'namespace', type: 'string', required: false, description: '検索対象の名前空間' },
    ],
    tags: ['knowledge-graph', 'query'],
  },
];

// Custom skills storage
const customSkills: BuiltInSkill[] = [];

/**
 * Handle skill_list tool call
 */
export async function handleSkillList(input: SkillListInput): Promise<{
  content: Array<{ type: 'text'; text: string }>;
}> {
  let skills = [...builtInSkills, ...customSkills];
  
  // Filter by type
  if (input.type) {
    skills = skills.filter(s => s.type === input.type);
  }
  
  // Filter by enabled only
  if (input.enabledOnly !== false) {
    skills = skills.filter(s => s.enabled);
  }
  
  // Filter by tags
  if (input.tags && input.tags.length > 0) {
    skills = skills.filter(s => 
      input.tags!.every(tag => s.tags.includes(tag))
    );
  }
  
  // Filter by query
  if (input.query) {
    const query = input.query.toLowerCase();
    skills = skills.filter(s =>
      s.name.toLowerCase().includes(query) ||
      s.description.toLowerCase().includes(query) ||
      s.tags.some(t => t.toLowerCase().includes(query))
    );
  }
  
  // Group by type
  const grouped: Record<string, BuiltInSkill[]> = {};
  for (const skill of skills) {
    if (!grouped[skill.type]) {
      grouped[skill.type] = [];
    }
    grouped[skill.type].push(skill);
  }
  
  let responseText = `## 📚 スキル一覧

**総数**: ${skills.length}件
`;

  if (input.type) {
    responseText += `**フィルタ**: タイプ = ${input.type}\n`;
  }
  if (input.tags && input.tags.length > 0) {
    responseText += `**フィルタ**: タグ = ${input.tags.join(', ')}\n`;
  }
  if (input.query) {
    responseText += `**フィルタ**: 検索 = "${input.query}"\n`;
  }

  responseText += '\n';

  for (const [type, typeSkills] of Object.entries(grouped)) {
    const typeInfo = SKILL_TYPE_LABELS[type] || { label: type, icon: '❓' };
    responseText += `### ${typeInfo.icon} ${typeInfo.label}\n\n`;
    responseText += '| ID | 名前 | 説明 | タグ |\n';
    responseText += '|----|------|------|------|\n';
    
    for (const skill of typeSkills) {
      responseText += `| \`${skill.id}\` | ${skill.name} | ${skill.description} | ${skill.tags.join(', ')} |\n`;
    }
    
    responseText += '\n';
  }
  
  return {
    content: [{ type: 'text', text: responseText }],
  };
}

/**
 * Handle skill_execute tool call
 */
export async function handleSkillExecute(input: SkillExecuteInput): Promise<{
  content: Array<{ type: 'text'; text: string }>;
}> {
  const allSkills = [...builtInSkills, ...customSkills];
  const skill = allSkills.find(s => s.id === input.skillId);
  
  if (!skill) {
    return {
      content: [{
        type: 'text',
        text: `❌ スキル \`${input.skillId}\` が見つかりません。`,
      }],
    };
  }
  
  if (!skill.enabled) {
    return {
      content: [{
        type: 'text',
        text: `⚠️ スキル \`${input.skillId}\` は無効化されています。`,
      }],
    };
  }
  
  // Validate required parameters
  const missingParams = skill.parameters
    .filter(p => p.required && input.parameters?.[p.name] === undefined)
    .map(p => p.name);
  
  if (missingParams.length > 0) {
    return {
      content: [{
        type: 'text',
        text: `❌ 必須パラメータが不足しています: ${missingParams.join(', ')}`,
      }],
    };
  }
  
  // Simulate execution
  const startTime = Date.now();
  
  // Placeholder result
  const result = {
    success: true,
    data: `Executed ${skill.name} with parameters: ${JSON.stringify(input.parameters)}`,
  };
  
  const duration = Date.now() - startTime;
  
  const typeInfo = SKILL_TYPE_LABELS[skill.type] || { label: skill.type, icon: '❓' };
  
  return {
    content: [{
      type: 'text',
      text: `## ${typeInfo.icon} スキル実行完了

**スキルID**: \`${skill.id}\`
**スキル名**: ${skill.name}
**結果**: ${result.success ? '✅ 成功' : '❌ 失敗'}
**実行時間**: ${duration}ms

### 結果

\`\`\`
${result.data}
\`\`\``,
    }],
  };
}

/**
 * Handle skill_validate tool call
 */
export async function handleSkillValidate(input: SkillValidateInput): Promise<{
  content: Array<{ type: 'text'; text: string }>;
}> {
  const errors: string[] = [];
  const warnings: string[] = [];
  
  if (input.skillId) {
    // Validate existing skill
    const allSkills = [...builtInSkills, ...customSkills];
    const skill = allSkills.find(s => s.id === input.skillId);
    
    if (!skill) {
      return {
        content: [{
          type: 'text',
          text: `❌ スキル \`${input.skillId}\` が見つかりません。`,
        }],
      };
    }
    
    // Validate skill
    if (!skill.name || skill.name.trim() === '') {
      errors.push('スキル名が未設定です');
    }
    if (!skill.description || skill.description.length < 10) {
      warnings.push('説明が短すぎます');
    }
    if (skill.parameters.length > 10) {
      warnings.push('パラメータが多すぎます');
    }
  } else if (input.definition) {
    // Validate new definition
    const def = input.definition;
    
    if (!def.id || def.id.trim() === '') {
      errors.push('スキルIDが未設定です');
    }
    if (!def.name || def.name.trim() === '') {
      errors.push('スキル名が未設定です');
    }
    if (!def.description || def.description.trim() === '') {
      errors.push('説明が未設定です');
    }
    if (!def.type) {
      errors.push('タイプが未設定です');
    }
  }
  
  const isValid = errors.length === 0;
  
  return {
    content: [{
      type: 'text',
      text: `## 🔍 スキル検証結果

**結果**: ${isValid ? '✅ 有効' : '❌ 無効'}

${errors.length > 0 ? `### エラー

${errors.map(e => `- ❌ ${e}`).join('\n')}
` : ''}

${warnings.length > 0 ? `### 警告

${warnings.map(w => `- ⚠️ ${w}`).join('\n')}
` : ''}

${isValid && warnings.length === 0 ? '問題は検出されませんでした。' : ''}`,
    }],
  };
}

/**
 * Handle skill_info tool call
 */
export async function handleSkillInfo(input: SkillInfoInput): Promise<{
  content: Array<{ type: 'text'; text: string }>;
}> {
  const allSkills = [...builtInSkills, ...customSkills];
  const skill = allSkills.find(s => s.id === input.skillId);
  
  if (!skill) {
    return {
      content: [{
        type: 'text',
        text: `❌ スキル \`${input.skillId}\` が見つかりません。`,
      }],
    };
  }
  
  const typeInfo = SKILL_TYPE_LABELS[skill.type] || { label: skill.type, icon: '❓' };
  
  let responseText = `## ${typeInfo.icon} ${skill.name}

**スキルID**: \`${skill.id}\`
**タイプ**: ${typeInfo.label}
**状態**: ${skill.enabled ? '✅ 有効' : '⬜ 無効'}
**タグ**: ${skill.tags.join(', ')}

### 説明

${skill.description}

### パラメータ

| 名前 | 型 | 必須 | 説明 |
|------|-----|------|------|
${skill.parameters.map(p => `| \`${p.name}\` | ${p.type} | ${p.required ? '✅' : '⬜'} | ${p.description} |`).join('\n')}

### 使用例

\`\`\`json
{
  "skillId": "${skill.id}",
  "parameters": {
${skill.parameters.map(p => `    "${p.name}": "<${p.type}>"`).join(',\n')}
  }
}
\`\`\``;
  
  return {
    content: [{ type: 'text', text: responseText }],
  };
}

/**
 * Handle skill_register tool call
 */
export async function handleSkillRegister(input: SkillRegisterInput): Promise<{
  content: Array<{ type: 'text'; text: string }>;
}> {
  // Check for duplicate ID
  const allSkills = [...builtInSkills, ...customSkills];
  if (allSkills.some(s => s.id === input.id)) {
    return {
      content: [{
        type: 'text',
        text: `❌ スキルID \`${input.id}\` は既に使用されています。`,
      }],
    };
  }
  
  const newSkill: BuiltInSkill = {
    id: input.id,
    name: input.name,
    description: input.description,
    type: input.type,
    enabled: true,
    parameters: (input.parameters || []).map(p => ({
      name: p.name,
      type: p.type,
      required: p.required ?? false,
      description: p.description,
    })),
    tags: input.tags || [],
  };
  
  customSkills.push(newSkill);
  
  const typeInfo = SKILL_TYPE_LABELS[input.type] || { label: input.type, icon: '❓' };
  
  return {
    content: [{
      type: 'text',
      text: `## ✅ スキル登録完了

**スキルID**: \`${newSkill.id}\`
**スキル名**: ${newSkill.name}
**タイプ**: ${typeInfo.icon} ${typeInfo.label}
**パラメータ数**: ${newSkill.parameters.length}

スキルが正常に登録されました。\`skill_execute\` で実行できます。`,
    }],
  };
}
