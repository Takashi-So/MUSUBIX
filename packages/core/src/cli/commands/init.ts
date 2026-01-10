/**
 * Init Command
 * 
 * Initializes a new MUSUBIX project
 * 
 * @packageDocumentation
 * @module cli/commands/init
 * 
 * @see REQ-ARC-002 - CLI Interface
 * @see DES-MUSUBIX-001 Section 3.2.2 - CLI Commands
 */

import type { Command } from 'commander';
import { mkdir, writeFile, access, readFile, readdir, cp } from 'fs/promises';
import { join, dirname } from 'path';
import { fileURLToPath } from 'url';
import { ExitCode, getGlobalOptions, outputResult } from '../base.js';
import { VERSION } from '../../version.js';

/**
 * Init command options
 */
export interface InitOptions {
  name?: string;
  template?: string;
  force: boolean;
}

/**
 * Init result
 */
export interface InitResult {
  success: boolean;
  projectPath: string;
  filesCreated: string[];
  message: string;
}

/**
 * Default project configuration template
 */
const DEFAULT_CONFIG = {
  version: VERSION,
  project: 'my-project',
  steeringDir: './steering',
  storageDir: './storage',
  llm: {
    provider: 'anthropic' as const,
    model: 'claude-sonnet-4-20250514',
    maxTokens: 4096,
    temperature: 0.7,
  },
  yata: {
    transport: 'stdio' as const,
    server: 'yata-mcp',
    timeout: 30000,
  },
  integration: {
    neuralThreshold: 0.7,
    symbolicThreshold: 0.8,
    defaultStrategy: 'neural-validated' as const,
    gracefulDegradation: true,
  },
};

/**
 * Directory structure to create
 */
const DIRECTORY_STRUCTURE = [
  'steering',
  'steering/rules',
  'storage',
  'storage/specs',
  'storage/archive',
  'storage/changes',
  '.github',
  '.github/prompts',
  '.github/skills',
  '.claude',
];

/**
 * Register init command
 */
export function registerInitCommand(program: Command): void {
  program
    .command('init')
    .description('Initialize a new MUSUBIX project')
    .argument('[path]', 'Project directory (default: current directory)', '.')
    .option('-n, --name <name>', 'Project name')
    .option('-t, --template <template>', 'Project template', 'default')
    .option('-f, --force', 'Overwrite existing files', false)
    .action(async (path: string, options: InitOptions) => {
      const globalOpts = getGlobalOptions(program);
      
      try {
        const result = await executeInit(path, options);
        outputResult(result, globalOpts);
        process.exit(result.success ? ExitCode.SUCCESS : ExitCode.GENERAL_ERROR);
      } catch (error) {
        if (globalOpts.json) {
          console.error(JSON.stringify({
            success: false,
            error: error instanceof Error ? error.message : String(error),
          }));
        } else {
          console.error(`Error: ${error instanceof Error ? error.message : String(error)}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });
}

/**
 * Execute init command
 */
export async function executeInit(
  targetPath: string,
  options: InitOptions
): Promise<InitResult> {
  const projectPath = join(process.cwd(), targetPath);
  const projectName = options.name ?? getProjectNameFromPath(projectPath);
  const filesCreated: string[] = [];

  // Check if directory exists and has files
  if (!options.force) {
    const configPath = join(projectPath, 'musubix.config.json');
    try {
      await access(configPath);
      return {
        success: false,
        projectPath,
        filesCreated: [],
        message: 'Project already initialized. Use --force to overwrite.',
      };
    } catch {
      // Config doesn't exist, continue
    }
  }

  // Create directory structure
  for (const dir of DIRECTORY_STRUCTURE) {
    const dirPath = join(projectPath, dir);
    await mkdir(dirPath, { recursive: true });
    filesCreated.push(dir + '/');
  }

  // Create configuration file
  const config = {
    ...DEFAULT_CONFIG,
    project: projectName,
  };
  const configPath = join(projectPath, 'musubix.config.json');
  await writeFile(configPath, JSON.stringify(config, null, 2) + '\n');
  filesCreated.push('musubix.config.json');

  // Create steering documents
  await createSteeringDocuments(projectPath, projectName, filesCreated);

  // Copy AGENTS.md and .github/ from musubix package
  await copyAgentFiles(projectPath, filesCreated);

  // Create .gitkeep files
  await writeFile(join(projectPath, 'storage/archive/.gitkeep'), '');
  await writeFile(join(projectPath, 'storage/changes/.gitkeep'), '');
  filesCreated.push('storage/archive/.gitkeep', 'storage/changes/.gitkeep');

  return {
    success: true,
    projectPath,
    filesCreated,
    message: `MUSUBIX project '${projectName}' initialized successfully!`,
  };
}

/**
 * Create steering documents
 */
async function createSteeringDocuments(
  projectPath: string,
  projectName: string,
  filesCreated: string[]
): Promise<void> {
  // Constitution
  const constitution = `# ${projectName} Constitution

## 9つの憲法条項

本プロジェクトは以下の憲法条項に準拠します。

### Article I: Library-First Architecture
すべての機能はライブラリとして分離すること。

### Article II: CLI Interface Mandate
すべてのライブラリにCLIエントリーポイントを設けること。

### Article III: Test-First Development
テスト駆動開発を実践すること。

### Article IV: Project Memory
steering/配下にプロジェクトメモリを維持すること。

### Article V: Traceability
要件からコードまでの追跡可能性を確保すること。

### Article VI: Agent Memory Format
MUSUBI SDD形式でメモリを管理すること。

### Article VII: Simplicity Gate
初期は3プロジェクト以内に抑えること。

### Article VIII: Anti-Abstraction
フレームワークAPIを直接使用すること。

### Article IX: Integration Testing
実サービスでテストを行うこと。

---

**生成日**: ${new Date().toISOString().split('T')[0]}
**MUSUBIX Version**: ${VERSION}
`;
  
  await writeFile(
    join(projectPath, 'steering/rules/constitution.md'),
    constitution
  );
  filesCreated.push('steering/rules/constitution.md');

  // Product context
  const product = `# ${projectName} - Product Context

## 概要

[プロジェクトの概要を記述]

## 目的

[プロジェクトの目的を記述]

## ステークホルダー

- [ステークホルダー1]
- [ステークホルダー2]

---

**生成日**: ${new Date().toISOString().split('T')[0]}
`;
  
  await writeFile(join(projectPath, 'steering/product.md'), product);
  filesCreated.push('steering/product.md');

  // Tech stack
  const tech = `# ${projectName} - Technology Stack

## 言語

- TypeScript 5.3+
- Node.js 20+

## フレームワーク

- [使用するフレームワーク]

## ツール

- Vitest (テスト)
- ESLint (リント)

---

**生成日**: ${new Date().toISOString().split('T')[0]}
`;
  
  await writeFile(join(projectPath, 'steering/tech.md'), tech);
  filesCreated.push('steering/tech.md');

  // Structure
  const structure = `# ${projectName} - Project Structure

## ディレクトリ構成

\`\`\`
${projectName}/
├── steering/          # プロジェクトメモリ
│   ├── rules/         # 憲法・ルール
│   ├── product.md     # プロダクトコンテキスト
│   ├── tech.md        # 技術スタック
│   └── structure.md   # 構造定義
├── storage/           # データストレージ
│   ├── specs/         # 仕様書
│   ├── archive/       # アーカイブ
│   └── changes/       # 変更履歴
└── musubix.config.json # 設定ファイル
\`\`\`

---

**生成日**: ${new Date().toISOString().split('T')[0]}
`;
  
  await writeFile(join(projectPath, 'steering/structure.md'), structure);
  filesCreated.push('steering/structure.md');
}

/**
 * Extract project name from path
 */
function getProjectNameFromPath(projectPath: string): string {
  const parts = projectPath.split(/[/\\]/);
  return parts[parts.length - 1] || 'my-project';
}

/**
 * Find musubix package directory in node_modules or global install
 */
async function findMusubixPackage(): Promise<string | null> {
  // Try to find musubix package in multiple locations
  const searchPaths = [
    // From current working directory (local install)
    join(process.cwd(), 'node_modules', '@nahisaho', 'musubix-core'),
    join(process.cwd(), 'node_modules', 'musubix'),
    // From this file's location (global install or development)
    join(dirname(fileURLToPath(import.meta.url)), '..', '..'),  // packages/core/
    join(dirname(fileURLToPath(import.meta.url)), '..', '..', '..', '..', '..'),  // monorepo root
    // Global npm install locations
    ...(process.env.npm_config_prefix 
      ? [join(process.env.npm_config_prefix, 'lib', 'node_modules', '@nahisaho', 'musubix-core')]
      : []),
  ];

  for (const searchPath of searchPaths) {
    try {
      // Check if .github/skills exists (indicates musubix package with skills)
      await access(join(searchPath, '.github', 'skills'));
      return searchPath;
    } catch {
      // Try checking for AGENTS.md as fallback
      try {
        await access(join(searchPath, 'AGENTS.md'));
        return searchPath;
      } catch {
        // Not found, try next
      }
    }
  }

  return null;
}

/**
 * Copy AGENTS.md, .github/, and .claude/ to project root for AI agents
 */
async function copyAgentFiles(
  projectPath: string,
  filesCreated: string[]
): Promise<void> {
  const musubixPath = await findMusubixPackage();
  
  if (!musubixPath) {
    // If musubix package not found, create default files
    await createDefaultAgentsFile(projectPath, filesCreated);
    await createDefaultClaudeSettings(projectPath, filesCreated);
    return;
  }

  try {
    // Copy AGENTS.md
    const agentsSource = join(musubixPath, 'AGENTS.md');
    const agentsDest = join(projectPath, 'AGENTS.md');
    const agentsContent = await readFile(agentsSource, 'utf-8');
    await writeFile(agentsDest, agentsContent);
    filesCreated.push('AGENTS.md');

    // Copy AGENTS.md as CLAUDE.md for Claude Code
    const claudeMdDest = join(projectPath, 'CLAUDE.md');
    await writeFile(claudeMdDest, agentsContent);
    filesCreated.push('CLAUDE.md');

    // Copy .github/ directory
    const githubSource = join(musubixPath, '.github');
    const githubDest = join(projectPath, '.github');
    
    try {
      await cp(githubSource, githubDest, { recursive: true });
      filesCreated.push('.github/');
      
      // List copied files
      const promptsDir = join(githubDest, 'prompts');
      const skillsDir = join(githubDest, 'skills');
      
      try {
        const prompts = await readdir(promptsDir);
        for (const file of prompts) {
          filesCreated.push(`.github/prompts/${file}`);
        }
      } catch {
        // prompts dir might not exist
      }
      
      try {
        const skills = await readdir(skillsDir);
        for (const skill of skills) {
          filesCreated.push(`.github/skills/${skill}/`);
        }
      } catch {
        // skills dir might not exist
      }
    } catch {
      // .github copy failed, create minimal structure
      await createDefaultGithubFiles(projectPath, filesCreated);
    }

    // Copy .claude/ directory or create default
    const claudeSource = join(musubixPath, '.claude');
    const claudeDest = join(projectPath, '.claude');
    
    try {
      await access(claudeSource);
      await cp(claudeSource, claudeDest, { recursive: true });
      filesCreated.push('.claude/');
    } catch {
      // .claude doesn't exist in source, create default
      await createDefaultClaudeSettings(projectPath, filesCreated);
    }
  } catch {
    // Fallback to default files
    await createDefaultAgentsFile(projectPath, filesCreated);
    await createDefaultGithubFiles(projectPath, filesCreated);
    await createDefaultClaudeSettings(projectPath, filesCreated);
  }
}

/**
 * Create default AGENTS.md if musubix package not found
 */
async function createDefaultAgentsFile(
  projectPath: string,
  filesCreated: string[]
): Promise<void> {
  const agentsContent = `# MUSUBIX Project - AI Coding Agent Guide

> **AI Coding Agent向け**: このファイルはAIエージェント（GitHub Copilot、Claude等）がプロジェクトを理解するためのガイドです。

## 🎯 プロジェクト概要

このプロジェクトは **MUSUBIX** (Neuro-Symbolic AI Coding System) を使用しています。

## 📋 9憲法条項（Constitutional Articles）

| Article | 原則 |
|---------|------|
| I | Library-First Architecture |
| II | CLI Interface Mandate |
| III | Test-First Development |
| IV | Project Memory |
| V | Traceability |
| VI | Agent Memory Format |
| VII | Simplicity Gate |
| VIII | Anti-Abstraction |
| IX | Integration Testing |

## 📂 プロジェクト構造

- \`steering/\` - プロジェクトメモリ（決定前に必ず参照）
- \`storage/specs/\` - 要件・設計・タスク仕様
- \`musubix.config.json\` - MUSUBIX設定

## 🛠️ MUSUBIX CLI

\`\`\`bash
npx musubix --help
npx musubix requirements analyze <file>
npx musubix design generate <file>
npx musubix codegen generate <file>
\`\`\`

---

**Generated by**: MUSUBIX v${VERSION}
**Date**: ${new Date().toISOString().split('T')[0]}
`;

  await writeFile(join(projectPath, 'AGENTS.md'), agentsContent);
  filesCreated.push('AGENTS.md');

  // Also create CLAUDE.md for Claude Code
  await writeFile(join(projectPath, 'CLAUDE.md'), agentsContent);
  filesCreated.push('CLAUDE.md');
}

/**
 * Create default .github files
 */
async function createDefaultGithubFiles(
  projectPath: string,
  filesCreated: string[]
): Promise<void> {
  // Create .github/copilot-instructions.md
  const copilotInstructions = `# GitHub Copilot Instructions

このプロジェクトは MUSUBIX (Neuro-Symbolic AI Coding System) を使用しています。

## 基本原則

1. **steering/ を参照**: 決定前にプロジェクトメモリを確認
2. **EARS形式**: 要件は EARS 形式で記述
3. **トレーサビリティ**: コードコメントに要件ID (REQ-*) を記載
4. **テスト先行**: Red-Green-Blue サイクルを遵守

## コマンド

\`\`\`bash
npx musubix requirements analyze <file>
npx musubix design generate <file>
npx musubix codegen generate <file>
npx musubix test generate <file>
\`\`\`

## 参照ドキュメント

- \`AGENTS.md\` - AI エージェントガイド
- \`steering/rules/constitution.md\` - 憲法条項
- \`steering/product.md\` - プロダクトコンテキスト
`;

  await mkdir(join(projectPath, '.github'), { recursive: true });
  await writeFile(
    join(projectPath, '.github', 'copilot-instructions.md'),
    copilotInstructions
  );
  filesCreated.push('.github/copilot-instructions.md');
}

/**
 * Create default .claude settings for Claude Code
 */
async function createDefaultClaudeSettings(
  projectPath: string,
  filesCreated: string[]
): Promise<void> {
  // Create .claude/settings.json
  const claudeSettings = {
    projectContext: {
      name: getProjectNameFromPath(projectPath),
      framework: 'MUSUBIX',
      methodology: 'SDD (Specification-Driven Development)',
    },
    skills: {
      enabled: true,
      autoDetect: true,
      skillsPath: '.github/skills',
    },
    prompts: {
      enabled: true,
      promptsPath: '.github/prompts',
    },
    rules: {
      constitution: 'steering/rules/constitution.md',
      alwaysReadFirst: [
        'AGENTS.md',
        'steering/product.md',
        'steering/tech.md',
      ],
    },
    codeGeneration: {
      testFirst: true,
      traceabilityComments: true,
      earsFormat: true,
    },
  };

  await mkdir(join(projectPath, '.claude'), { recursive: true });
  await writeFile(
    join(projectPath, '.claude', 'settings.json'),
    JSON.stringify(claudeSettings, null, 2) + '\n'
  );
  filesCreated.push('.claude/settings.json');

  // Create .claude/CLAUDE.md (Claude Code instructions)
  const claudeInstructions = `# Claude Code Instructions

このプロジェクトは **MUSUBIX** (Neuro-Symbolic AI Coding System) を使用しています。

## 🎯 基本ルール

1. **プロジェクトメモリを参照**: 決定前に \`steering/\` を確認
2. **EARS形式**: 要件は必ず EARS 形式で記述
3. **トレーサビリティ**: コードコメントに要件ID (REQ-*) を記載
4. **テスト先行**: Red-Green-Blue サイクルを遵守

## 📁 重要なファイル

| ファイル | 用途 |
|---------|------|
| \`AGENTS.md\` | AI エージェント向けガイド |
| \`steering/rules/constitution.md\` | 9つの憲法条項 |
| \`steering/product.md\` | プロダクトコンテキスト |
| \`steering/tech.md\` | 技術スタック |

## 🛠️ Agent Skills

\`.github/skills/\` に10のMUSUBIX Agent Skillsが配置されています:

- \`musubix-sdd-workflow\` - SDD開発ワークフロー
- \`musubix-ears-validation\` - EARS形式検証
- \`musubix-code-generation\` - コード生成
- \`musubix-c4-design\` - C4モデル設計
- \`musubix-traceability\` - トレーサビリティ
- \`musubix-test-generation\` - テスト生成
- \`musubix-adr-generation\` - ADR生成
- \`musubix-best-practices\` - ベストプラクティス
- \`musubix-domain-inference\` - ドメイン推論
- \`musubix-technical-writing\` - 技術ドキュメント作成

## 📝 CLIコマンド

\`\`\`bash
npx musubix requirements analyze <file>
npx musubix design generate <file>
npx musubix codegen generate <file>
npx musubix test generate <file>
npx musubix trace matrix
\`\`\`

---

**Generated by**: MUSUBIX v${VERSION}
`;

  await writeFile(
    join(projectPath, '.claude', 'CLAUDE.md'),
    claudeInstructions
  );
  filesCreated.push('.claude/CLAUDE.md');
}