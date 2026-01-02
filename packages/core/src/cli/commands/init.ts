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
import { mkdir, writeFile, access } from 'fs/promises';
import { join } from 'path';
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
