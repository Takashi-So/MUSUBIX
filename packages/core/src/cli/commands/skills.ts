/**
 * Skills Command
 *
 * Manage GitHub Agent Skills for MUSUBIX
 *
 * @packageDocumentation
 * @module cli/commands/skills
 *
 * @see REQ-SKL-001 - Skills Directory Structure
 * @see REQ-SKL-002 - Skills Manifest Format
 * @see REQ-SKL-003 - Skills Validation
 * @see REQ-SKL-004 - Skills CLI Integration
 * @see DES-MUSUBIX-001 Section 16-B - Agent Skills設計
 * @see TSK-061 - Skills CLI実装
 */

import type { Command } from 'commander';
import { readdir, readFile, writeFile, mkdir, access, stat } from 'fs/promises';
import { join, resolve, basename } from 'path';
import { ExitCode, getGlobalOptions, outputResult } from '../base.js';
import * as yaml from 'yaml';

/**
 * Skills command options
 */
export interface SkillsOptions {
  skillsDir?: string;
}

/**
 * Skill metadata from SKILL.md frontmatter
 */
export interface SkillMetadata {
  name: string;
  description: string;
  license?: string;
  version?: string;
  author?: string;
  tags?: string[];
}

/**
 * Skill information
 */
export interface SkillInfo {
  name: string;
  path: string;
  metadata: SkillMetadata | null;
  hasSkillMd: boolean;
  error?: string;
}

/**
 * Skill validation result
 */
export interface SkillValidationResult {
  skillName: string;
  valid: boolean;
  errors: string[];
  warnings: string[];
}

/**
 * Skills list result
 */
export interface SkillsListResult {
  success: boolean;
  skills: SkillInfo[];
  skillsDir: string;
  message: string;
}

/**
 * Skills validate result
 */
export interface SkillsValidateResult {
  success: boolean;
  results: SkillValidationResult[];
  message: string;
}

/**
 * Skills create result
 */
export interface SkillsCreateResult {
  success: boolean;
  skillPath: string;
  filesCreated: string[];
  message: string;
}

/**
 * Default skills directory
 */
const DEFAULT_SKILLS_DIR = '.github/skills';

/**
 * Required fields in SKILL.md frontmatter
 */
const REQUIRED_FRONTMATTER_FIELDS = ['name', 'description'];

/**
 * Skill template for creation
 */
const SKILL_TEMPLATE = (name: string): string => `---
name: ${name}
description: [Enter skill description]
license: MIT
---

# ${name}

## Overview

[Describe what this skill does]

## Usage

[Explain how to use this skill]

## Prerequisites

[List any prerequisites]

## Workflow

[Describe the workflow steps]

## Examples

[Provide usage examples]
`;

/**
 * Register skills command
 */
export function registerSkillsCommand(program: Command): void {
  const skills = program
    .command('skills')
    .description('Manage GitHub Agent Skills');

  // skills list
  skills
    .command('list')
    .description('List all available skills')
    .option('-d, --skills-dir <dir>', 'Skills directory', DEFAULT_SKILLS_DIR)
    .action(async (options: SkillsOptions) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const result = await executeSkillsList(options);
        outputResult(result, globalOpts);
        process.exit(result.success ? ExitCode.SUCCESS : ExitCode.GENERAL_ERROR);
      } catch (error) {
        handleError(error, globalOpts);
      }
    });

  // skills validate
  skills
    .command('validate')
    .description('Validate skill(s)')
    .argument('[skill-name]', 'Skill name to validate (validates all if omitted)')
    .option('-d, --skills-dir <dir>', 'Skills directory', DEFAULT_SKILLS_DIR)
    .action(async (skillName: string | undefined, options: SkillsOptions) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const result = await executeSkillsValidate(skillName, options);
        outputResult(result, globalOpts);
        process.exit(result.success ? ExitCode.SUCCESS : ExitCode.GENERAL_ERROR);
      } catch (error) {
        handleError(error, globalOpts);
      }
    });

  // skills create
  skills
    .command('create')
    .description('Create a new skill from template')
    .argument('<skill-name>', 'Name for the new skill')
    .option('-d, --skills-dir <dir>', 'Skills directory', DEFAULT_SKILLS_DIR)
    .action(async (skillName: string, options: SkillsOptions) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const result = await executeSkillsCreate(skillName, options);
        outputResult(result, globalOpts);
        process.exit(result.success ? ExitCode.SUCCESS : ExitCode.GENERAL_ERROR);
      } catch (error) {
        handleError(error, globalOpts);
      }
    });
}

/**
 * Handle error with proper output
 */
function handleError(error: unknown, globalOpts: { json: boolean }): never {
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

/**
 * Parse YAML frontmatter from SKILL.md content
 */
export function parseFrontmatter(content: string): SkillMetadata | null {
  const frontmatterMatch = content.match(/^---\n([\s\S]*?)\n---/);
  if (!frontmatterMatch) {
    return null;
  }

  try {
    const parsed = yaml.parse(frontmatterMatch[1]) as SkillMetadata;
    return parsed;
  } catch {
    return null;
  }
}

/**
 * Get skill info from a skill directory
 */
async function getSkillInfo(skillPath: string): Promise<SkillInfo> {
  const name = basename(skillPath);
  const skillMdPath = join(skillPath, 'SKILL.md');

  try {
    await access(skillMdPath);
    const content = await readFile(skillMdPath, 'utf-8');
    const metadata = parseFrontmatter(content);

    return {
      name,
      path: skillPath,
      metadata,
      hasSkillMd: true,
    };
  } catch {
    return {
      name,
      path: skillPath,
      metadata: null,
      hasSkillMd: false,
      error: 'SKILL.md not found',
    };
  }
}

/**
 * Execute skills list command
 */
export async function executeSkillsList(options: SkillsOptions): Promise<SkillsListResult> {
  const skillsDir = resolve(process.cwd(), options.skillsDir ?? DEFAULT_SKILLS_DIR);

  try {
    await access(skillsDir);
  } catch {
    return {
      success: false,
      skills: [],
      skillsDir,
      message: `Skills directory not found: ${skillsDir}`,
    };
  }

  const entries = await readdir(skillsDir, { withFileTypes: true });
  const skillDirs = entries.filter(entry => entry.isDirectory());

  const skills: SkillInfo[] = [];
  for (const dir of skillDirs) {
    const skillPath = join(skillsDir, dir.name);
    const info = await getSkillInfo(skillPath);
    skills.push(info);
  }

  return {
    success: true,
    skills,
    skillsDir,
    message: `Found ${skills.length} skill(s)`,
  };
}

/**
 * Validate a single skill
 */
async function validateSkill(skillPath: string): Promise<SkillValidationResult> {
  const skillName = basename(skillPath);
  const errors: string[] = [];
  const warnings: string[] = [];

  // Check if skill directory exists
  try {
    const stats = await stat(skillPath);
    if (!stats.isDirectory()) {
      errors.push('Skill path is not a directory');
      return { skillName, valid: false, errors, warnings };
    }
  } catch {
    errors.push('Skill directory not found');
    return { skillName, valid: false, errors, warnings };
  }

  // Check SKILL.md exists
  const skillMdPath = join(skillPath, 'SKILL.md');
  let content: string;
  try {
    content = await readFile(skillMdPath, 'utf-8');
  } catch {
    errors.push('SKILL.md file not found (REQ-SKL-001 violation)');
    return { skillName, valid: false, errors, warnings };
  }

  // Check frontmatter exists and is valid YAML
  const frontmatterMatch = content.match(/^---\n([\s\S]*?)\n---/);
  if (!frontmatterMatch) {
    errors.push('YAML frontmatter not found (REQ-SKL-002 violation)');
    return { skillName, valid: false, errors, warnings };
  }

  // Parse frontmatter
  let metadata: SkillMetadata;
  try {
    metadata = yaml.parse(frontmatterMatch[1]) as SkillMetadata;
  } catch (e) {
    errors.push(`Invalid YAML frontmatter: ${e instanceof Error ? e.message : String(e)}`);
    return { skillName, valid: false, errors, warnings };
  }

  // Check required fields (REQ-SKL-002)
  for (const field of REQUIRED_FRONTMATTER_FIELDS) {
    if (!(field in metadata) || !metadata[field as keyof SkillMetadata]) {
      errors.push(`Missing required field: ${field} (REQ-SKL-002 violation)`);
    }
  }

  // Check name matches directory name (Article VI - Project Memory)
  if (metadata.name && metadata.name !== skillName) {
    warnings.push(`Skill name '${metadata.name}' does not match directory name '${skillName}'`);
  }

  // Check description is not placeholder
  if (metadata.description?.includes('[Enter') || metadata.description?.includes('[TODO')) {
    warnings.push('Description contains placeholder text');
  }

  // Check for license
  if (!metadata.license) {
    warnings.push('License not specified (recommended)');
  }

  // Check content has meaningful documentation
  const bodyContent = content.replace(/^---\n[\s\S]*?\n---/, '').trim();
  if (bodyContent.length < 100) {
    warnings.push('Skill documentation seems too short');
  }

  return {
    skillName,
    valid: errors.length === 0,
    errors,
    warnings,
  };
}

/**
 * Execute skills validate command
 */
export async function executeSkillsValidate(
  skillName: string | undefined,
  options: SkillsOptions
): Promise<SkillsValidateResult> {
  const skillsDir = resolve(process.cwd(), options.skillsDir ?? DEFAULT_SKILLS_DIR);

  if (skillName) {
    // Validate single skill
    const skillPath = join(skillsDir, skillName);
    const result = await validateSkill(skillPath);
    return {
      success: result.valid,
      results: [result],
      message: result.valid
        ? `Skill '${skillName}' is valid`
        : `Skill '${skillName}' has ${result.errors.length} error(s)`,
    };
  }

  // Validate all skills
  try {
    await access(skillsDir);
  } catch {
    return {
      success: false,
      results: [],
      message: `Skills directory not found: ${skillsDir}`,
    };
  }

  const entries = await readdir(skillsDir, { withFileTypes: true });
  const skillDirs = entries.filter(entry => entry.isDirectory());

  const results: SkillValidationResult[] = [];
  for (const dir of skillDirs) {
    const skillPath = join(skillsDir, dir.name);
    const result = await validateSkill(skillPath);
    results.push(result);
  }

  const validCount = results.filter(r => r.valid).length;
  const allValid = validCount === results.length;

  return {
    success: allValid,
    results,
    message: allValid
      ? `All ${results.length} skill(s) are valid`
      : `${validCount}/${results.length} skill(s) are valid`,
  };
}

/**
 * Execute skills create command
 */
export async function executeSkillsCreate(
  skillName: string,
  options: SkillsOptions
): Promise<SkillsCreateResult> {
  const skillsDir = resolve(process.cwd(), options.skillsDir ?? DEFAULT_SKILLS_DIR);
  const skillPath = join(skillsDir, skillName);
  const filesCreated: string[] = [];

  // Check if skill already exists
  try {
    await access(skillPath);
    return {
      success: false,
      skillPath,
      filesCreated: [],
      message: `Skill '${skillName}' already exists`,
    };
  } catch {
    // Skill doesn't exist, continue
  }

  // Create skills directory if it doesn't exist
  await mkdir(skillsDir, { recursive: true });

  // Create skill directory
  await mkdir(skillPath, { recursive: true });
  filesCreated.push(skillName + '/');

  // Create SKILL.md
  const skillMdPath = join(skillPath, 'SKILL.md');
  const content = SKILL_TEMPLATE(skillName);
  await writeFile(skillMdPath, content);
  filesCreated.push(join(skillName, 'SKILL.md'));

  return {
    success: true,
    skillPath,
    filesCreated,
    message: `Created skill '${skillName}' at ${skillPath}`,
  };
}
