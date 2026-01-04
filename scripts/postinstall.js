#!/usr/bin/env node
/**
 * MUSUBIX Postinstall Script
 * 
 * Copies .github/ and AGENTS.md to the project root after npm install.
 * This enables GitHub Copilot and other AI agents to use MUSUBIX prompts and skills.
 */

import { existsSync, cpSync, copyFileSync, mkdirSync } from 'fs';
import { dirname, join, resolve } from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

// Source: where musubix is installed (node_modules/musubix)
const packageRoot = resolve(__dirname, '..');

// Target: project root (where npm install was run)
// When installed as dependency: process.env.INIT_CWD points to project root
// When running in musubix repo itself: skip
const projectRoot = process.env.INIT_CWD || process.cwd();

// Skip if we're in the musubix package itself
if (projectRoot === packageRoot || projectRoot.includes('node_modules/musubix')) {
  console.log('musubix: Skipping postinstall (running in package directory)');
  process.exit(0);
}

const sourceGithub = join(packageRoot, '.github');
const sourceAgents = join(packageRoot, 'AGENTS.md');
const targetGithub = join(projectRoot, '.github');
const targetAgents = join(projectRoot, 'AGENTS.md');

let copied = false;

// Copy .github directory
if (existsSync(sourceGithub)) {
  // Only copy musubix-specific files, don't overwrite existing .github
  const musubixPrompts = join(sourceGithub, 'prompts');
  const musubixSkills = join(sourceGithub, 'skills');
  const musubixAgents = join(sourceGithub, 'AGENTS.md');

  // Create .github if not exists
  if (!existsSync(targetGithub)) {
    mkdirSync(targetGithub, { recursive: true });
  }

  // Copy prompts
  if (existsSync(musubixPrompts)) {
    const targetPrompts = join(targetGithub, 'prompts');
    if (!existsSync(targetPrompts)) {
      mkdirSync(targetPrompts, { recursive: true });
    }
    cpSync(musubixPrompts, targetPrompts, { recursive: true, force: false });
    console.log('musubix: Copied .github/prompts/');
    copied = true;
  }

  // Copy skills
  if (existsSync(musubixSkills)) {
    const targetSkills = join(targetGithub, 'skills');
    if (!existsSync(targetSkills)) {
      mkdirSync(targetSkills, { recursive: true });
    }
    cpSync(musubixSkills, targetSkills, { recursive: true, force: false });
    console.log('musubix: Copied .github/skills/');
    copied = true;
  }

  // Copy .github/AGENTS.md
  if (existsSync(musubixAgents)) {
    const targetGithubAgents = join(targetGithub, 'AGENTS.md');
    if (!existsSync(targetGithubAgents)) {
      copyFileSync(musubixAgents, targetGithubAgents);
      console.log('musubix: Copied .github/AGENTS.md');
      copied = true;
    }
  }
}

// Copy AGENTS.md to project root
if (existsSync(sourceAgents) && !existsSync(targetAgents)) {
  copyFileSync(sourceAgents, targetAgents);
  console.log('musubix: Copied AGENTS.md');
  copied = true;
}

if (copied) {
  console.log('musubix: AI agent configuration files installed successfully!');
  console.log('musubix: GitHub Copilot can now use MUSUBIX SDD prompts and skills.');
} else {
  console.log('musubix: Configuration files already exist, skipping.');
}
