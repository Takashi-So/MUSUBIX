#!/usr/bin/env node
/**
 * MUSUBIX Postinstall Script
 * 
 * Copies .github/ (prompts, skills) and AGENTS.md to the project root after npm install.
 * This enables GitHub Copilot and Claude Code to use MUSUBIX SDD prompts and Agent Skills.
 * 
 * Installed skills (9 total):
 * - musubix-sdd-workflow: SDD development workflow guide
 * - musubix-ears-validation: EARS format validation
 * - musubix-code-generation: Design-to-code generation
 * - musubix-c4-design: C4 model architecture design
 * - musubix-traceability: Requirements traceability management
 * - musubix-test-generation: TDD-based test generation
 * - musubix-adr-generation: Architecture Decision Records
 * - musubix-best-practices: 17 best practices guide
 * - musubix-domain-inference: 62 domain detection
 */

import { existsSync, cpSync, copyFileSync, mkdirSync, readdirSync } from 'fs';
import { dirname, join, resolve } from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

// Source: where musubix-core is installed (node_modules/@nahisaho/musubix-core)
const packageRoot = resolve(__dirname, '..');

// Target: project root (where npm install was run)
// When installed as dependency: process.env.INIT_CWD points to project root
const projectRoot = process.env.INIT_CWD || process.cwd();

// Skip if we're in the musubix package itself or in node_modules
const isInNodeModules = packageRoot.includes('node_modules');
const isSameDir = projectRoot === packageRoot;
const isInMusubixRepo = projectRoot.endsWith('MUSUBIX') || projectRoot.includes('/MUSUBIX/');

if (isSameDir || (!isInNodeModules && isInMusubixRepo)) {
  console.log('musubix: Skipping postinstall (running in package directory)');
  process.exit(0);
}

const sourceGithub = join(packageRoot, '.github');
const sourceAgents = join(packageRoot, 'AGENTS.md');
const targetGithub = join(projectRoot, '.github');
const targetAgents = join(projectRoot, 'AGENTS.md');

let copiedItems = [];

// Helper to count items in directory
function countItems(dir) {
  if (!existsSync(dir)) return 0;
  return readdirSync(dir, { recursive: true }).length;
}

// Copy .github directory contents
if (existsSync(sourceGithub)) {
  const musubixPrompts = join(sourceGithub, 'prompts');
  const musubixSkills = join(sourceGithub, 'skills');
  const musubixGithubAgents = join(sourceGithub, 'AGENTS.md');

  // Create .github if not exists
  if (!existsSync(targetGithub)) {
    mkdirSync(targetGithub, { recursive: true });
  }

  // Copy prompts (for GitHub Copilot)
  if (existsSync(musubixPrompts)) {
    const targetPrompts = join(targetGithub, 'prompts');
    if (!existsSync(targetPrompts)) {
      mkdirSync(targetPrompts, { recursive: true });
    }
    try {
      cpSync(musubixPrompts, targetPrompts, { recursive: true, force: false });
      const count = readdirSync(musubixPrompts).length;
      copiedItems.push(`${count} prompts`);
    } catch (e) {
      // Files may already exist
    }
  }

  // Copy skills (for Claude Code Agent Skills)
  if (existsSync(musubixSkills)) {
    const targetSkills = join(targetGithub, 'skills');
    if (!existsSync(targetSkills)) {
      mkdirSync(targetSkills, { recursive: true });
    }
    try {
      cpSync(musubixSkills, targetSkills, { recursive: true, force: false });
      const count = readdirSync(musubixSkills).length;
      copiedItems.push(`${count} Agent Skills`);
    } catch (e) {
      // Files may already exist
    }
  }

  // Copy .github/AGENTS.md
  if (existsSync(musubixGithubAgents)) {
    const targetGithubAgents = join(targetGithub, 'AGENTS.md');
    if (!existsSync(targetGithubAgents)) {
      try {
        copyFileSync(musubixGithubAgents, targetGithubAgents);
        copiedItems.push('.github/AGENTS.md');
      } catch (e) {
        // File may already exist
      }
    }
  }
}

// Copy AGENTS.md to project root
if (existsSync(sourceAgents) && !existsSync(targetAgents)) {
  try {
    copyFileSync(sourceAgents, targetAgents);
    copiedItems.push('AGENTS.md');
  } catch (e) {
    // File may already exist
  }
}

// Output results
if (copiedItems.length > 0) {
  console.log('');
  console.log('╔══════════════════════════════════════════════════════════════╗');
  console.log('║  🎉 MUSUBIX - AI Agent Configuration Installed!              ║');
  console.log('╠══════════════════════════════════════════════════════════════╣');
  console.log('║                                                              ║');
  console.log('║  Installed: ' + copiedItems.join(', ').padEnd(47) + '║');
  console.log('║                                                              ║');
  console.log('║  ✅ GitHub Copilot: Use SDD prompts in chat                  ║');
  console.log('║  ✅ Claude Code: 9 Agent Skills available                    ║');
  console.log('║                                                              ║');
  console.log('║  Skills installed:                                           ║');
  console.log('║    • musubix-sdd-workflow      • musubix-traceability        ║');
  console.log('║    • musubix-ears-validation   • musubix-test-generation     ║');
  console.log('║    • musubix-code-generation   • musubix-adr-generation      ║');
  console.log('║    • musubix-c4-design         • musubix-best-practices      ║');
  console.log('║    • musubix-domain-inference                                ║');
  console.log('║                                                              ║');
  console.log('║  📚 Docs: https://github.com/nahisaho/MUSUBIX                ║');
  console.log('╚══════════════════════════════════════════════════════════════╝');
  console.log('');
} else {
  console.log('musubix: Configuration files already exist, skipping.');
}
