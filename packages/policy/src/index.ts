/**
 * @musubix/policy - Executable Policy Engine
 * 
 * TypeScript-based policy validation for MUSUBIX v3.0
 * 
 * @packageDocumentation
 */

// ============================================================
// Policy Types
// ============================================================

/**
 * Policy category
 */
export type PolicyCategory = 
  | 'constitution'
  | 'naming'
  | 'security'
  | 'quality'
  | 'custom';

/**
 * Severity level
 */
export type Severity = 'error' | 'warning' | 'info';

/**
 * Source location
 */
export interface Location {
  file?: string;
  line?: number;
  column?: number;
}

/**
 * Policy violation
 */
export interface Violation {
  policyId: string;
  message: string;
  location?: Location;
  severity: Severity;
}

/**
 * Policy validation result
 */
export interface PolicyResult {
  passed: boolean;
  violations: Violation[];
  suggestions?: string[];
}

/**
 * Fix result
 */
export interface FixResult {
  fixed: boolean;
  changes: Array<{
    file: string;
    before: string;
    after: string;
  }>;
}

/**
 * Validation context
 */
export interface ValidationContext {
  filePath?: string;
  content?: string;
  projectPath?: string;
  config?: PolicyConfig;
}

/**
 * Policy configuration
 */
export interface PolicyConfig {
  enabled?: string[];
  disabled?: string[];
  severity?: Record<string, Severity>;
}

/**
 * Policy definition
 */
export interface Policy {
  /** Unique identifier */
  id: string;
  /** Display name */
  name: string;
  /** Description */
  description: string;
  /** Severity level */
  severity: Severity;
  /** Category */
  category: PolicyCategory;
  /** Validation function */
  validate(context: ValidationContext): Promise<PolicyResult>;
  /** Auto-fix function (optional) */
  fix?(context: ValidationContext): Promise<FixResult>;
}

/**
 * Validation report
 */
export interface ValidationReport {
  passed: boolean;
  totalPolicies: number;
  passedPolicies: number;
  failedPolicies: number;
  violations: Violation[];
  timestamp: string;
}

// ============================================================
// Policy Engine Interface
// ============================================================

/**
 * Policy engine options
 */
export interface PolicyEngineOptions {
  config?: PolicyConfig;
}

/**
 * Policy engine interface
 */
export interface IPolicyEngine {
  registerPolicy(policy: Policy): void;
  loadPolicies(dir: string): Promise<void>;
  getPolicy(id: string): Policy | undefined;
  listPolicies(category?: PolicyCategory): Policy[];
  validate(context: ValidationContext, policyIds?: string[]): Promise<ValidationReport>;
  validateFile(filePath: string, policyIds?: string[]): Promise<ValidationReport>;
  validateProject(projectPath: string, policyIds?: string[]): Promise<ValidationReport>;
  fix(context: ValidationContext, policyIds?: string[]): Promise<FixResult[]>;
}

// ============================================================
// Factory Function
// ============================================================

/**
 * Create a new policy engine
 */
export function createPolicyEngine(options?: PolicyEngineOptions): IPolicyEngine {
  return new PolicyEngine(options);
}

// ============================================================
// Implementation
// ============================================================

import * as fs from 'node:fs/promises';
import * as path from 'node:path';

/**
 * Policy engine implementation
 */
export class PolicyEngine implements IPolicyEngine {
  private policies: Map<string, Policy> = new Map();
  private config: PolicyConfig;

  constructor(options?: PolicyEngineOptions) {
    this.config = options?.config ?? {};
    // Register built-in constitution policies
    this.registerBuiltinPolicies();
  }

  private registerBuiltinPolicies(): void {
    for (const policy of constitutionPolicies) {
      this.registerPolicy(policy);
    }
  }

  registerPolicy(policy: Policy): void {
    this.policies.set(policy.id, policy);
  }

  async loadPolicies(dir: string): Promise<void> {
    try {
      const files = await fs.readdir(dir);
      for (const file of files) {
        if (file.endsWith('.ts') || file.endsWith('.js')) {
          const filePath = path.join(dir, file);
          try {
            const module = await import(filePath);
            if (Array.isArray(module.default)) {
              for (const policy of module.default) {
                this.registerPolicy(policy);
              }
            } else if (module.policies && Array.isArray(module.policies)) {
              for (const policy of module.policies) {
                this.registerPolicy(policy);
              }
            }
          } catch {
            // Skip files that can't be imported
          }
        }
      }
    } catch {
      // Directory doesn't exist, skip
    }
  }

  getPolicy(id: string): Policy | undefined {
    return this.policies.get(id);
  }

  listPolicies(category?: PolicyCategory): Policy[] {
    const policies = Array.from(this.policies.values());
    if (category) {
      return policies.filter(p => p.category === category);
    }
    return policies;
  }

  async validate(context: ValidationContext, policyIds?: string[]): Promise<ValidationReport> {
    const policiesToRun = policyIds
      ? policyIds.map(id => this.policies.get(id)).filter((p): p is Policy => p !== undefined)
      : Array.from(this.policies.values());

    const violations: Violation[] = [];
    let passedCount = 0;

    for (const policy of policiesToRun) {
      // Check if disabled
      if (this.config.disabled?.includes(policy.id)) continue;
      if (this.config.enabled && !this.config.enabled.includes(policy.id)) continue;

      const result = await policy.validate(context);
      if (result.passed) {
        passedCount++;
      } else {
        violations.push(...result.violations);
      }
    }

    return {
      passed: violations.length === 0,
      totalPolicies: policiesToRun.length,
      passedPolicies: passedCount,
      failedPolicies: policiesToRun.length - passedCount,
      violations,
      timestamp: new Date().toISOString(),
    };
  }

  async validateFile(filePath: string, policyIds?: string[]): Promise<ValidationReport> {
    const content = await fs.readFile(filePath, 'utf-8');
    return this.validate({ filePath, content }, policyIds);
  }

  async validateProject(projectPath: string, policyIds?: string[]): Promise<ValidationReport> {
    return this.validate({ projectPath }, policyIds);
  }

  async fix(context: ValidationContext, policyIds?: string[]): Promise<FixResult[]> {
    const policiesToRun = policyIds
      ? policyIds.map(id => this.policies.get(id)).filter((p): p is Policy => p !== undefined)
      : Array.from(this.policies.values());

    const results: FixResult[] = [];

    for (const policy of policiesToRun) {
      if (policy.fix) {
        const result = await policy.fix(context);
        results.push(result);
      }
    }

    return results;
  }
}

// ============================================================
// Built-in Constitution Policies (9 Articles)
// ============================================================

/**
 * Constitution policies implementing the 9 Articles
 */
export const constitutionPolicies: Policy[] = [
  {
    id: 'CONST-001',
    name: 'Library-First',
    description: 'Article I: Features must start as independent libraries',
    severity: 'error',
    category: 'constitution',
    async validate(ctx: ValidationContext): Promise<PolicyResult> {
      // Check if packages/ directory exists and has proper structure
      if (!ctx.projectPath) {
        return { passed: true, violations: [] };
      }
      
      try {
        const packagesDir = path.join(ctx.projectPath, 'packages');
        await fs.access(packagesDir);
        return { passed: true, violations: [] };
      } catch {
        return {
          passed: false,
          violations: [{
            policyId: 'CONST-001',
            message: 'Project must have a packages/ directory for library-first architecture',
            severity: 'error',
          }],
        };
      }
    },
  },
  {
    id: 'CONST-002',
    name: 'CLI Interface',
    description: 'Article II: All libraries must expose CLI interface',
    severity: 'error',
    category: 'constitution',
    async validate(ctx: ValidationContext): Promise<PolicyResult> {
      // Check for bin/ directory or bin field in package.json
      if (!ctx.projectPath) {
        return { passed: true, violations: [] };
      }
      
      try {
        const pkgPath = path.join(ctx.projectPath, 'package.json');
        const pkg = JSON.parse(await fs.readFile(pkgPath, 'utf-8'));
        if (pkg.bin) {
          return { passed: true, violations: [] };
        }
        
        const binDir = path.join(ctx.projectPath, 'bin');
        await fs.access(binDir);
        return { passed: true, violations: [] };
      } catch {
        return {
          passed: false,
          violations: [{
            policyId: 'CONST-002',
            message: 'Project must have CLI interface (bin/ directory or bin field in package.json)',
            severity: 'error',
          }],
        };
      }
    },
  },
  {
    id: 'CONST-003',
    name: 'Test-First',
    description: 'Article III: Red-Green-Blue test cycle required',
    severity: 'error',
    category: 'constitution',
    async validate(ctx: ValidationContext): Promise<PolicyResult> {
      // Check for test files
      if (!ctx.projectPath) {
        return { passed: true, violations: [] };
      }
      
      // Simple check: look for __tests__ or *.test.ts files
      const hasTests = async (dir: string): Promise<boolean> => {
        try {
          const entries = await fs.readdir(dir, { withFileTypes: true });
          for (const entry of entries) {
            if (entry.name === '__tests__' || entry.name.includes('.test.')) {
              return true;
            }
            if (entry.isDirectory() && !entry.name.startsWith('.') && entry.name !== 'node_modules') {
              if (await hasTests(path.join(dir, entry.name))) {
                return true;
              }
            }
          }
        } catch {
          // Ignore errors
        }
        return false;
      };
      
      if (await hasTests(ctx.projectPath)) {
        return { passed: true, violations: [] };
      }
      
      return {
        passed: false,
        violations: [{
          policyId: 'CONST-003',
          message: 'Project must have test files (__tests__/ or *.test.ts)',
          severity: 'error',
        }],
      };
    },
  },
  {
    id: 'CONST-004',
    name: 'EARS Format',
    description: 'Article IV: Requirements must use EARS format',
    severity: 'error',
    category: 'constitution',
    async validate(ctx: ValidationContext): Promise<PolicyResult> {
      // Check if requirements files use EARS patterns
      if (ctx.content && ctx.filePath?.includes('REQ-')) {
        const earsPatterns = [
          /THE\s+\w+\s+SHALL/i,
          /WHEN\s+.+,\s+THE\s+\w+\s+SHALL/i,
          /WHILE\s+.+,\s+THE\s+\w+\s+SHALL/i,
          /IF\s+.+,\s+THEN\s+THE\s+\w+\s+SHALL/i,
        ];
        
        const hasEars = earsPatterns.some(pattern => pattern.test(ctx.content!));
        if (hasEars) {
          return { passed: true, violations: [] };
        }
        
        return {
          passed: false,
          violations: [{
            policyId: 'CONST-004',
            message: 'Requirements file must use EARS format (THE system SHALL...)',
            severity: 'error',
            location: { file: ctx.filePath },
          }],
        };
      }
      
      return { passed: true, violations: [] };
    },
  },
  {
    id: 'CONST-005',
    name: 'Traceability',
    description: 'Article V: 100% traceability from requirements to code',
    severity: 'error',
    category: 'constitution',
    async validate(ctx: ValidationContext): Promise<PolicyResult> {
      // Check for traceability matrix
      if (!ctx.projectPath) {
        return { passed: true, violations: [] };
      }
      
      try {
        const traceDir = path.join(ctx.projectPath, 'storage', 'traceability');
        await fs.access(traceDir);
        return { passed: true, violations: [] };
      } catch {
        return {
          passed: false,
          violations: [{
            policyId: 'CONST-005',
            message: 'Project must have storage/traceability/ directory for traceability tracking',
            severity: 'error',
          }],
        };
      }
    },
  },
  {
    id: 'CONST-006',
    name: 'Project Memory',
    description: 'Article VI: Reference steering/ before decisions',
    severity: 'warning',
    category: 'constitution',
    async validate(ctx: ValidationContext): Promise<PolicyResult> {
      // Check for steering/ directory
      if (!ctx.projectPath) {
        return { passed: true, violations: [] };
      }
      
      try {
        const steeringDir = path.join(ctx.projectPath, 'steering');
        await fs.access(steeringDir);
        return { passed: true, violations: [] };
      } catch {
        return {
          passed: false,
          violations: [{
            policyId: 'CONST-006',
            message: 'Project must have steering/ directory for project memory',
            severity: 'warning',
          }],
        };
      }
    },
  },
  {
    id: 'CONST-007',
    name: 'Design Patterns',
    description: 'Article VII: Document applied design patterns',
    severity: 'warning',
    category: 'constitution',
    async validate(ctx: ValidationContext): Promise<PolicyResult> {
      // Check for design documentation
      if (!ctx.projectPath) {
        return { passed: true, violations: [] };
      }
      
      try {
        const designDir = path.join(ctx.projectPath, 'storage', 'design');
        await fs.access(designDir);
        return { passed: true, violations: [] };
      } catch {
        return {
          passed: false,
          violations: [{
            policyId: 'CONST-007',
            message: 'Project should have storage/design/ directory for design documentation',
            severity: 'warning',
          }],
        };
      }
    },
  },
  {
    id: 'CONST-008',
    name: 'Decision Records',
    description: 'Article VIII: Record all decisions as ADRs',
    severity: 'warning',
    category: 'constitution',
    async validate(ctx: ValidationContext): Promise<PolicyResult> {
      // Check for ADR directory
      if (!ctx.projectPath) {
        return { passed: true, violations: [] };
      }
      
      try {
        const adrDir = path.join(ctx.projectPath, 'docs', 'decisions');
        await fs.access(adrDir);
        return { passed: true, violations: [] };
      } catch {
        return {
          passed: false,
          violations: [{
            policyId: 'CONST-008',
            message: 'Project should have docs/decisions/ directory for ADRs',
            severity: 'warning',
          }],
        };
      }
    },
  },
  {
    id: 'CONST-009',
    name: 'Quality Gates',
    description: 'Article IX: Verify quality before phase transitions',
    severity: 'error',
    category: 'constitution',
    async validate(ctx: ValidationContext): Promise<PolicyResult> {
      // Check for quality gate configuration or CI
      if (!ctx.projectPath) {
        return { passed: true, violations: [] };
      }
      
      try {
        // Check for CI configuration
        const ciPath = path.join(ctx.projectPath, '.github', 'workflows');
        await fs.access(ciPath);
        return { passed: true, violations: [] };
      } catch {
        // Also accept vitest config as quality gate
        try {
          const vitestConfig = path.join(ctx.projectPath, 'vitest.config.ts');
          await fs.access(vitestConfig);
          return { passed: true, violations: [] };
        } catch {
          return {
            passed: false,
            violations: [{
              policyId: 'CONST-009',
              message: 'Project must have quality gates (.github/workflows/ or vitest.config.ts)',
              severity: 'error',
            }],
          };
        }
      }
    },
  },
];

// FastRender Non-negotiables (v3.6.0)
export * from './non-negotiables/index.js';

// FastRender Balance Rules (v3.6.0)
export * from './balance/index.js';
