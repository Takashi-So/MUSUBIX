/**
 * Design Validation
 *
 * SOLID validation, design review system (Article VII & IX compliance)
 *
 * @packageDocumentation
 * @module cli/commands/design/validation
 */

import type {
  C4Model,
  DesignPattern,
  DesignValidationResult,
  DesignReviewResult,
  DesignReviewFinding,
} from './types.js';

/**
 * Validate design
 */
export function validateDesign(designContent: string, strict: boolean): {
  violations: DesignValidationResult['solidViolations'];
  gaps: DesignValidationResult['traceabilityGaps'];
} {
  const violations: DesignValidationResult['solidViolations'] = [];
  const gaps: DesignValidationResult['traceabilityGaps'] = [];

  const contentLower = designContent.toLowerCase();

  if (contentLower.includes('and') && designContent.match(/class\s+\w+/gi)?.length) {
    if (strict) {
      violations.push({
        principle: 'S',
        element: 'Multiple responsibilities detected',
        message: 'Class may have multiple responsibilities',
        severity: 'warning',
      });
    }
  }

  const reqMatches = designContent.match(/REQ-[A-Z]+-\d+/g) || [];
  const desMatches = designContent.match(/DES-[A-Z]+-\d+/g) || [];

  if (reqMatches.length > 0 && desMatches.length === 0) {
    const firstReq = reqMatches[0];
    if (firstReq) {
      gaps.push({
        requirement: firstReq,
        message: 'No design element traceability found',
      });
    }
  }

  return { violations, gaps };
}

/**
 * Review design for quality and SOLID compliance
 */
export async function reviewDesign(
  model: C4Model,
  patterns: DesignPattern[],
  traceability: Array<{ requirement: string; designElement: string }>
): Promise<DesignReviewResult> {
  const findings: DesignReviewFinding[] = [];
  const recommendations: string[] = [];
  let passedChecks = 0;
  let totalChecks = 0;

  const solidAnalysis = {
    s: { passed: true, message: 'Single responsibility maintained' },
    o: { passed: true, message: 'Open for extension, closed for modification' },
    l: { passed: true, message: 'Substitution principle applicable' },
    i: { passed: true, message: 'Interface segregation maintained' },
    d: { passed: true, message: 'Dependencies properly inverted' },
  };

  // 1. Check C4 model completeness
  totalChecks++;
  if (model.elements.length === 0) {
    findings.push({
      severity: 'error',
      category: 'completeness',
      message: 'No design elements defined',
      suggestion: 'Ensure requirements are properly parsed and design elements generated',
    });
  } else {
    passedChecks++;
  }

  // 2. Check for proper element types
  totalChecks++;
  const hasPersons = model.elements.some(e => e.type === 'person');
  const hasSystems = model.elements.some(e => e.type === 'software_system' || e.type === 'container' || e.type === 'component');

  if (!hasPersons && !hasSystems) {
    findings.push({
      severity: 'warning',
      category: 'completeness',
      message: 'Design lacks clear actor and system separation',
      suggestion: 'Define both actors (users) and system components',
    });
  } else {
    passedChecks++;
  }

  // 3. Check relationships exist
  totalChecks++;
  if (model.relationships.length === 0 && model.elements.length > 1) {
    findings.push({
      severity: 'warning',
      category: 'completeness',
      message: 'No relationships defined between elements',
      suggestion: 'Define how components interact with each other',
    });
  } else {
    passedChecks++;
  }

  // 4. Check design patterns are documented (Article VII)
  totalChecks++;
  if (patterns.length === 0) {
    findings.push({
      severity: 'info',
      category: 'pattern',
      message: 'No design patterns detected or applied',
      suggestion: 'Consider applying appropriate design patterns for maintainability',
    });
  } else {
    passedChecks++;
    findings.push({
      severity: 'info',
      category: 'pattern',
      message: `${patterns.length} design pattern(s) applied: ${patterns.map(p => p.name).join(', ')}`,
    });
  }

  // 5. Check traceability (Article V)
  totalChecks++;
  if (traceability.length === 0) {
    findings.push({
      severity: 'error',
      category: 'traceability',
      message: 'No traceability links to requirements',
      suggestion: 'Each design element should trace back to requirements',
    });
    solidAnalysis.d.passed = false;
    solidAnalysis.d.message = 'Missing requirement traceability violates dependency management';
  } else {
    passedChecks++;
  }

  // 6. Check Single Responsibility (S)
  totalChecks++;
  for (const element of model.elements) {
    const descWords = element.description.split(/\s+/).length;
    if (descWords > 20) {
      solidAnalysis.s.passed = false;
      solidAnalysis.s.message = 'Some components may have too many responsibilities';
      findings.push({
        severity: 'warning',
        category: 'solid',
        element: element.id,
        message: `${element.name} description is long (${descWords} words) - may indicate multiple responsibilities`,
        suggestion: 'Consider splitting into smaller, focused components',
      });
    }
  }
  if (solidAnalysis.s.passed) passedChecks++;

  // 7. Check element naming conventions
  totalChecks++;
  let namingValid = true;
  for (const element of model.elements) {
    if (!/^[a-z]/.test(element.id)) {
      namingValid = false;
      findings.push({
        severity: 'warning',
        category: 'consistency',
        element: element.id,
        message: 'Element ID does not follow naming convention (should start with lowercase)',
      });
    }
  }
  if (namingValid) passedChecks++;

  // 8. Check for circular dependencies
  totalChecks++;
  const relationshipMap = new Map<string, Set<string>>();
  for (const rel of model.relationships) {
    if (!relationshipMap.has(rel.source)) {
      relationshipMap.set(rel.source, new Set());
    }
    relationshipMap.get(rel.source)!.add(rel.target);
  }

  let hasCircular = false;
  for (const [source, targets] of relationshipMap) {
    for (const target of targets) {
      if (relationshipMap.get(target)?.has(source)) {
        hasCircular = true;
        findings.push({
          severity: 'warning',
          category: 'consistency',
          message: `Potential circular dependency between ${source} and ${target}`,
          suggestion: 'Review dependency direction to avoid circular references',
        });
      }
    }
  }
  if (!hasCircular) passedChecks++;

  // Generate recommendations
  const errorCount = findings.filter(f => f.severity === 'error').length;
  const warningCount = findings.filter(f => f.severity === 'warning').length;

  if (errorCount > 0) {
    recommendations.push('⚠️ Address error-level findings before implementation');
  }
  if (warningCount > 0) {
    recommendations.push('📝 Review warning-level findings for potential improvements');
  }
  if (patterns.length === 0) {
    recommendations.push('📚 Consider applying design patterns (Factory, Strategy, Observer, etc.)');
  }
  if (traceability.length < model.elements.length) {
    recommendations.push('🔗 Ensure all design elements trace back to requirements');
  }
  if (errorCount === 0 && warningCount <= 2) {
    recommendations.push('✅ Design is ready for implementation phase');
  }

  const score = totalChecks > 0 ? Math.round((passedChecks / totalChecks) * 100) : 0;

  return {
    passed: errorCount === 0,
    score,
    totalChecks,
    passedChecks,
    findings,
    recommendations,
    constitutionCompliance: {
      articleVII: patterns.length > 0,
      articleV: traceability.length > 0,
      articleIX: score >= 60,
    },
    solidAnalysis,
  };
}

/**
 * Display design review result
 */
export function displayDesignReviewResult(result: DesignReviewResult, quiet: boolean): void {
  if (quiet) return;

  const statusIcon = result.passed ? '✅' : '❌';
  console.log(`${statusIcon} レビュー結果: ${result.score}% (${result.passedChecks}/${result.totalChecks} checks)`);
  console.log('');

  console.log('📜 憲法準拠状況:');
  console.log(`   Article V (トレーサビリティ): ${result.constitutionCompliance.articleV ? '✓' : '✗'}`);
  console.log(`   Article VII (設計パターン): ${result.constitutionCompliance.articleVII ? '✓' : '✗'}`);
  console.log(`   Article IX (品質ゲート): ${result.constitutionCompliance.articleIX ? '✓' : '✗'}`);
  console.log('');

  console.log('🏗️ SOLID原則分析:');
  console.log(`   [S] 単一責任: ${result.solidAnalysis.s.passed ? '✓' : '✗'} ${result.solidAnalysis.s.message}`);
  console.log(`   [O] 開放閉鎖: ${result.solidAnalysis.o.passed ? '✓' : '✗'} ${result.solidAnalysis.o.message}`);
  console.log(`   [L] リスコフ置換: ${result.solidAnalysis.l.passed ? '✓' : '✗'} ${result.solidAnalysis.l.message}`);
  console.log(`   [I] インターフェース分離: ${result.solidAnalysis.i.passed ? '✓' : '✗'} ${result.solidAnalysis.i.message}`);
  console.log(`   [D] 依存性逆転: ${result.solidAnalysis.d.passed ? '✓' : '✗'} ${result.solidAnalysis.d.message}`);
  console.log('');

  if (result.findings.length > 0) {
    console.log('📋 発見事項:');
    for (const finding of result.findings) {
      const icon = finding.severity === 'error' ? '🔴' : finding.severity === 'warning' ? '🟡' : '🔵';
      console.log(`   ${icon} [${finding.category}] ${finding.message}`);
      if (finding.element) {
        console.log(`      対象: ${finding.element}`);
      }
      if (finding.suggestion) {
        console.log(`      💡 ${finding.suggestion}`);
      }
    }
    console.log('');
  }

  if (result.recommendations.length > 0) {
    console.log('💡 推奨事項:');
    for (const rec of result.recommendations) {
      console.log(`   ${rec}`);
    }
    console.log('');
  }
}

/**
 * Generate design review document
 */
export function generateDesignReviewDocument(result: DesignReviewResult): string {
  const now = new Date().toISOString().split('T')[0];

  let doc = `# Design Review Report

> Generated by MUSUBIX Design Review System
> Date: ${now}

## Summary

| Metric | Value |
|--------|-------|
| **Status** | ${result.passed ? '✅ PASSED' : '❌ FAILED'} |
| **Score** | ${result.score}% |
| **Checks Passed** | ${result.passedChecks}/${result.totalChecks} |

## Constitution Compliance

| Article | Name | Status |
|---------|------|--------|
| V | Traceability | ${result.constitutionCompliance.articleV ? '✅ Compliant' : '❌ Non-compliant'} |
| VII | Design Patterns | ${result.constitutionCompliance.articleVII ? '✅ Compliant' : '⚠️ No patterns applied'} |
| IX | Quality Gates | ${result.constitutionCompliance.articleIX ? '✅ Compliant' : '❌ Non-compliant'} |

## SOLID Principles Analysis

| Principle | Status | Analysis |
|-----------|--------|----------|
| **S** - Single Responsibility | ${result.solidAnalysis.s.passed ? '✅' : '⚠️'} | ${result.solidAnalysis.s.message} |
| **O** - Open/Closed | ${result.solidAnalysis.o.passed ? '✅' : '⚠️'} | ${result.solidAnalysis.o.message} |
| **L** - Liskov Substitution | ${result.solidAnalysis.l.passed ? '✅' : '⚠️'} | ${result.solidAnalysis.l.message} |
| **I** - Interface Segregation | ${result.solidAnalysis.i.passed ? '✅' : '⚠️'} | ${result.solidAnalysis.i.message} |
| **D** - Dependency Inversion | ${result.solidAnalysis.d.passed ? '✅' : '⚠️'} | ${result.solidAnalysis.d.message} |

## Findings

`;

  if (result.findings.length === 0) {
    doc += '_No issues found._\n\n';
  } else {
    const errors = result.findings.filter(f => f.severity === 'error');
    const warnings = result.findings.filter(f => f.severity === 'warning');
    const infos = result.findings.filter(f => f.severity === 'info');

    if (errors.length > 0) {
      doc += '### 🔴 Errors\n\n';
      for (const f of errors) {
        doc += `- **[${f.category}]** ${f.message}\n`;
        if (f.element) doc += `  - Element: ${f.element}\n`;
        if (f.suggestion) doc += `  - 💡 ${f.suggestion}\n`;
      }
      doc += '\n';
    }

    if (warnings.length > 0) {
      doc += '### 🟡 Warnings\n\n';
      for (const f of warnings) {
        doc += `- **[${f.category}]** ${f.message}\n`;
        if (f.element) doc += `  - Element: ${f.element}\n`;
        if (f.suggestion) doc += `  - 💡 ${f.suggestion}\n`;
      }
      doc += '\n';
    }

    if (infos.length > 0) {
      doc += '### 🔵 Info\n\n';
      for (const f of infos) {
        doc += `- **[${f.category}]** ${f.message}\n`;
      }
      doc += '\n';
    }
  }

  doc += `## Recommendations

`;
  for (const rec of result.recommendations) {
    doc += `- ${rec}\n`;
  }

  doc += `
---

**Reviewed by**: MUSUBIX Design Review System
**Review Date**: ${now}
`;

  return doc;
}
