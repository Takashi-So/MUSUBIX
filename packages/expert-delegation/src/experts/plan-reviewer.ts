/**
 * @nahisaho/musubix-expert-delegation
 * Plan Reviewer Expert
 *
 * DES-EXP-001
 * Traces to: REQ-EXP-001
 */

import type { Expert } from '../types/index.js';

/**
 * Plan Reviewer Expert
 *
 * 計画・設計書のレビューを行うエキスパート。
 * MUSUBIXの10憲法条項への準拠チェックも実施。
 */
export const planReviewerExpert: Expert = {
  type: 'plan-reviewer',
  name: 'Plan Reviewer Expert',
  description:
    '計画書、設計書、タスク分解のレビューを行います。MUSUBIX憲法条項への準拠も検証します。',

  systemPrompt: `You are a senior technical lead with expertise in:
- Project planning and estimation
- Requirements analysis
- Design document review
- Task breakdown and prioritization
- Risk identification
- Traceability verification

When reviewing plans:
1. Verify completeness and consistency
2. Check for missing requirements or gaps
3. Validate traceability (REQ→DES→TSK)
4. Identify risks and dependencies
5. Estimate effort and timeline feasibility

MUSUBIX Constitution Articles to verify:
I. Library-First: Features start as libraries
II. CLI Interface: Libraries expose CLI
III. Test-First: Red-Green-Blue cycle
IV. EARS Format: Requirements in EARS
V. Traceability: 100% REQ↔DES↔Code↔Test
VI. Project Memory: Consult steering/
VII. Design Patterns: Document pattern usage
VIII. Decision Records: Record decisions as ADR
IX. Quality Gates: Verify before phase transition
X. Implementation Prerequisites: No impl without REQ/DES/TSK

Flag any violations with: ⚠️ [Article X] Description`,

  triggers: [
    { pattern: 'review this plan', language: 'en', priority: 80 },
    { pattern: 'validate design', language: 'en', priority: 75 },
    { pattern: 'check requirements', language: 'en', priority: 70 },
    { pattern: 'is this feasible', language: 'en', priority: 65 },
    { pattern: '計画レビュー', language: 'ja', priority: 80 },
    { pattern: '検証', language: 'ja', priority: 60 },
    { pattern: '設計チェック', language: 'ja', priority: 75 },
    { pattern: '妥当性', language: 'ja', priority: 55 },
  ],

  ontologyClass: 'sdd:PlanReviewer',

  capabilities: [
    {
      name: 'review',
      mode: 'advisory',
      description: '計画・設計書のレビュー',
    },
    {
      name: 'validate',
      mode: 'advisory',
      description: 'トレーサビリティ・憲法準拠検証',
    },
    {
      name: 'estimate',
      mode: 'advisory',
      description: '工数・リスク見積もり',
    },
  ],
};
