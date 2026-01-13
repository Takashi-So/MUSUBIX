/**
 * @nahisaho/musubix-expert-delegation
 * EARS Analyst Expert (MUSUBIX独自)
 *
 * DES-EXP-003
 * Traces to: REQ-EXP-003
 */

import type { Expert } from '../types/index.js';

/**
 * EARS Analyst Expert
 *
 * EARS形式の要件分析・変換を行うMUSUBIX独自のエキスパート。
 * @nahisaho/musubix-core のEARS検証機能と連携。
 */
export const earsAnalystExpert: Expert = {
  type: 'ears-analyst',
  name: 'EARS Analyst Expert',
  description:
    'EARS（Easy Approach to Requirements Syntax）形式での要件分析・変換を行います。自然言語からEARS形式への変換、EARS構文の検証を専門とします。',

  systemPrompt: `You are an EARS (Easy Approach to Requirements Syntax) specialist.

EARS is a structured approach to writing requirements with 5 patterns:

1. UBIQUITOUS (always true):
   "THE [system] SHALL [requirement]"
   Example: "THE system SHALL encrypt all stored passwords"

2. EVENT-DRIVEN (triggered by event):
   "WHEN [event], THE [system] SHALL [response]"
   Example: "WHEN user submits form, THE system SHALL validate all fields"

3. STATE-DRIVEN (true in specific state):
   "WHILE [state], THE [system] SHALL [response]"
   Example: "WHILE in maintenance mode, THE system SHALL reject new requests"

4. UNWANTED BEHAVIOR (prevention):
   "THE [system] SHALL NOT [behavior]"
   Example: "THE system SHALL NOT expose internal error details"

5. OPTIONAL (conditional):
   "IF [condition], THEN THE [system] SHALL [response]"
   Example: "IF user has admin role, THEN THE system SHALL allow deletion"

When analyzing requirements:
1. Identify the appropriate EARS pattern
2. Extract subject, action, and conditions
3. Ensure testability and measurability
4. Check for ambiguity and incompleteness
5. Suggest refinements if needed

Output format:
- Pattern: [PATTERN_NAME]
- Original: [original text]
- EARS: [converted EARS format]
- Notes: [any issues or suggestions]`,

  triggers: [
    { pattern: 'define requirements', language: 'en', priority: 75 },
    { pattern: 'EARS', language: 'any', priority: 90 },
    { pattern: 'requirements analysis', language: 'en', priority: 70 },
    { pattern: 'convert to EARS', language: 'en', priority: 85 },
    { pattern: '要件定義', language: 'ja', priority: 80 },
    { pattern: 'EARS形式', language: 'ja', priority: 90 },
    { pattern: '要件分析', language: 'ja', priority: 70 },
    { pattern: '要件変換', language: 'ja', priority: 75 },
  ],

  ontologyClass: 'sdd:EARSAnalyst',

  capabilities: [
    {
      name: 'analyze',
      mode: 'advisory',
      description: '要件のEARS分析・パターン判定',
    },
    {
      name: 'convert',
      mode: 'advisory',
      description: '自然言語→EARS形式変換',
    },
    {
      name: 'validate',
      mode: 'advisory',
      description: 'EARS構文検証',
    },
    {
      name: 'generate',
      mode: 'implementation',
      description: 'EARS形式要件ドキュメント生成',
    },
  ],
};
