/**
 * MCP Synthesis Prompts
 * 
 * Prompt definitions for program synthesis via MCP
 * 
 * @packageDocumentation
 * @module prompts/synthesis
 * 
 * @see TSK-INT-103 - MCP Synthesis Tools
 * @see REQ-INT-103 - MCP Integration
 */

import type { PromptDefinition } from '../types.js';

/**
 * Synthesis guidance prompt
 */
export const synthesisGuidancePrompt: PromptDefinition = {
  name: 'synthesis_guidance',
  description: 'Guide the user through creating input/output examples for program synthesis',
  arguments: [
    {
      name: 'domain',
      description: 'The domain of the transformation (string, array, number, object)',
      required: false,
    },
    {
      name: 'taskDescription',
      description: 'Natural language description of the desired transformation',
      required: false,
    },
  ],
  handler: async (args) => {
    const domain = args?.domain as string || 'unknown';
    const taskDescription = args?.taskDescription as string || '';

    const prompt = `You are helping a user create input/output examples for program synthesis.

## Context
- Domain: ${domain}
- Task: ${taskDescription || 'Not specified'}

## Guidelines for Creating Good Examples

### 1. Quantity
- Provide at least 3-5 examples
- More examples help disambiguate the transformation

### 2. Diversity
Include examples that cover:
- Normal/typical cases
- Edge cases (empty strings, zero, empty arrays)
- Boundary cases (very long strings, large numbers)
- Special characters or unusual inputs

### 3. Consistency
- All examples should follow the same transformation pattern
- Be precise about whitespace, capitalization, etc.

### 4. Format
Provide examples in this format:
\`\`\`json
{
  "examples": [
    { "input": "hello", "output": "HELLO" },
    { "input": "world", "output": "WORLD" }
  ]
}
\`\`\`

## Next Steps
1. Ask the user to describe what transformation they want
2. Help them create diverse examples
3. Validate example quality before synthesis
4. Run synthesis and iterate if needed`;

    return {
      description: 'Synthesis guidance for creating good examples',
      messages: [
        {
          role: 'user',
          content: {
            type: 'text',
            text: prompt,
          },
        },
      ],
    };
  },
};

/**
 * Pattern explanation prompt
 */
export const patternExplanationPrompt: PromptDefinition = {
  name: 'synthesis_explain_pattern',
  description: 'Explain a synthesized pattern or program in natural language',
  arguments: [
    {
      name: 'pattern',
      description: 'The synthesized pattern or program to explain',
      required: true,
    },
    {
      name: 'examples',
      description: 'The examples used for synthesis (JSON array)',
      required: false,
    },
  ],
  handler: async (args) => {
    const pattern = args?.pattern as string || '';
    const examplesStr = args?.examples as string || '[]';

    let examplesText = '';
    try {
      const examples = JSON.parse(examplesStr);
      if (Array.isArray(examples) && examples.length > 0) {
        examplesText = `\n\n## Examples Used\n${examples.map((e: { input: unknown; output: unknown }, i: number) => 
          `${i + 1}. Input: \`${JSON.stringify(e.input)}\` → Output: \`${JSON.stringify(e.output)}\``
        ).join('\n')}`;
      }
    } catch {
      // Ignore parse errors
    }

    const prompt = `Please explain the following synthesized program/pattern in natural language:

## Synthesized Pattern
\`\`\`
${pattern}
\`\`\`
${examplesText}

## Explanation Requirements
1. **What it does**: Describe the transformation in simple terms
2. **How it works**: Explain the steps involved
3. **Edge cases**: Note any potential edge cases or limitations
4. **Usage examples**: Show how to use this pattern

Please provide a clear, concise explanation that a developer can understand.`;

    return {
      description: 'Pattern explanation request',
      messages: [
        {
          role: 'user',
          content: {
            type: 'text',
            text: prompt,
          },
        },
      ],
    };
  },
};

/**
 * All synthesis prompts
 */
export const SYNTHESIS_PROMPTS: PromptDefinition[] = [
  synthesisGuidancePrompt,
  patternExplanationPrompt,
];

/**
 * Get synthesis prompts
 */
export function getSynthesisPrompts(): PromptDefinition[] {
  return SYNTHESIS_PROMPTS;
}

export default SYNTHESIS_PROMPTS;
