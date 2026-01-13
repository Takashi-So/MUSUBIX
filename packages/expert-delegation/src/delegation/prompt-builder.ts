/**
 * @nahisaho/musubix-expert-delegation
 * Prompt Builder
 *
 * DES-DEL-001
 * Traces to: REQ-DEL-001
 */

import type {
  Expert,
  DelegationContext,
  DelegationTask,
  TraceLink,
} from '../types/index.js';

/**
 * プロンプトセクション
 */
interface PromptSection {
  title: string;
  content: string;
  required: boolean;
}

/**
 * Prompt Builder
 *
 * 7セクション + EARS拡張形式のプロンプトを構築する。
 */
export class PromptBuilder {
  private sections: PromptSection[] = [];

  /**
   * エキスパートとコンテキストからプロンプトを構築
   */
  build(expert: Expert, context: DelegationContext): string {
    this.sections = [];

    // 1. System Prompt
    this.addSection('System Prompt', expert.systemPrompt, true);

    // 2. User Request
    this.addSection('User Request', context.userMessage, true);

    // 3. Active Files
    if (context.activeFiles && context.activeFiles.length > 0) {
      this.addSection('Active Files', this.formatActiveFiles(context), false);
    }

    // 4. Related Context
    if (context.relatedRequirements || context.relatedDesigns) {
      this.addSection(
        'Related Context',
        this.formatRelatedContext(context),
        false
      );
    }

    // 5. Constraints
    if (context.constitutionArticles && context.constitutionArticles.length > 0) {
      this.addSection(
        'MUSUBIX Constraints',
        this.formatConstraints(context),
        false
      );
    }

    // 6. Expected Output
    this.addSection(
      'Expected Output',
      this.formatExpectedOutput(expert, context),
      true
    );

    // 7. Traceability
    if (context.traceLinks && context.traceLinks.length > 0) {
      this.addSection(
        'Traceability',
        this.formatTraceLinks(context.traceLinks),
        false
      );
    }

    return this.render();
  }

  /**
   * タスクからプロンプトを構築
   */
  buildFromTask(expert: Expert, task: DelegationTask): string {
    return this.build(expert, task.context);
  }

  /**
   * EARS形式の要件分析プロンプトを構築
   */
  buildEarsAnalysisPrompt(
    requirementText: string,
    suggestedPattern?: string
  ): string {
    return `## EARS Requirements Analysis

### Input Text
${requirementText}

### Analysis Instructions
1. Identify the type of requirement (functional, non-functional, constraint)
2. Detect the appropriate EARS pattern:
   - Ubiquitous: THE [system] SHALL [requirement]
   - Event-driven: WHEN [event], THE [system] SHALL [response]
   - State-driven: WHILE [state], THE [system] SHALL [response]
   - Unwanted: THE [system] SHALL NOT [behavior]
   - Optional: IF [condition], THEN THE [system] SHALL [response]
3. Convert to EARS format
4. Assign priority (P0: Critical, P1: Important, P2: Optional)
5. Generate unique ID (REQ-XXX-NNN)

${suggestedPattern ? `### Suggested Pattern\n${suggestedPattern}\n` : ''}

### Expected Output Format
\`\`\`
ID: REQ-XXX-001
Pattern: [ears-pattern]
Priority: [P0|P1|P2]
Statement: [EARS formatted requirement]
Rationale: [why this pattern was chosen]
\`\`\``;
  }

  /**
   * 形式検証プロンプトを構築
   */
  buildFormalVerificationPrompt(code: string, specification?: string): string {
    return `## Formal Verification Request

### Code to Verify
\`\`\`
${code}
\`\`\`

${specification ? `### Specification\n${specification}\n` : ''}

### Verification Tasks
1. Generate preconditions and postconditions (Hoare logic)
2. Identify invariants
3. Translate to Z3/SMT-LIB format
4. Suggest Lean 4 theorem if applicable
5. Report verification result

### Expected Output Format
\`\`\`
Precondition: [condition]
Postcondition: [condition]
Invariants: [list]
Z3 Query: [SMT-LIB]
Verification: [PASS|FAIL|UNKNOWN]
Confidence: [0.0-1.0]
\`\`\``;
  }

  /**
   * オントロジー推論プロンプトを構築
   */
  buildOntologyReasoningPrompt(
    query: string,
    contextTriples?: Array<{ s: string; p: string; o: string }>
  ): string {
    let prompt = `## Ontology Reasoning Request

### Query
${query}

### Reasoning Tasks
1. Identify relevant concepts and relationships
2. Apply inference rules (RDFS/OWL)
3. Check consistency
4. Generate derived knowledge
5. Explain reasoning chain

`;

    if (contextTriples && contextTriples.length > 0) {
      prompt += `### Context Knowledge
\`\`\`turtle
${contextTriples.map((t) => `${t.s} ${t.p} ${t.o} .`).join('\n')}
\`\`\`

`;
    }

    prompt += `### Expected Output Format
\`\`\`
Inferred Knowledge:
  - [subject] [predicate] [object]
Reasoning Chain:
  1. [step]
  2. [step]
Confidence: [0.0-1.0]
Consistency: [CONSISTENT|INCONSISTENT|UNKNOWN]
\`\`\``;

    return prompt;
  }

  private addSection(title: string, content: string, required: boolean): void {
    this.sections.push({ title, content, required });
  }

  private formatActiveFiles(context: DelegationContext): string {
    if (!context.activeFiles) return '';

    return context.activeFiles
      .map((file) => {
        const preview = file.content
          ? `\n\`\`\`\n${file.content.slice(0, 500)}${file.content.length > 500 ? '\n...' : ''}\n\`\`\``
          : '';
        return `- ${file.path}${preview}`;
      })
      .join('\n\n');
  }

  private formatRelatedContext(context: DelegationContext): string {
    const parts: string[] = [];

    if (context.relatedRequirements && context.relatedRequirements.length > 0) {
      parts.push('### Related Requirements');
      parts.push(context.relatedRequirements.map((r) => `- ${r}`).join('\n'));
    }

    if (context.relatedDesigns && context.relatedDesigns.length > 0) {
      parts.push('### Related Designs');
      parts.push(context.relatedDesigns.map((d) => `- ${d}`).join('\n'));
    }

    return parts.join('\n\n');
  }

  private formatConstraints(context: DelegationContext): string {
    if (!context.constitutionArticles) return '';

    return context.constitutionArticles
      .map((article, i) => `${i + 1}. ${article}`)
      .join('\n');
  }

  private formatExpectedOutput(
    expert: Expert,
    context: DelegationContext
  ): string {
    const mode = context.mode ?? 'advisory';

    if (mode === 'advisory') {
      return `Provide analysis and recommendations. Do NOT generate code directly.
Focus on:
- Identifying issues and concerns
- Suggesting improvements
- Explaining trade-offs
- Providing actionable recommendations`;
    } else {
      const hasCodeGenCapability = expert.capabilities.some(
        (cap) => cap.name === 'code-generation'
      );
      return `Generate implementation code following best practices.
Requirements:
- Include inline comments
- Follow ${hasCodeGenCapability ? 'project coding standards' : 'general best practices'}
- Add traceability comments (// Traces to: REQ-XXX)
- Ensure type safety`;
    }
  }

  private formatTraceLinks(links: TraceLink[]): string {
    return links
      .map((link) => `- ${link.sourceId} → ${link.targetId} (${link.type})`)
      .join('\n');
  }

  private render(): string {
    return this.sections
      .map((section) => `## ${section.title}\n\n${section.content}`)
      .join('\n\n---\n\n');
  }
}

/**
 * PromptBuilderのファクトリ関数
 */
export function createPromptBuilder(): PromptBuilder {
  return new PromptBuilder();
}
