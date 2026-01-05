/**
 * Prompt Renderer - Renders context-aware prompts
 *
 * @module cli/repl/prompt-renderer
 * @traces DES-CLI-004, REQ-CLI-004
 * @pattern Template Method - Base prompt with customizable parts
 */

import type { ProjectContext, ReplConfig } from './types.js';

// ANSI color codes
const COLORS = {
  reset: '\x1b[0m',
  bold: '\x1b[1m',
  red: '\x1b[31m',
  green: '\x1b[32m',
  yellow: '\x1b[33m',
  blue: '\x1b[34m',
  magenta: '\x1b[35m',
  cyan: '\x1b[36m',
  gray: '\x1b[90m',
};

/**
 * Prompt renderer for REPL
 *
 * Renders context-aware prompts with project name, phase, and status colors.
 */
export class PromptRenderer {
  private context: ProjectContext = {};
  private hasError: boolean = false;
  private config: ReplConfig['prompt'];

  constructor(config?: Partial<ReplConfig['prompt']>) {
    this.config = {
      showProject: config?.showProject ?? true,
      showPhase: config?.showPhase ?? true,
      useColor: config?.useColor ?? true,
      defaultPrompt: config?.defaultPrompt ?? 'musubix> ',
    };
  }

  /**
   * Render the prompt string
   */
  render(): string {
    const parts: string[] = [];

    // Add project name
    if (this.config.showProject && this.context.name) {
      parts.push(this.colorize(this.context.name, 'cyan'));
    }

    // Add phase
    if (this.config.showPhase && this.context.phase) {
      const phaseColor = this.getPhaseColor(this.context.phase);
      parts.push(this.colorize(`[${this.context.phase}]`, phaseColor));
    }

    // Build prompt
    if (parts.length > 0) {
      const prefix = parts.join(' ');
      const promptChar = this.hasError
        ? this.colorize('✗', 'red')
        : this.colorize('❯', 'green');
      return `${prefix} ${promptChar} `;
    }

    // Default prompt
    const color = this.hasError ? 'red' : 'green';
    return this.colorize(this.config.defaultPrompt, color);
  }

  /**
   * Render continuation prompt (for multi-line input)
   */
  renderContinuation(): string {
    return this.colorize('... ', 'gray');
  }

  /**
   * Set project context
   * @param context - Current project context
   */
  setContext(context: ProjectContext): void {
    this.context = { ...context };
  }

  /**
   * Update context partially
   */
  updateContext(updates: Partial<ProjectContext>): void {
    this.context = { ...this.context, ...updates };
  }

  /**
   * Set error state
   * @param hasError - Whether there's an error
   */
  setErrorState(hasError: boolean): void {
    this.hasError = hasError;
  }

  /**
   * Clear context
   */
  clearContext(): void {
    this.context = {};
  }

  /**
   * Get phase color
   */
  private getPhaseColor(phase: ProjectContext['phase']): keyof typeof COLORS {
    switch (phase) {
      case 'requirements':
        return 'blue';
      case 'design':
        return 'magenta';
      case 'implementation':
        return 'yellow';
      case 'test':
        return 'green';
      default:
        return 'gray';
    }
  }

  /**
   * Apply color to text
   */
  private colorize(text: string, color: keyof typeof COLORS): string {
    if (!this.config.useColor) {
      return text;
    }
    return `${COLORS[color]}${text}${COLORS.reset}`;
  }

  /**
   * Enable/disable colors
   */
  setColorMode(useColor: boolean): void {
    this.config.useColor = useColor;
  }

  /**
   * Get current context
   */
  getContext(): ProjectContext {
    return { ...this.context };
  }
}

/**
 * Create a new prompt renderer
 */
export function createPromptRenderer(config?: Partial<ReplConfig['prompt']>): PromptRenderer {
  return new PromptRenderer(config);
}
