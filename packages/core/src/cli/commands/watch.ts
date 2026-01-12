/**
 * Watch Command Registration
 *
 * Implements: TSK-WATCH-007, REQ-WATCH-006
 * @see DES-DX-v3.1.0 Section Watch Module
 */

import type { Command } from 'commander';
import { createWatchCommand } from '../../watch/watch-command.js';

/**
 * Register watch command to CLI
 */
export function registerWatchCommand(program: Command): void {
  program.addCommand(createWatchCommand());
}

export { registerWatchCommand as default };
