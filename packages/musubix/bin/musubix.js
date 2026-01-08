#!/usr/bin/env node
/**
 * MUSUBIX CLI - Delegates to @nahisaho/musubix-core
 */
import('@nahisaho/musubix-core/dist/cli/index.js').catch(() => {
  require('@nahisaho/musubix-core/dist/cli/index.js');
});
