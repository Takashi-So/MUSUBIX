/**
 * MUSUBIX Version
 * 
 * Dynamically reads version from package.json
 * 
 * @packageDocumentation
 * @module @musubix/core/version
 */

import { fileURLToPath } from 'url';
import { dirname, join } from 'path';
import { readFileSync, existsSync } from 'fs';

/**
 * Get version from package.json
 * Tries multiple locations to handle different installation scenarios
 */
function getVersion(): string {
  // Try to find package.json in various locations
  const possiblePaths = [
    // When running from source (development)
    join(dirname(fileURLToPath(import.meta.url)), '..', 'package.json'),
    join(dirname(fileURLToPath(import.meta.url)), '..', '..', 'package.json'),
    // When running from dist (production)
    join(dirname(fileURLToPath(import.meta.url)), '..', '..', 'package.json'),
    join(dirname(fileURLToPath(import.meta.url)), '..', '..', '..', 'package.json'),
  ];

  for (const pkgPath of possiblePaths) {
    try {
      if (existsSync(pkgPath)) {
        const pkg = JSON.parse(readFileSync(pkgPath, 'utf-8'));
        if (pkg.name === '@nahisaho/musubix-core' || pkg.name === 'musubix') {
          return pkg.version;
        }
      }
    } catch {
      // Continue to next path
    }
  }

  // Fallback version (should not happen in normal operation)
  return '1.1.8';
}

export const VERSION = getVersion();
