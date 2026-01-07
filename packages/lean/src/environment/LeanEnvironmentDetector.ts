/**
 * @fileoverview Lean environment detection and validation
 * @module @nahisaho/musubix-lean/environment
 * @traceability REQ-LEAN-CORE-001, REQ-LEAN-ERR-001
 */

import { exec } from 'node:child_process';
import { promisify } from 'node:util';
import { platform } from 'node:os';
import type { LeanEnvironmentInfo, LeanVersion } from '../types.js';
import {
  LeanNotFoundError,
  LeanVersionError,
  getInstallInstructions,
} from '../errors.js';

const execAsync = promisify(exec);

/**
 * Parse a version string into a LeanVersion object
 */
function parseVersion(versionString: string): LeanVersion {
  const parts = versionString.split('.').map(Number);
  return {
    major: parts[0] || 0,
    minor: parts[1] || 0,
    patch: parts[2] || 0,
    full: versionString,
  };
}

/**
 * Cache for environment detection results
 */
let cachedEnvInfo: LeanEnvironmentInfo | null = null;

/**
 * Detect Lean 4 installation and gather environment information
 * @traceability REQ-LEAN-CORE-001
 */
export async function detectLeanEnvironment(): Promise<LeanEnvironmentInfo> {
  // Return cached result if available
  if (cachedEnvInfo !== null) {
    return cachedEnvInfo;
  }

  const envInfo: LeanEnvironmentInfo = {
    installed: false,
    version: null,
    path: null,
    lakeVersion: null,
    mathlibAvailable: false,
  };

  try {
    // Detect Lean path
    const leanPath = await detectLeanPath();
    if (!leanPath) {
      cachedEnvInfo = envInfo;
      return envInfo;
    }

    // Get Lean version
    const version = await getLeanVersion(leanPath);

    // Get Lake version
    const lakeVersion = await getLakeVersion();

    // Check Mathlib availability
    const mathlibAvailable = await checkMathlibAvailability();

    cachedEnvInfo = {
      installed: true,
      version,
      path: leanPath,
      lakeVersion,
      mathlibAvailable,
    };

    return cachedEnvInfo;
  } catch {
    cachedEnvInfo = envInfo;
    return envInfo;
  }
}

/**
 * Detect the path to the Lean executable
 */
async function detectLeanPath(): Promise<string | null> {
  const os = platform();
  const whichCommand = os === 'win32' ? 'where lean' : 'which lean';

  try {
    const { stdout } = await execAsync(whichCommand, { timeout: 5000 });
    const path = stdout.trim().split('\n')[0];
    return path || null;
  } catch {
    return null;
  }
}

/**
 * Get the Lean version from the executable
 */
async function getLeanVersion(leanPath: string): Promise<LeanVersion | null> {
  try {
    const { stdout } = await execAsync(`"${leanPath}" --version`, {
      timeout: 5000,
    });
    // Parse version from output like "Lean (version 4.3.0, ...)"
    const match = stdout.match(/version\s+(\d+\.\d+\.\d+)/i);
    return match ? parseVersion(match[1]) : null;
  } catch {
    return null;
  }
}

/**
 * Get the Lake version
 */
async function getLakeVersion(): Promise<string | null> {
  try {
    const { stdout } = await execAsync('lake --version', { timeout: 5000 });
    // Parse version from output like "Lake version 4.3.0 ..."
    const match = stdout.match(/version\s+(\d+\.\d+\.\d+)/i);
    return match ? match[1] : null;
  } catch {
    return null;
  }
}

/**
 * Check if Mathlib is available
 */
async function checkMathlibAvailability(): Promise<boolean> {
  try {
    // Check if mathlib is cached in lake
    const { stdout } = await execAsync('lake env printenv LEAN_PATH', {
      timeout: 10000,
    });
    return stdout.includes('mathlib') || stdout.includes('Mathlib');
  } catch {
    return false;
  }
}

/**
 * Validate that Lean version meets minimum requirement
 * @traceability REQ-LEAN-CORE-001
 */
export function validateLeanVersion(
  actual: LeanVersion | null,
  minVersion: string
): boolean {
  if (!actual) {
    return false;
  }

  const actualParts = actual.full.split('.').map(Number);
  const minParts = minVersion.split('.').map(Number);

  for (let i = 0; i < Math.max(actualParts.length, minParts.length); i++) {
    const actualPart = actualParts[i] || 0;
    const minPart = minParts[i] || 0;

    if (actualPart > minPart) {
      return true;
    }
    if (actualPart < minPart) {
      return false;
    }
  }

  return true; // Equal versions
}

/**
 * Ensure Lean is installed and meets version requirements
 * @throws {LeanNotFoundError} If Lean is not installed
 * @throws {LeanVersionError} If Lean version is below minimum
 * @traceability REQ-LEAN-CORE-001, REQ-LEAN-ERR-001
 */
export async function ensureLeanInstalled(
  minVersion: string = '4.0.0'
): Promise<LeanEnvironmentInfo> {
  const envInfo = await detectLeanEnvironment();

  if (!envInfo.installed) {
    throw new LeanNotFoundError(platform());
  }

  if (!validateLeanVersion(envInfo.version, minVersion)) {
    throw new LeanVersionError(minVersion, envInfo.version?.full || 'unknown');
  }

  return envInfo;
}

/**
 * Get installation instructions for the current OS
 * @traceability REQ-LEAN-ERR-001
 */
export function getInstallationInstructions(): string {
  return getInstallInstructions(platform());
}

/**
 * Clear the cached environment information
 * Useful for testing or when Lean installation changes
 */
export function clearEnvironmentCache(): void {
  cachedEnvInfo = null;
}

/**
 * LeanEnvironmentDetector class implementation
 * @traceability REQ-LEAN-CORE-001
 */
export class LeanEnvironmentDetector {
  private cachedInfo: LeanEnvironmentInfo | null = null;

  /**
   * Detect Lean environment
   */
  async detect(): Promise<LeanEnvironmentInfo> {
    if (this.cachedInfo) {
      return this.cachedInfo;
    }
    this.cachedInfo = await detectLeanEnvironment();
    return this.cachedInfo;
  }

  /**
   * Validate version meets minimum requirement
   */
  validateVersion(minVersion: string): boolean {
    if (!this.cachedInfo) {
      return false;
    }
    return validateLeanVersion(this.cachedInfo.version, minVersion);
  }

  /**
   * Get installation instructions for given OS
   */
  getInstallInstructions(os: 'linux' | 'macos' | 'windows'): string {
    return getInstallInstructions(os);
  }

  /**
   * Clear cached information
   */
  clearCache(): void {
    this.cachedInfo = null;
    clearEnvironmentCache();
  }
}
