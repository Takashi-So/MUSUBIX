/**
 * ConfigLoader Infrastructure
 *
 * Loads and manages Assistant Axis configuration
 *
 * @see REQ-AA-INT-001 - Configuration management
 */

import type { IConfigLoader } from '../application/interfaces.js';
import type { AssistantAxisConfig } from '../config/types.js';
import { DEFAULT_CONFIG, mergeConfig } from '../config/defaults.js';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';

/**
 * Configuration file name
 */
const CONFIG_FILE_NAME = 'assistant-axis.config.json';

/**
 * ConfigLoader state
 */
interface ConfigLoaderState {
  config: AssistantAxisConfig;
  loaded: boolean;
  configPath?: string;
}

/**
 * Create ConfigLoader service
 *
 * @returns IConfigLoader implementation
 */
export function createConfigLoader(): IConfigLoader {
  const state: ConfigLoaderState = {
    config: DEFAULT_CONFIG,
    loaded: false,
  };

  return {
    async load(configPath?: string): Promise<void> {
      const searchPaths = configPath
        ? [configPath]
        : [
            path.join(process.cwd(), CONFIG_FILE_NAME),
            path.join(process.cwd(), '.config', CONFIG_FILE_NAME),
            path.join(process.cwd(), 'config', CONFIG_FILE_NAME),
          ];

      for (const searchPath of searchPaths) {
        try {
          const content = await fs.readFile(searchPath, 'utf-8');
          const userConfig = JSON.parse(content) as Partial<AssistantAxisConfig>;
          state.config = mergeConfig(userConfig);
          state.configPath = searchPath;
          state.loaded = true;
          return;
        } catch {
          // Continue to next path
        }
      }

      // No config file found, use defaults
      state.config = DEFAULT_CONFIG;
      state.loaded = true;
    },

    get<T>(key: string): T | undefined {
      const keys = key.split('.');
      let value: unknown = state.config;

      for (const k of keys) {
        if (value === null || value === undefined) {
          return undefined;
        }
        value = (value as Record<string, unknown>)[k];
      }

      return value as T | undefined;
    },

    isLoaded(): boolean {
      return state.loaded;
    },
  };
}

/**
 * Get full configuration
 */
export function getConfig(loader: IConfigLoader): AssistantAxisConfig {
  return {
    driftThresholds: {
      low: loader.get('driftThresholds.low') ?? DEFAULT_CONFIG.driftThresholds.low,
      medium: loader.get('driftThresholds.medium') ?? DEFAULT_CONFIG.driftThresholds.medium,
      high: loader.get('driftThresholds.high') ?? DEFAULT_CONFIG.driftThresholds.high,
    },
    refreshInterval: loader.get('refreshInterval') ?? DEFAULT_CONFIG.refreshInterval,
    maxInterventions: loader.get('maxInterventions') ?? DEFAULT_CONFIG.maxInterventions,
    monitoringFrequency: {
      safeDomain: loader.get('monitoringFrequency.safeDomain') ?? DEFAULT_CONFIG.monitoringFrequency.safeDomain,
      riskyDomain: loader.get('monitoringFrequency.riskyDomain') ?? DEFAULT_CONFIG.monitoringFrequency.riskyDomain,
    },
    phaseMonitoring: {
      requirements: loader.get('phaseMonitoring.requirements') ?? DEFAULT_CONFIG.phaseMonitoring.requirements,
      design: loader.get('phaseMonitoring.design') ?? DEFAULT_CONFIG.phaseMonitoring.design,
      tasks: loader.get('phaseMonitoring.tasks') ?? DEFAULT_CONFIG.phaseMonitoring.tasks,
      implementation: loader.get('phaseMonitoring.implementation') ?? DEFAULT_CONFIG.phaseMonitoring.implementation,
      done: loader.get('phaseMonitoring.done') ?? DEFAULT_CONFIG.phaseMonitoring.done,
    },
    prompts: {
      identityReinforcement: loader.get('prompts.identityReinforcement') ?? DEFAULT_CONFIG.prompts.identityReinforcement,
      recovery: loader.get('prompts.recovery') ?? DEFAULT_CONFIG.prompts.recovery,
    },
    logging: {
      enabled: loader.get('logging.enabled') ?? DEFAULT_CONFIG.logging.enabled,
      level: loader.get('logging.level') ?? DEFAULT_CONFIG.logging.level,
      anonymize: loader.get('logging.anonymize') ?? DEFAULT_CONFIG.logging.anonymize,
    },
    metrics: {
      enabled: loader.get('metrics.enabled') ?? DEFAULT_CONFIG.metrics.enabled,
      endpoint: loader.get('metrics.endpoint') ?? DEFAULT_CONFIG.metrics.endpoint,
    },
  };
}

/**
 * Save configuration to file
 */
export async function saveConfig(
  config: AssistantAxisConfig,
  configPath?: string
): Promise<void> {
  const targetPath = configPath ?? path.join(process.cwd(), CONFIG_FILE_NAME);
  const content = JSON.stringify(config, null, 2);
  await fs.writeFile(targetPath, content, 'utf-8');
}
