/**
 * Platform Adapter
 * 
 * Adapts MUSUBIX MCP server for different AI coding platforms
 * 
 * @packageDocumentation
 * @module platform
 * 
 * @see REQ-PLAT-101 - Multi-platform Support
 * @see DES-MUSUBIX-001 Section 2.2 - Container Diagram
 */

import type { MCPServerConfig, ServerCapabilities } from '../types.js';

/**
 * Supported AI coding platforms
 */
export type PlatformType =
  | 'claude-code'
  | 'github-copilot'
  | 'cursor'
  | 'gemini-cli'
  | 'codex-cli'
  | 'qwen-code'
  | 'windsurf'
  | 'generic';

/**
 * Platform-specific configuration
 */
export interface PlatformConfig {
  /** Platform identifier */
  platform: PlatformType;
  /** Platform display name */
  displayName: string;
  /** Supported MCP protocol version */
  protocolVersion: string;
  /** Transport preferences */
  preferredTransport: 'stdio' | 'sse';
  /** Platform-specific capabilities */
  capabilities: PlatformCapabilities;
  /** Configuration file location */
  configPath?: string;
  /** Environment variable prefix */
  envPrefix?: string;
}

/**
 * Platform-specific capabilities
 */
export interface PlatformCapabilities {
  /** Supports tools */
  tools: boolean;
  /** Supports prompts */
  prompts: boolean;
  /** Supports resources */
  resources: boolean;
  /** Supports resource templates */
  resourceTemplates: boolean;
  /** Supports sampling */
  sampling: boolean;
  /** Supports roots */
  roots: boolean;
  /** Maximum context size */
  maxContextSize?: number;
  /** Supports images in responses */
  supportsImages: boolean;
  /** Custom features */
  customFeatures?: string[];
}

/**
 * Platform configurations
 */
export const PLATFORM_CONFIGS: Record<PlatformType, PlatformConfig> = {
  'claude-code': {
    platform: 'claude-code',
    displayName: 'Claude Code',
    protocolVersion: '2024-11-05',
    preferredTransport: 'stdio',
    capabilities: {
      tools: true,
      prompts: true,
      resources: true,
      resourceTemplates: true,
      sampling: true,
      roots: true,
      maxContextSize: 200000,
      supportsImages: true,
      customFeatures: ['caching', 'extended-thinking'],
    },
    configPath: '~/.claude/claude_desktop_config.json',
    envPrefix: 'CLAUDE_',
  },

  'github-copilot': {
    platform: 'github-copilot',
    displayName: 'GitHub Copilot',
    protocolVersion: '2024-11-05',
    preferredTransport: 'stdio',
    capabilities: {
      tools: true,
      prompts: true,
      resources: true,
      resourceTemplates: true,
      sampling: false,
      roots: true,
      maxContextSize: 128000,
      supportsImages: true,
    },
    configPath: '~/.vscode/settings.json',
    envPrefix: 'GITHUB_COPILOT_',
  },

  cursor: {
    platform: 'cursor',
    displayName: 'Cursor',
    protocolVersion: '2024-11-05',
    preferredTransport: 'stdio',
    capabilities: {
      tools: true,
      prompts: true,
      resources: true,
      resourceTemplates: true,
      sampling: false,
      roots: true,
      maxContextSize: 128000,
      supportsImages: true,
    },
    configPath: '~/.cursor/mcp.json',
    envPrefix: 'CURSOR_',
  },

  'gemini-cli': {
    platform: 'gemini-cli',
    displayName: 'Gemini CLI',
    protocolVersion: '2024-11-05',
    preferredTransport: 'stdio',
    capabilities: {
      tools: true,
      prompts: true,
      resources: true,
      resourceTemplates: true,
      sampling: false,
      roots: true,
      maxContextSize: 1000000,
      supportsImages: true,
    },
    envPrefix: 'GEMINI_',
  },

  'codex-cli': {
    platform: 'codex-cli',
    displayName: 'Codex CLI',
    protocolVersion: '2024-11-05',
    preferredTransport: 'stdio',
    capabilities: {
      tools: true,
      prompts: true,
      resources: true,
      resourceTemplates: true,
      sampling: false,
      roots: true,
      maxContextSize: 128000,
      supportsImages: false,
    },
    envPrefix: 'CODEX_',
  },

  'qwen-code': {
    platform: 'qwen-code',
    displayName: 'Qwen Code',
    protocolVersion: '2024-11-05',
    preferredTransport: 'stdio',
    capabilities: {
      tools: true,
      prompts: true,
      resources: true,
      resourceTemplates: true,
      sampling: false,
      roots: true,
      maxContextSize: 128000,
      supportsImages: true,
    },
    envPrefix: 'QWEN_',
  },

  windsurf: {
    platform: 'windsurf',
    displayName: 'Windsurf',
    protocolVersion: '2024-11-05',
    preferredTransport: 'stdio',
    capabilities: {
      tools: true,
      prompts: true,
      resources: true,
      resourceTemplates: true,
      sampling: false,
      roots: true,
      maxContextSize: 128000,
      supportsImages: true,
    },
    configPath: '~/.windsurf/mcp.json',
    envPrefix: 'WINDSURF_',
  },

  generic: {
    platform: 'generic',
    displayName: 'Generic MCP Client',
    protocolVersion: '2024-11-05',
    preferredTransport: 'stdio',
    capabilities: {
      tools: true,
      prompts: true,
      resources: true,
      resourceTemplates: true,
      sampling: false,
      roots: false,
      supportsImages: false,
    },
  },
};

/**
 * Platform detection result
 */
export interface PlatformDetectionResult {
  platform: PlatformType;
  confidence: number;
  source: 'environment' | 'client-info' | 'default';
}

/**
 * Platform Adapter
 * 
 * Detects and adapts to different AI coding platforms
 */
export class PlatformAdapter {
  private currentPlatform: PlatformType = 'generic';
  private platformConfig: PlatformConfig;

  constructor(platform?: PlatformType) {
    if (platform) {
      this.currentPlatform = platform;
    } else {
      this.detectPlatform();
    }
    this.platformConfig = PLATFORM_CONFIGS[this.currentPlatform];
  }

  /**
   * Get current platform
   */
  getPlatform(): PlatformType {
    return this.currentPlatform;
  }

  /**
   * Get platform configuration
   */
  getConfig(): PlatformConfig {
    return this.platformConfig;
  }

  /**
   * Get platform display name
   */
  getDisplayName(): string {
    return this.platformConfig.displayName;
  }

  /**
   * Detect platform from environment
   */
  detectPlatform(): PlatformDetectionResult {
    // Check environment variables
    const env = process.env;

    // Claude Code detection
    if (env.CLAUDE_CODE || env.MCP_CLIENT_NAME?.includes('claude')) {
      this.currentPlatform = 'claude-code';
      return { platform: 'claude-code', confidence: 0.9, source: 'environment' };
    }

    // GitHub Copilot detection
    if (env.GITHUB_COPILOT || env.VSCODE_PID) {
      this.currentPlatform = 'github-copilot';
      return { platform: 'github-copilot', confidence: 0.8, source: 'environment' };
    }

    // Cursor detection
    if (env.CURSOR_SESSION || env.MCP_CLIENT_NAME?.includes('cursor')) {
      this.currentPlatform = 'cursor';
      return { platform: 'cursor', confidence: 0.9, source: 'environment' };
    }

    // Gemini CLI detection
    if (env.GEMINI_API_KEY || env.MCP_CLIENT_NAME?.includes('gemini')) {
      this.currentPlatform = 'gemini-cli';
      return { platform: 'gemini-cli', confidence: 0.8, source: 'environment' };
    }

    // Codex CLI detection
    if (env.OPENAI_API_KEY && env.CODEX_CLI) {
      this.currentPlatform = 'codex-cli';
      return { platform: 'codex-cli', confidence: 0.8, source: 'environment' };
    }

    // Qwen Code detection
    if (env.QWEN_API_KEY || env.MCP_CLIENT_NAME?.includes('qwen')) {
      this.currentPlatform = 'qwen-code';
      return { platform: 'qwen-code', confidence: 0.8, source: 'environment' };
    }

    // Windsurf detection
    if (env.WINDSURF_SESSION || env.MCP_CLIENT_NAME?.includes('windsurf')) {
      this.currentPlatform = 'windsurf';
      return { platform: 'windsurf', confidence: 0.9, source: 'environment' };
    }

    // Default to generic
    return { platform: 'generic', confidence: 0.5, source: 'default' };
  }

  /**
   * Update platform from client info
   */
  updateFromClientInfo(clientInfo: { name: string; version: string }): void {
    const name = clientInfo.name.toLowerCase();

    if (name.includes('claude')) {
      this.currentPlatform = 'claude-code';
    } else if (name.includes('copilot') || name.includes('vscode')) {
      this.currentPlatform = 'github-copilot';
    } else if (name.includes('cursor')) {
      this.currentPlatform = 'cursor';
    } else if (name.includes('gemini')) {
      this.currentPlatform = 'gemini-cli';
    } else if (name.includes('codex')) {
      this.currentPlatform = 'codex-cli';
    } else if (name.includes('qwen')) {
      this.currentPlatform = 'qwen-code';
    } else if (name.includes('windsurf')) {
      this.currentPlatform = 'windsurf';
    }

    this.platformConfig = PLATFORM_CONFIGS[this.currentPlatform];
  }

  /**
   * Get server capabilities adapted for platform
   */
  getAdaptedCapabilities(baseCapabilities: ServerCapabilities): ServerCapabilities {
    const platformCaps = this.platformConfig.capabilities;
    const adapted: ServerCapabilities = {};

    if (platformCaps.tools && baseCapabilities.tools) {
      adapted.tools = baseCapabilities.tools;
    }

    if (platformCaps.prompts && baseCapabilities.prompts) {
      adapted.prompts = baseCapabilities.prompts;
    }

    if (platformCaps.resources && baseCapabilities.resources) {
      adapted.resources = {
        ...baseCapabilities.resources,
        subscribe: platformCaps.resources && baseCapabilities.resources?.subscribe,
      };
    }

    if (baseCapabilities.logging) {
      adapted.logging = baseCapabilities.logging;
    }

    return adapted;
  }

  /**
   * Get server config adapted for platform
   */
  getAdaptedServerConfig(baseConfig: Partial<MCPServerConfig>): MCPServerConfig {
    return {
      name: baseConfig.name ?? 'musubix-mcp-server',
      version: baseConfig.version ?? '0.1.0',
      transport: baseConfig.transport ?? this.platformConfig.preferredTransport,
      debug: baseConfig.debug ?? false,
      port: baseConfig.port,
    };
  }

  /**
   * Check if feature is supported
   */
  supportsFeature(feature: keyof PlatformCapabilities): boolean {
    return !!this.platformConfig.capabilities[feature];
  }

  /**
   * Get max context size
   */
  getMaxContextSize(): number {
    return this.platformConfig.capabilities.maxContextSize ?? 128000;
  }

  /**
   * Generate configuration snippet for platform
   */
  generateConfigSnippet(serverPath: string): string {
    const platform = this.currentPlatform;
    const config = this.platformConfig;

    switch (platform) {
      case 'claude-code':
        return JSON.stringify(
          {
            mcpServers: {
              musubix: {
                command: 'node',
                args: [serverPath],
              },
            },
          },
          null,
          2
        );

      case 'cursor':
      case 'windsurf':
        return JSON.stringify(
          {
            mcpServers: {
              musubix: {
                command: 'node',
                args: [serverPath],
              },
            },
          },
          null,
          2
        );

      case 'github-copilot':
        return JSON.stringify(
          {
            'github.copilot.chat.codeGeneration.instructions': [
              {
                file: 'mcp.json',
              },
            ],
          },
          null,
          2
        );

      default:
        return `# Add to your MCP client configuration:
command: node
args: ["${serverPath}"]
transport: ${config.preferredTransport}`;
    }
  }
}

/**
 * Create platform adapter instance
 */
export function createPlatformAdapter(platform?: PlatformType): PlatformAdapter {
  return new PlatformAdapter(platform);
}

/**
 * Get all supported platforms
 */
export function getSupportedPlatforms(): PlatformType[] {
  return Object.keys(PLATFORM_CONFIGS) as PlatformType[];
}

/**
 * Get platform config by type
 */
export function getPlatformConfig(platform: PlatformType): PlatformConfig {
  return PLATFORM_CONFIGS[platform];
}
