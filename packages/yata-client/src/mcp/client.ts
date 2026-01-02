/**
 * YATA MCP Client
 * 
 * Client for connecting to YATA MCP server
 * 
 * @packageDocumentation
 * @module mcp/client
 * 
 * @see REQ-INT-102 - MCP Server
 * @see DES-MUSUBIX-001 Section 2.2 - Container Diagram
 */

import { spawn, type ChildProcess } from 'child_process';
import { EventEmitter } from 'events';
import type {
  YataClientConfig,
  ConnectionState,
  ToolCallRequest,
  ToolCallResponse,
} from '../types.js';
import { DEFAULT_YATA_CONFIG } from '../types.js';

/**
 * JSON-RPC request structure
 */
interface JsonRpcRequest {
  jsonrpc: '2.0';
  id: number;
  method: string;
  params?: Record<string, unknown>;
}

/**
 * JSON-RPC response structure
 */
interface JsonRpcResponse {
  jsonrpc: '2.0';
  id: number;
  result?: unknown;
  error?: {
    code: number;
    message: string;
    data?: unknown;
  };
}

/**
 * Pending request tracker
 */
interface PendingRequest {
  resolve: (value: unknown) => void;
  reject: (error: Error) => void;
  timeout: ReturnType<typeof setTimeout>;
}

/**
 * YATA MCP Client Events
 */
export interface YataClientEvents {
  connected: [];
  disconnected: [];
  error: [Error];
  reconnecting: [number];
  message: [JsonRpcResponse];
}

/**
 * YATA MCP Client
 * 
 * Provides connection management and tool invocation for YATA MCP server
 */
export class YataMCPClient extends EventEmitter {
  private config: YataClientConfig;
  private state: ConnectionState = 'disconnected';
  private process: ChildProcess | null = null;
  private requestId = 0;
  private pendingRequests = new Map<number, PendingRequest>();
  private reconnectAttempts = 0;
  private buffer = '';

  constructor(config?: Partial<YataClientConfig>) {
    super();
    this.config = { ...DEFAULT_YATA_CONFIG, ...config };
  }

  /**
   * Get current connection state
   */
  getState(): ConnectionState {
    return this.state;
  }

  /**
   * Check if connected
   */
  isConnected(): boolean {
    return this.state === 'connected';
  }

  /**
   * Connect to YATA MCP server
   */
  async connect(): Promise<void> {
    if (this.state === 'connected') {
      return;
    }

    this.setState('connecting');

    try {
      if (this.config.transport === 'stdio') {
        await this.connectStdio();
      } else {
        await this.connectSSE();
      }

      this.setState('connected');
      this.reconnectAttempts = 0;
      this.emit('connected');
    } catch (error) {
      this.setState('error');
      this.emit('error', error instanceof Error ? error : new Error(String(error)));
      throw error;
    }
  }

  /**
   * Disconnect from server
   */
  async disconnect(): Promise<void> {
    if (this.state === 'disconnected') {
      return;
    }

    // Clear pending requests
    for (const [id, pending] of this.pendingRequests) {
      clearTimeout(pending.timeout);
      pending.reject(new Error('Connection closed'));
      this.pendingRequests.delete(id);
    }

    // Kill process if stdio
    if (this.process) {
      this.process.kill();
      this.process = null;
    }

    this.setState('disconnected');
    this.emit('disconnected');
  }

  /**
   * Call a tool on YATA server
   */
  async callTool<T = unknown>(request: ToolCallRequest): Promise<ToolCallResponse<T>> {
    const startTime = Date.now();

    try {
      const result = await this.sendRequest('tools/call', {
        name: request.name,
        arguments: request.arguments,
      });

      return {
        success: true,
        result: result as T,
        executionTime: Date.now() - startTime,
      };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : String(error),
        executionTime: Date.now() - startTime,
      };
    }
  }

  /**
   * List available tools
   */
  async listTools(): Promise<Array<{ name: string; description: string }>> {
    const result = await this.sendRequest('tools/list', {});
    return result as Array<{ name: string; description: string }>;
  }

  /**
   * Send initialize request
   */
  async initialize(): Promise<void> {
    await this.sendRequest('initialize', {
      protocolVersion: '2024-11-05',
      capabilities: {
        tools: {},
      },
      clientInfo: {
        name: 'musubix-yata-client',
        version: '0.1.0',
      },
    });

    // Send initialized notification
    this.sendNotification('notifications/initialized', {});
  }

  /**
   * Connect via stdio transport
   */
  private async connectStdio(): Promise<void> {
    return new Promise((resolve, reject) => {
      const args = this.config.args ?? [];
      
      this.process = spawn(this.config.server, args, {
        stdio: ['pipe', 'pipe', 'pipe'],
      });

      this.process.on('error', (error) => {
        reject(new Error(`Failed to spawn YATA server: ${error.message}`));
      });

      this.process.on('exit', (_code) => {
        if (this.state === 'connected') {
          this.handleDisconnect();
        }
      });

      this.process.stdout?.on('data', (data: Buffer) => {
        this.handleData(data.toString());
      });

      this.process.stderr?.on('data', (data: Buffer) => {
        console.error(`[YATA stderr] ${data.toString()}`);
      });

      // Give process time to start
      setTimeout(() => {
        if (this.process && !this.process.killed) {
          resolve();
        }
      }, 100);
    });
  }

  /**
   * Connect via SSE transport
   */
  private async connectSSE(): Promise<void> {
    // SSE implementation placeholder
    throw new Error('SSE transport not yet implemented');
  }

  /**
   * Send JSON-RPC request
   */
  private sendRequest(method: string, params: Record<string, unknown>): Promise<unknown> {
    return new Promise((resolve, reject) => {
      if (!this.isConnected() && this.state !== 'connecting') {
        reject(new Error('Not connected to YATA server'));
        return;
      }

      const id = ++this.requestId;
      const request: JsonRpcRequest = {
        jsonrpc: '2.0',
        id,
        method,
        params,
      };

      const timeout = setTimeout(() => {
        this.pendingRequests.delete(id);
        reject(new Error(`Request timeout: ${method}`));
      }, this.config.timeout);

      this.pendingRequests.set(id, { resolve, reject, timeout });

      this.send(JSON.stringify(request));
    });
  }

  /**
   * Send notification (no response expected)
   */
  private sendNotification(method: string, params: Record<string, unknown>): void {
    const notification = {
      jsonrpc: '2.0',
      method,
      params,
    };
    this.send(JSON.stringify(notification));
  }

  /**
   * Send data to server
   */
  private send(data: string): void {
    if (this.config.transport === 'stdio' && this.process?.stdin) {
      this.process.stdin.write(data + '\n');
    }
  }

  /**
   * Handle incoming data
   */
  private handleData(data: string): void {
    this.buffer += data;
    
    // Process complete lines
    const lines = this.buffer.split('\n');
    this.buffer = lines.pop() ?? '';

    for (const line of lines) {
      if (line.trim()) {
        try {
          const response = JSON.parse(line) as JsonRpcResponse;
          this.handleResponse(response);
        } catch {
          // Ignore parse errors
        }
      }
    }
  }

  /**
   * Handle JSON-RPC response
   */
  private handleResponse(response: JsonRpcResponse): void {
    this.emit('message', response);

    const pending = this.pendingRequests.get(response.id);
    if (pending) {
      clearTimeout(pending.timeout);
      this.pendingRequests.delete(response.id);

      if (response.error) {
        pending.reject(new Error(response.error.message));
      } else {
        pending.resolve(response.result);
      }
    }
  }

  /**
   * Handle disconnect
   */
  private handleDisconnect(): void {
    this.setState('disconnected');
    this.emit('disconnected');

    if (this.config.autoReconnect && this.reconnectAttempts < this.config.maxReconnectAttempts) {
      this.attemptReconnect();
    }
  }

  /**
   * Attempt reconnection
   */
  private attemptReconnect(): void {
    this.reconnectAttempts++;
    this.setState('reconnecting');
    this.emit('reconnecting', this.reconnectAttempts);

    setTimeout(() => {
      this.connect().catch(() => {
        if (this.reconnectAttempts < this.config.maxReconnectAttempts) {
          this.attemptReconnect();
        }
      });
    }, this.config.reconnectDelay * this.reconnectAttempts);
  }

  /**
   * Set connection state
   */
  private setState(state: ConnectionState): void {
    this.state = state;
  }
}

/**
 * Create a new YATA client instance
 */
export function createYataClient(config?: Partial<YataClientConfig>): YataMCPClient {
  return new YataMCPClient(config);
}
