/**
 * YATA Global HTTP Server
 *
 * REST API server for YATA Global knowledge graph
 *
 * @packageDocumentation
 * @module @nahisaho/yata-global/server
 */

import { createServer, IncomingMessage, ServerResponse } from 'http';
import { URL } from 'url';
import type {
  FrameworkKnowledge,
  PatternCategory,
} from './types.js';
import type {
  KGPR,
  KGPRStatus,
  KGPRDiff,
  KGPRComment,
} from './kgpr/types.js';
import { MergeEngine } from './kgpr/merge-engine.js';

/**
 * Server configuration
 */
export interface ServerConfig {
  port: number;
  host: string;
  enableCors: boolean;
}

const DEFAULT_CONFIG: ServerConfig = {
  port: 3000,
  host: '0.0.0.0',
  enableCors: true,
};

/**
 * Simplified user for server
 */
interface ServerUser {
  id: string;
  username: string;
  email: string;
}

/**
 * Simplified KGPR for server storage
 */
interface ServerKGPR {
  id: string;
  title: string;
  description: string;
  status: KGPRStatus;
  author: { id: string; name: string };
  sourceNamespace: string;
  diff: KGPRDiff;
  reviews: Array<{
    id: string;
    userId: string;
    userName: string;
    decision: 'approve' | 'changes_requested' | 'commented';
    comment?: string;
    createdAt: Date;
  }>;
  comments: KGPRComment[];
  labels: string[];
  createdAt: Date;
  updatedAt: Date;
  mergedAt?: Date;
}

/**
 * Simplified pattern for server
 */
interface ServerPattern {
  id: string;
  name: string;
  category: PatternCategory;
  description: string;
  template: string;
  example?: string;
  metrics: { usageCount: number; successRate: number };
  contributor: { id: string; name: string };
  votes: number;
  createdAt: Date;
  updatedAt: Date;
}

/**
 * In-memory storage for demo/testing
 */
interface Storage {
  users: Map<string, ServerUser>;
  kgprs: Map<string, ServerKGPR>;
  patterns: Map<string, ServerPattern>;
  frameworks: Map<string, FrameworkKnowledge>;
  tokens: Map<string, { userId: string; expiresAt: Date }>;
}

/**
 * Create in-memory storage
 */
function createStorage(): Storage {
  return {
    users: new Map([
      ['user-1', { id: 'user-1', username: 'demo', email: 'demo@example.com' }],
    ]),
    kgprs: new Map(),
    patterns: new Map(),
    frameworks: new Map(),
    tokens: new Map(),
  };
}

/**
 * Parse JSON body
 */
async function parseBody(req: IncomingMessage): Promise<unknown> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (chunk) => chunks.push(chunk));
    req.on('end', () => {
      const body = Buffer.concat(chunks).toString();
      if (!body) {
        resolve({});
        return;
      }
      try {
        resolve(JSON.parse(body));
      } catch {
        reject(new Error('Invalid JSON'));
      }
    });
    req.on('error', reject);
  });
}

/**
 * Send JSON response
 */
function sendJson(res: ServerResponse, status: number, data: unknown): void {
  res.writeHead(status, { 'Content-Type': 'application/json' });
  res.end(JSON.stringify(data));
}

/**
 * Send error response
 */
function sendError(res: ServerResponse, status: number, message: string): void {
  sendJson(res, status, { success: false, error: message });
}

/**
 * Create empty diff
 */
function createEmptyDiff(): KGPRDiff {
  return {
    entities: { added: [], updated: [], deleted: [] },
    relationships: { added: [], updated: [], deleted: [] },
    stats: {
      entitiesAdded: 0,
      entitiesUpdated: 0,
      entitiesDeleted: 0,
      relationshipsAdded: 0,
      relationshipsUpdated: 0,
      relationshipsDeleted: 0,
      totalChanges: 0,
    },
  };
}

/**
 * YATA Global HTTP Server
 */
export class YataGlobalServer {
  private config: ServerConfig;
  private storage: Storage;
  private mergeEngine: MergeEngine;
  private server: ReturnType<typeof createServer> | null = null;

  constructor(config: Partial<ServerConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
    this.storage = createStorage();
    this.mergeEngine = new MergeEngine();
  }

  /**
   * Start the server
   */
  start(): Promise<void> {
    return new Promise((resolve) => {
      this.server = createServer((req, res) => this.handleRequest(req, res));
      this.server.listen(this.config.port, this.config.host, () => {
        console.log(`🌐 YATA Global Server running at http://${this.config.host}:${this.config.port}`);
        resolve();
      });
    });
  }

  /**
   * Stop the server
   */
  stop(): Promise<void> {
    return new Promise((resolve) => {
      if (this.server) {
        this.server.close(() => {
          console.log('🛑 YATA Global Server stopped');
          resolve();
        });
      } else {
        resolve();
      }
    });
  }

  /**
   * Main request handler
   */
  private async handleRequest(req: IncomingMessage, res: ServerResponse): Promise<void> {
    // CORS headers
    if (this.config.enableCors) {
      res.setHeader('Access-Control-Allow-Origin', '*');
      res.setHeader('Access-Control-Allow-Methods', 'GET, POST, PUT, DELETE, OPTIONS');
      res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Authorization');
    }

    // Handle preflight
    if (req.method === 'OPTIONS') {
      res.writeHead(204);
      res.end();
      return;
    }

    const url = new URL(req.url || '/', `http://${req.headers.host}`);
    const path = url.pathname;
    const method = req.method || 'GET';

    console.log(`[${new Date().toISOString()}] ${method} ${path}`);

    try {
      // Route handling
      if (path === '/health' && method === 'GET') {
        return this.handleHealth(res);
      }

      if (path === '/auth/login' && method === 'POST') {
        return await this.handleLogin(req, res);
      }

      if (path === '/api/v1/kgprs' && method === 'GET') {
        return this.handleListKGPRs(req, res);
      }

      if (path === '/api/v1/kgprs' && method === 'POST') {
        return await this.handleSubmitKGPR(req, res);
      }

      if (path.startsWith('/api/v1/kgprs/') && method === 'GET') {
        const id = path.split('/')[4];
        return this.handleGetKGPR(id, res);
      }

      if (path.match(/^\/api\/v1\/kgprs\/[^/]+\/review$/) && method === 'POST') {
        const id = path.split('/')[4];
        return await this.handleReviewKGPR(req, id, res);
      }

      if (path.match(/^\/api\/v1\/kgprs\/[^/]+\/merge$/) && method === 'POST') {
        const id = path.split('/')[4];
        return await this.handleMergeKGPR(id, res);
      }

      if (path === '/api/v1/patterns' && method === 'GET') {
        return this.handleListPatterns(res);
      }

      if (path === '/api/v1/patterns' && method === 'POST') {
        return await this.handleCreatePattern(req, res);
      }

      if (path === '/api/v1/frameworks' && method === 'GET') {
        return this.handleListFrameworks(res);
      }

      // 404
      sendError(res, 404, 'Not found');
    } catch (error) {
      console.error('Request error:', error);
      sendError(res, 500, error instanceof Error ? error.message : 'Internal server error');
    }
  }

  /**
   * Health check
   */
  private handleHealth(res: ServerResponse): void {
    sendJson(res, 200, {
      success: true,
      data: {
        status: 'healthy',
        version: '2.4.1',
        timestamp: new Date().toISOString(),
        stats: {
          kgprs: this.storage.kgprs.size,
          patterns: this.storage.patterns.size,
          frameworks: this.storage.frameworks.size,
        },
      },
    });
  }

  /**
   * Login (demo implementation)
   */
  private async handleLogin(req: IncomingMessage, res: ServerResponse): Promise<void> {
    const body = await parseBody(req) as { username?: string; password?: string };

    if (!body.username || !body.password) {
      sendError(res, 400, 'Username and password required');
      return;
    }

    // Demo auth - accept any password for 'demo' user
    if (body.username === 'demo') {
      const token = `token-${Date.now()}-${Math.random().toString(36).substring(2)}`;
      this.storage.tokens.set(token, {
        userId: 'user-1',
        expiresAt: new Date(Date.now() + 24 * 60 * 60 * 1000), // 24h
      });

      sendJson(res, 200, {
        success: true,
        data: {
          accessToken: token,
          tokenType: 'Bearer',
          expiresIn: 86400,
          user: this.storage.users.get('user-1'),
        },
      });
    } else {
      sendError(res, 401, 'Invalid credentials');
    }
  }

  /**
   * List KGPRs
   */
  private handleListKGPRs(req: IncomingMessage, res: ServerResponse): void {
    const url = new URL(req.url || '/', `http://${req.headers.host}`);
    const status = url.searchParams.get('status') as KGPRStatus | null;

    let kgprs = Array.from(this.storage.kgprs.values());

    if (status) {
      kgprs = kgprs.filter((k) => k.status === status);
    }

    sendJson(res, 200, {
      success: true,
      data: {
        items: kgprs,
        total: kgprs.length,
        limit: 100,
        offset: 0,
      },
    });
  }

  /**
   * Get single KGPR
   */
  private handleGetKGPR(id: string, res: ServerResponse): void {
    const kgpr = this.storage.kgprs.get(id);

    if (!kgpr) {
      sendError(res, 404, `KGPR not found: ${id}`);
      return;
    }

    sendJson(res, 200, { success: true, data: kgpr });
  }

  /**
   * Submit KGPR
   */
  private async handleSubmitKGPR(req: IncomingMessage, res: ServerResponse): Promise<void> {
    const body = await parseBody(req) as Partial<ServerKGPR>;

    if (!body.title) {
      sendError(res, 400, 'Title is required');
      return;
    }

    const id = `KGPR-${Date.now().toString(36)}-${Math.random().toString(36).substring(2, 8)}`;
    const now = new Date();

    const kgpr: ServerKGPR = {
      id,
      title: body.title,
      description: body.description || '',
      status: 'open',
      author: {
        id: 'user-1',
        name: 'demo',
      },
      sourceNamespace: body.sourceNamespace || '*',
      diff: body.diff || createEmptyDiff(),
      reviews: [],
      comments: [],
      labels: body.labels || [],
      createdAt: now,
      updatedAt: now,
    };

    this.storage.kgprs.set(id, kgpr);

    console.log(`📝 KGPR created: ${id} - ${kgpr.title}`);

    sendJson(res, 201, { success: true, data: kgpr });
  }

  /**
   * Review KGPR
   */
  private async handleReviewKGPR(req: IncomingMessage, id: string, res: ServerResponse): Promise<void> {
    const kgpr = this.storage.kgprs.get(id);

    if (!kgpr) {
      sendError(res, 404, `KGPR not found: ${id}`);
      return;
    }

    const body = await parseBody(req) as { decision: string; comment?: string };

    if (!body.decision || !['approve', 'changes_requested', 'commented'].includes(body.decision)) {
      sendError(res, 400, 'Valid decision required (approve, changes_requested, commented)');
      return;
    }

    const review = {
      id: `review-${Date.now()}`,
      userId: 'user-1',
      userName: 'demo',
      decision: body.decision as 'approve' | 'changes_requested' | 'commented',
      comment: body.comment,
      createdAt: new Date(),
    };

    kgpr.reviews.push(review);
    kgpr.updatedAt = new Date();

    if (body.decision === 'approve') {
      kgpr.status = 'approved';
    } else if (body.decision === 'changes_requested') {
      kgpr.status = 'changes_requested';
    }

    console.log(`✅ KGPR reviewed: ${id} - ${body.decision}`);

    sendJson(res, 200, { success: true, data: kgpr });
  }

  /**
   * Merge KGPR
   */
  private async handleMergeKGPR(id: string, res: ServerResponse): Promise<void> {
    const kgpr = this.storage.kgprs.get(id);

    if (!kgpr) {
      sendError(res, 404, `KGPR not found: ${id}`);
      return;
    }

    if (kgpr.status !== 'approved') {
      sendError(res, 400, 'KGPR must be approved before merge');
      return;
    }

    // Convert to KGPR format for merge engine
    const kgprForMerge: KGPR = {
      id: kgpr.id,
      title: kgpr.title,
      description: kgpr.description,
      authorId: kgpr.author.id,
      authorName: kgpr.author.name,
      status: kgpr.status,
      sourceNamespace: kgpr.sourceNamespace,
      diff: kgpr.diff,
      reviews: kgpr.reviews.map((r) => ({
        id: r.id,
        reviewerId: r.userId,
        reviewerName: r.userName,
        status: r.decision === 'approve' ? 'approved' as const : r.decision,
        body: r.comment,
        comments: [],
        createdAt: r.createdAt,
      })),
      comments: kgpr.comments,
      labels: kgpr.labels,
      createdAt: kgpr.createdAt,
      updatedAt: kgpr.updatedAt,
    };

    // Perform merge (dry run since we don't have global KG connected)
    const mergeResult = await this.mergeEngine.merge(kgprForMerge, { dryRun: true });

    kgpr.status = 'merged';
    kgpr.mergedAt = new Date();
    kgpr.updatedAt = new Date();

    console.log(`🔀 KGPR merged: ${id}`);

    // Save merged patterns
    for (const entity of kgpr.diff.entities.added) {
      if (entity.entityType === 'pattern') {
        const pattern: ServerPattern = {
          id: entity.localId || `pattern-${Date.now()}`,
          name: entity.name,
          category: 'design-pattern',
          description: '',
          template: '',
          example: undefined,
          metrics: { usageCount: 0, successRate: 0 },
          contributor: kgpr.author,
          votes: 0,
          createdAt: new Date(),
          updatedAt: new Date(),
        };
        this.storage.patterns.set(pattern.id, pattern);
      }
    }

    sendJson(res, 200, {
      success: true,
      data: {
        kgpr,
        mergeResult: {
          entitiesMerged: mergeResult.applied.entitiesAdded + mergeResult.applied.entitiesUpdated,
          relationshipsMerged: mergeResult.applied.relationshipsAdded + mergeResult.applied.relationshipsUpdated,
          conflicts: mergeResult.conflicts,
        },
      },
    });
  }

  /**
   * List patterns
   */
  private handleListPatterns(res: ServerResponse): void {
    sendJson(res, 200, {
      success: true,
      data: {
        items: Array.from(this.storage.patterns.values()),
        total: this.storage.patterns.size,
      },
    });
  }

  /**
   * Create pattern
   */
  private async handleCreatePattern(req: IncomingMessage, res: ServerResponse): Promise<void> {
    const body = await parseBody(req) as Partial<ServerPattern>;

    if (!body.name) {
      sendError(res, 400, 'Pattern name is required');
      return;
    }

    const pattern: ServerPattern = {
      id: `pattern-${Date.now()}`,
      name: body.name,
      category: body.category || 'design-pattern',
      description: body.description || '',
      template: body.template || '',
      example: body.example,
      metrics: { usageCount: 0, successRate: 0 },
      contributor: { id: 'user-1', name: 'demo' },
      votes: 0,
      createdAt: new Date(),
      updatedAt: new Date(),
    };

    this.storage.patterns.set(pattern.id, pattern);

    sendJson(res, 201, { success: true, data: pattern });
  }

  /**
   * List frameworks
   */
  private handleListFrameworks(res: ServerResponse): void {
    sendJson(res, 200, {
      success: true,
      data: {
        items: Array.from(this.storage.frameworks.values()),
        total: this.storage.frameworks.size,
      },
    });
  }
}

/**
 * Create and start server (CLI entry point)
 */
export async function startServer(config?: Partial<ServerConfig>): Promise<YataGlobalServer> {
  const server = new YataGlobalServer(config);
  await server.start();
  return server;
}
