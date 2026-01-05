/**
 * Pattern Server
 *
 * @module learning/sharing/pattern-server
 * @description HTTPベースのパターン共有サーバー
 * @requirements REQ-SHARE-001, REQ-SHARE-002
 * @design DES-SHARE-001
 */

import { createServer, IncomingMessage, ServerResponse, Server } from 'http';
import { EventEmitter } from 'events';
import type {
  SharedPattern,
  ServerConfig,
  AuthToken,
} from './types.js';
import { PatternSerializer } from './pattern-serializer.js';
import { PatternDeserializer } from './pattern-deserializer.js';

/**
 * デフォルトのサーバー設定
 */
const DEFAULT_SERVER_CONFIG: ServerConfig = {
  port: 3456,
  host: 'localhost',
  enableAuth: false,
  cors: {
    allowedOrigins: ['*'],
    allowedMethods: ['GET', 'POST', 'PUT', 'DELETE', 'OPTIONS'],
    allowedHeaders: ['Content-Type', 'Authorization'],
  },
  rateLimit: {
    windowMs: 60000, // 1分
    maxRequests: 100, // 100リクエスト/分
  },
};

/**
 * リクエストカウンター（レート制限用）
 */
interface RequestCounter {
  count: number;
  resetAt: number;
}

/**
 * サーバーイベント
 */
export interface ServerEvents {
  start: { port: number; host: string };
  stop: {};
  request: { method: string; path: string; ip: string };
  error: { error: Error; context?: string };
  patternExported: { count: number };
  patternImported: { count: number };
}

/**
 * パターン共有サーバー
 */
export class PatternServer extends EventEmitter {
  private config: ServerConfig;
  private server: Server | null = null;
  private patterns: Map<string, SharedPattern> = new Map();
  private serializer: PatternSerializer;
  private deserializer: PatternDeserializer;
  private requestCounters: Map<string, RequestCounter> = new Map();
  private tokens: Map<string, AuthToken> = new Map();
  private running = false;

  constructor(config: Partial<ServerConfig> = {}) {
    super();
    this.config = { ...DEFAULT_SERVER_CONFIG, ...config };
    this.serializer = new PatternSerializer();
    this.deserializer = new PatternDeserializer();
  }

  /**
   * サーバーを開始
   */
  async start(): Promise<void> {
    if (this.running) {
      throw new Error('Server is already running');
    }

    return new Promise((resolve, reject) => {
      this.server = createServer((req, res) => this.handleRequest(req, res));

      this.server.on('error', (err) => {
        this.emit('error', { error: err, context: 'server' });
        reject(err);
      });

      this.server.listen(this.config.port, this.config.host, () => {
        this.running = true;
        this.emit('start', { port: this.config.port, host: this.config.host });
        resolve();
      });
    });
  }

  /**
   * サーバーを停止
   */
  async stop(): Promise<void> {
    if (!this.running || !this.server) {
      return;
    }

    return new Promise((resolve) => {
      this.server!.close(() => {
        this.running = false;
        this.server = null;
        this.emit('stop', {});
        resolve();
      });
    });
  }

  /**
   * HTTPリクエストを処理
   */
  private async handleRequest(req: IncomingMessage, res: ServerResponse): Promise<void> {
    const ip = req.socket.remoteAddress ?? 'unknown';
    const method = req.method ?? 'GET';
    const url = new URL(req.url ?? '/', `http://${req.headers.host}`);
    const path = url.pathname;

    this.emit('request', { method, path, ip });

    // CORS プリフライト
    if (method === 'OPTIONS') {
      this.sendCorsHeaders(res);
      res.writeHead(204);
      res.end();
      return;
    }

    // CORSヘッダー設定
    this.sendCorsHeaders(res);

    // レート制限チェック
    if (!this.checkRateLimit(ip)) {
      this.sendError(res, 429, 'Too Many Requests');
      return;
    }

    // 認証チェック
    if (this.config.enableAuth) {
      const authorized = this.checkAuth(req);
      if (!authorized) {
        this.sendError(res, 401, 'Unauthorized');
        return;
      }
    }

    try {
      // ルーティング
      if (path === '/api/patterns' && method === 'GET') {
        await this.handleGetPatterns(req, res);
      } else if (path === '/api/patterns' && method === 'POST') {
        await this.handleImportPatterns(req, res);
      } else if (path === '/api/patterns/export' && method === 'GET') {
        await this.handleExportPatterns(req, res);
      } else if (path === '/api/patterns/validate' && method === 'POST') {
        await this.handleValidatePatterns(req, res);
      } else if (path.startsWith('/api/patterns/') && method === 'GET') {
        await this.handleGetPattern(req, res, path);
      } else if (path.startsWith('/api/patterns/') && method === 'DELETE') {
        await this.handleDeletePattern(req, res, path);
      } else if (path === '/api/health' && method === 'GET') {
        this.handleHealth(req, res);
      } else if (path === '/api/stats' && method === 'GET') {
        this.handleStats(req, res);
      } else {
        this.sendError(res, 404, 'Not Found');
      }
    } catch (err) {
      this.emit('error', { error: err as Error, context: 'request' });
      this.sendError(res, 500, 'Internal Server Error');
    }
  }

  /**
   * パターン一覧を取得
   */
  private async handleGetPatterns(_req: IncomingMessage, res: ServerResponse): Promise<void> {
    const patterns = Array.from(this.patterns.values());
    this.sendJson(res, 200, { patterns, count: patterns.length });
  }

  /**
   * パターンをインポート
   */
  private async handleImportPatterns(req: IncomingMessage, res: ServerResponse): Promise<void> {
    const body = await this.readBody(req);
    const result = await this.deserializer.import(body);

    if (result.success) {
      // パターンを保存
      for (const pattern of result.patterns) {
        this.patterns.set(pattern.id, pattern);
      }
      this.emit('patternImported', { count: result.importedCount });
    }

    this.sendJson(res, result.success ? 200 : 400, result);
  }

  /**
   * パターンをエクスポート
   */
  private async handleExportPatterns(req: IncomingMessage, res: ServerResponse): Promise<void> {
    const url = new URL(req.url ?? '/', `http://${req.headers.host}`);
    const format = (url.searchParams.get('format') ?? 'json') as 'json' | 'n3';
    const sanitize = url.searchParams.get('sanitize') !== 'false';

    const patterns = Array.from(this.patterns.values());
    const detectedPatterns = patterns.map((p) => ({
      id: p.id,
      name: p.name,
      confidence: p.confidence,
      usageCount: p.usageCount,
      template: p.template,
      description: p.description,
      context: p.context,
      tags: p.metadata.tags,
      source: p.metadata.source,
      createdAt: p.createdAt,
      updatedAt: p.updatedAt,
      version: p.version,
    }));

    const result = this.serializer.export(detectedPatterns as any, { format, sanitize });
    this.emit('patternExported', { count: result.patternCount });
    this.sendJson(res, 200, result);
  }

  /**
   * パターンを検証
   */
  private async handleValidatePatterns(req: IncomingMessage, res: ServerResponse): Promise<void> {
    const body = await this.readBody(req);
    const result = this.deserializer.validate(body);
    this.sendJson(res, result.valid ? 200 : 400, result);
  }

  /**
   * 単一パターンを取得
   */
  private async handleGetPattern(
    _req: IncomingMessage,
    res: ServerResponse,
    path: string
  ): Promise<void> {
    const id = path.replace('/api/patterns/', '');
    const pattern = this.patterns.get(id);

    if (pattern) {
      this.sendJson(res, 200, pattern);
    } else {
      this.sendError(res, 404, 'Pattern not found');
    }
  }

  /**
   * パターンを削除
   */
  private async handleDeletePattern(
    _req: IncomingMessage,
    res: ServerResponse,
    path: string
  ): Promise<void> {
    const id = path.replace('/api/patterns/', '');

    if (this.patterns.has(id)) {
      this.patterns.delete(id);
      this.sendJson(res, 200, { success: true, id });
    } else {
      this.sendError(res, 404, 'Pattern not found');
    }
  }

  /**
   * ヘルスチェック
   */
  private handleHealth(_req: IncomingMessage, res: ServerResponse): void {
    this.sendJson(res, 200, {
      status: 'healthy',
      uptime: process.uptime(),
      timestamp: new Date().toISOString(),
    });
  }

  /**
   * 統計情報
   */
  private handleStats(_req: IncomingMessage, res: ServerResponse): void {
    this.sendJson(res, 200, {
      patternCount: this.patterns.size,
      memoryUsage: process.memoryUsage(),
      uptime: process.uptime(),
    });
  }

  /**
   * CORSヘッダーを送信
   */
  private sendCorsHeaders(res: ServerResponse): void {
    const cors = this.config.cors!;
    res.setHeader('Access-Control-Allow-Origin', cors.allowedOrigins.join(', '));
    res.setHeader('Access-Control-Allow-Methods', cors.allowedMethods.join(', '));
    res.setHeader('Access-Control-Allow-Headers', cors.allowedHeaders.join(', '));
  }

  /**
   * JSONレスポンスを送信
   */
  private sendJson(res: ServerResponse, status: number, data: unknown): void {
    res.writeHead(status, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify(data));
  }

  /**
   * エラーレスポンスを送信
   */
  private sendError(res: ServerResponse, status: number, message: string): void {
    this.sendJson(res, status, { error: message, status });
  }

  /**
   * リクエストボディを読み取る
   */
  private readBody(req: IncomingMessage): Promise<string> {
    return new Promise((resolve, reject) => {
      const chunks: Buffer[] = [];
      req.on('data', (chunk) => chunks.push(chunk));
      req.on('end', () => resolve(Buffer.concat(chunks).toString('utf8')));
      req.on('error', reject);
    });
  }

  /**
   * レート制限をチェック
   */
  private checkRateLimit(ip: string): boolean {
    const now = Date.now();
    const limit = this.config.rateLimit!;
    let counter = this.requestCounters.get(ip);

    if (!counter || counter.resetAt < now) {
      counter = { count: 0, resetAt: now + limit.windowMs };
      this.requestCounters.set(ip, counter);
    }

    counter.count++;
    return counter.count <= limit.maxRequests;
  }

  /**
   * 認証をチェック
   */
  private checkAuth(req: IncomingMessage): boolean {
    const authHeader = req.headers.authorization;
    if (!authHeader || !authHeader.startsWith('Bearer ')) {
      return false;
    }

    const token = authHeader.substring(7);
    const authToken = this.tokens.get(token);

    if (!authToken) {
      return false;
    }

    // 有効期限チェック
    if (new Date(authToken.expiresAt) < new Date()) {
      this.tokens.delete(token);
      return false;
    }

    return true;
  }

  /**
   * トークンを登録
   */
  registerToken(token: AuthToken): void {
    this.tokens.set(token.token, token);
  }

  /**
   * トークンを無効化
   */
  revokeToken(token: string): void {
    this.tokens.delete(token);
  }

  /**
   * パターンを追加
   */
  addPattern(pattern: SharedPattern): void {
    this.patterns.set(pattern.id, pattern);
  }

  /**
   * パターンを取得
   */
  getPattern(id: string): SharedPattern | undefined {
    return this.patterns.get(id);
  }

  /**
   * 全パターンを取得
   */
  getAllPatterns(): SharedPattern[] {
    return Array.from(this.patterns.values());
  }

  /**
   * パターン数を取得
   */
  getPatternCount(): number {
    return this.patterns.size;
  }

  /**
   * パターンをクリア
   */
  clearPatterns(): void {
    this.patterns.clear();
  }

  /**
   * サーバーが実行中か
   */
  isRunning(): boolean {
    return this.running;
  }

  /**
   * サーバー設定を取得
   */
  getConfig(): ServerConfig {
    return { ...this.config };
  }

  /**
   * サーバーアドレスを取得
   */
  getAddress(): { host: string; port: number } | null {
    if (!this.running) {
      return null;
    }
    return { host: this.config.host, port: this.config.port };
  }
}
