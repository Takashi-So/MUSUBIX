/**
 * YATA UI Server
 *
 * Web-based visualization and management interface for YATA knowledge graphs.
 *
 * @packageDocumentation
 * @module @nahisaho/yata-ui
 *
 * @see REQ-YI-WEB-001 - Web-based Visualization
 * @see REQ-YI-WEB-002 - Interactive Graph Editing
 * @see REQ-YI-WEB-003 - Real-time Updates
 * @see DES-YATA-IMPROVEMENTS-001 - Design Document
 */

import express, { Express, Request, Response, Router } from 'express';
import * as http from 'http';

// ============================================================
// Types
// ============================================================

/**
 * UI Server configuration
 * @see REQ-YI-WEB-001
 */
export interface UIServerConfig {
  /** Server port */
  port: number;
  /** Host to bind to */
  host?: string;
  /** Enable CORS */
  cors?: boolean;
  /** Static files directory */
  staticDir?: string;
  /** API base path */
  apiBasePath?: string;
  /** Enable real-time updates via SSE */
  enableRealtime?: boolean;
}

/**
 * Graph data for visualization
 */
export interface GraphData {
  /** Nodes (entities) */
  nodes: GraphNode[];
  /** Edges (relationships) */
  edges: GraphEdge[];
  /** Graph metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Graph node
 */
export interface GraphNode {
  /** Node ID */
  id: string;
  /** Node label */
  label: string;
  /** Node type */
  type: string;
  /** Namespace */
  namespace?: string;
  /** Position (optional) */
  position?: { x: number; y: number };
  /** Custom data */
  data?: Record<string, unknown>;
}

/**
 * Graph edge
 */
export interface GraphEdge {
  /** Edge ID */
  id: string;
  /** Source node ID */
  source: string;
  /** Target node ID */
  target: string;
  /** Relationship type */
  type: string;
  /** Edge label */
  label?: string;
  /** Edge weight */
  weight?: number;
  /** Custom data */
  data?: Record<string, unknown>;
}

/**
 * API response
 */
export interface ApiResponse<T> {
  /** Success status */
  success: boolean;
  /** Response data */
  data?: T;
  /** Error message */
  error?: string;
  /** Timestamp */
  timestamp: string;
}

/**
 * SSE client
 */
interface SSEClient {
  id: string;
  response: Response;
  namespace?: string;
}

/**
 * Default configuration
 */
export const DEFAULT_UI_CONFIG: Partial<UIServerConfig> = {
  port: 3000,
  host: 'localhost',
  cors: true,
  apiBasePath: '/api',
  enableRealtime: true,
};

// ============================================================
// YataUIServer Class
// ============================================================

/**
 * YATA Knowledge Graph Web UI Server
 *
 * Provides web-based visualization and management for YATA knowledge graphs.
 *
 * @example
 * ```typescript
 * const server = new YataUIServer({
 *   port: 3000,
 *   enableRealtime: true,
 * });
 *
 * // Set data provider
 * server.setDataProvider(async () => {
 *   return {
 *     nodes: [{ id: '1', label: 'Node 1', type: 'entity' }],
 *     edges: [],
 *   };
 * });
 *
 * await server.start();
 * console.log('UI available at http://localhost:3000');
 * ```
 *
 * @see REQ-YI-WEB-001
 * @see REQ-YI-WEB-002
 * @see REQ-YI-WEB-003
 */
export class YataUIServer {
  private app: Express;
  private server: http.Server | null = null;
  private config: UIServerConfig;
  private sseClients: Map<string, SSEClient> = new Map();
  private dataProvider: (() => Promise<GraphData>) | null = null;

  constructor(config: Partial<UIServerConfig> = {}) {
    this.config = { ...DEFAULT_UI_CONFIG, ...config } as UIServerConfig;
    this.app = express();
    this.setupMiddleware();
    this.setupRoutes();
  }

  // ============================================================
  // Public API
  // ============================================================

  /**
   * Set data provider function
   * @param provider - Function that returns graph data
   */
  setDataProvider(provider: () => Promise<GraphData>): void {
    this.dataProvider = provider;
  }

  /**
   * Start the server
   * @see REQ-YI-WEB-001
   */
  async start(): Promise<void> {
    return new Promise((resolve, reject) => {
      try {
        const host = this.config.host ?? '0.0.0.0';
        this.server = this.app.listen(this.config.port, host, () => {
          resolve();
        });
      } catch (error) {
        reject(error);
      }
    });
  }

  /**
   * Stop the server
   */
  async stop(): Promise<void> {
    // Close all SSE connections
    for (const client of this.sseClients.values()) {
      client.response.end();
    }
    this.sseClients.clear();

    return new Promise((resolve, reject) => {
      if (!this.server) {
        resolve();
        return;
      }

      this.server.close((err) => {
        if (err) {
          reject(err);
        } else {
          this.server = null;
          resolve();
        }
      });
    });
  }

  /**
   * Get server URL
   */
  getUrl(): string {
    return `http://${this.config.host}:${this.config.port}`;
  }

  /**
   * Check if server is running
   */
  isRunning(): boolean {
    return this.server !== null;
  }

  /**
   * Broadcast update to all SSE clients
   * @see REQ-YI-WEB-003
   */
  broadcastUpdate(event: string, data: unknown): void {
    const message = `event: ${event}\ndata: ${JSON.stringify(data)}\n\n`;
    
    for (const client of this.sseClients.values()) {
      client.response.write(message);
    }
  }

  /**
   * Get Express app instance for testing
   */
  getApp(): Express {
    return this.app;
  }

  // ============================================================
  // Internal: Middleware
  // ============================================================

  private setupMiddleware(): void {
    // JSON body parser
    this.app.use(express.json());

    // CORS
    if (this.config.cors) {
      this.app.use((_req, res, next) => {
        res.header('Access-Control-Allow-Origin', '*');
        res.header('Access-Control-Allow-Methods', 'GET, POST, PUT, DELETE, OPTIONS');
        res.header('Access-Control-Allow-Headers', 'Content-Type, Authorization');
        next();
      });
    }
  }

  // ============================================================
  // Internal: Routes
  // ============================================================

  private setupRoutes(): void {
    const router = Router();

    // Health check
    router.get('/health', (_req, res) => {
      this.sendResponse(res, { status: 'ok', timestamp: new Date().toISOString() });
    });

    // Get graph data
    router.get('/graph', async (_req, res) => {
      try {
        const data = await this.getGraphData();
        this.sendResponse(res, data);
      } catch (error) {
        this.sendError(res, 500, error instanceof Error ? error.message : 'Failed to get graph data');
      }
    });

    // Get nodes
    router.get('/nodes', async (_req, res) => {
      try {
        const data = await this.getGraphData();
        this.sendResponse(res, data.nodes);
      } catch (error) {
        this.sendError(res, 500, error instanceof Error ? error.message : 'Failed to get nodes');
      }
    });

    // Get edges
    router.get('/edges', async (_req, res) => {
      try {
        const data = await this.getGraphData();
        this.sendResponse(res, data.edges);
      } catch (error) {
        this.sendError(res, 500, error instanceof Error ? error.message : 'Failed to get edges');
      }
    });

    // Get single node
    router.get('/nodes/:id', async (req, res) => {
      try {
        const data = await this.getGraphData();
        const node = data.nodes.find(n => n.id === req.params.id);
        if (!node) {
          this.sendError(res, 404, 'Node not found');
          return;
        }
        this.sendResponse(res, node);
      } catch (error) {
        this.sendError(res, 500, error instanceof Error ? error.message : 'Failed to get node');
      }
    });

    // SSE endpoint for real-time updates
    if (this.config.enableRealtime) {
      router.get('/events', (req, res) => {
        this.handleSSEConnection(req, res);
      });
    }

    // Cytoscape data format endpoint
    router.get('/cytoscape', async (_req, res) => {
      try {
        const data = await this.getGraphData();
        const cytoscapeData = this.toCytoscapeFormat(data);
        this.sendResponse(res, cytoscapeData);
      } catch (error) {
        this.sendError(res, 500, error instanceof Error ? error.message : 'Failed to get Cytoscape data');
      }
    });

    // Statistics endpoint
    router.get('/stats', async (_req, res) => {
      try {
        const data = await this.getGraphData();
        const stats = {
          nodeCount: data.nodes.length,
          edgeCount: data.edges.length,
          nodeTypes: this.countByType(data.nodes),
          edgeTypes: this.countByType(data.edges),
          namespaces: [...new Set(data.nodes.map(n => n.namespace).filter(Boolean))],
        };
        this.sendResponse(res, stats);
      } catch (error) {
        this.sendError(res, 500, error instanceof Error ? error.message : 'Failed to get stats');
      }
    });

    // Mount API routes
    this.app.use(this.config.apiBasePath || '/api', router);

    // Serve static files (for embedded UI)
    if (this.config.staticDir) {
      this.app.use(express.static(this.config.staticDir));
    }

    // Serve built-in UI
    this.app.get('/', (_req, res) => {
      res.send(this.getBuiltInUI());
    });
  }

  // ============================================================
  // Internal: SSE
  // ============================================================

  /**
   * Handle SSE connection
   * @see REQ-YI-WEB-003
   */
  private handleSSEConnection(req: Request, res: Response): void {
    // Set SSE headers
    res.setHeader('Content-Type', 'text/event-stream');
    res.setHeader('Cache-Control', 'no-cache');
    res.setHeader('Connection', 'keep-alive');

    // Generate client ID
    const clientId = `client-${Date.now()}-${Math.random().toString(36).slice(2)}`;

    // Register client
    this.sseClients.set(clientId, {
      id: clientId,
      response: res,
      namespace: req.query.namespace as string | undefined,
    });

    // Send initial connection event
    res.write(`event: connected\ndata: ${JSON.stringify({ clientId })}\n\n`);

    // Handle client disconnect
    req.on('close', () => {
      this.sseClients.delete(clientId);
    });
  }

  // ============================================================
  // Internal: Helpers
  // ============================================================

  /**
   * Get graph data from provider
   */
  private async getGraphData(): Promise<GraphData> {
    if (!this.dataProvider) {
      return { nodes: [], edges: [] };
    }
    return this.dataProvider();
  }

  /**
   * Send API response
   */
  private sendResponse<T>(res: Response, data: T): void {
    const response: ApiResponse<T> = {
      success: true,
      data,
      timestamp: new Date().toISOString(),
    };
    res.json(response);
  }

  /**
   * Send error response
   */
  private sendError(res: Response, status: number, error: string): void {
    const response: ApiResponse<null> = {
      success: false,
      error,
      timestamp: new Date().toISOString(),
    };
    res.status(status).json(response);
  }

  /**
   * Convert to Cytoscape.js format
   * @see REQ-YI-WEB-001
   */
  private toCytoscapeFormat(data: GraphData): object {
    const elements: object[] = [];

    // Add nodes
    for (const node of data.nodes) {
      elements.push({
        data: {
          id: node.id,
          label: node.label,
          type: node.type,
          namespace: node.namespace,
          ...node.data,
        },
        position: node.position,
      });
    }

    // Add edges
    for (const edge of data.edges) {
      elements.push({
        data: {
          id: edge.id,
          source: edge.source,
          target: edge.target,
          label: edge.label || edge.type,
          type: edge.type,
          weight: edge.weight,
          ...edge.data,
        },
      });
    }

    return { elements };
  }

  /**
   * Count items by type
   */
  private countByType(items: Array<{ type: string }>): Record<string, number> {
    const counts: Record<string, number> = {};
    for (const item of items) {
      counts[item.type] = (counts[item.type] || 0) + 1;
    }
    return counts;
  }

  /**
   * Get built-in UI HTML
   */
  private getBuiltInUI(): string {
    return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>YATA Knowledge Graph</title>
  <script src="https://unpkg.com/cytoscape@3.28.1/dist/cytoscape.min.js"></script>
  <style>
    * { margin: 0; padding: 0; box-sizing: border-box; }
    body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; }
    .container { display: flex; height: 100vh; }
    .sidebar { width: 300px; background: #f5f5f5; padding: 20px; overflow-y: auto; }
    .graph-container { flex: 1; position: relative; }
    #cy { width: 100%; height: 100%; }
    h1 { font-size: 1.5rem; margin-bottom: 20px; color: #333; }
    .stats { margin-bottom: 20px; padding: 15px; background: white; border-radius: 8px; }
    .stat-item { display: flex; justify-content: space-between; margin: 8px 0; }
    .stat-label { color: #666; }
    .stat-value { font-weight: bold; color: #333; }
    .controls { margin-top: 20px; }
    button { padding: 10px 20px; margin: 5px 0; width: 100%; border: none; border-radius: 6px; 
             cursor: pointer; font-size: 14px; transition: background 0.2s; }
    .btn-primary { background: #0066cc; color: white; }
    .btn-primary:hover { background: #0052a3; }
    .btn-secondary { background: #e0e0e0; color: #333; }
    .btn-secondary:hover { background: #d0d0d0; }
    .node-info { margin-top: 20px; padding: 15px; background: white; border-radius: 8px; display: none; }
    .node-info.active { display: block; }
    .node-info h3 { margin-bottom: 10px; color: #333; }
    .node-info p { margin: 5px 0; color: #666; font-size: 14px; }
    .legend { margin-top: 20px; }
    .legend-item { display: flex; align-items: center; margin: 5px 0; }
    .legend-color { width: 16px; height: 16px; border-radius: 4px; margin-right: 8px; }
    .connection-status { position: fixed; top: 10px; right: 10px; padding: 8px 16px; 
                         border-radius: 20px; font-size: 12px; }
    .status-connected { background: #d4edda; color: #155724; }
    .status-disconnected { background: #f8d7da; color: #721c24; }
  </style>
</head>
<body>
  <div id="connection-status" class="connection-status status-disconnected">Disconnected</div>
  <div class="container">
    <div class="sidebar">
      <h1>📊 YATA Graph</h1>
      <div id="stats" class="stats">
        <div class="stat-item"><span class="stat-label">Nodes:</span><span id="node-count" class="stat-value">-</span></div>
        <div class="stat-item"><span class="stat-label">Edges:</span><span id="edge-count" class="stat-value">-</span></div>
      </div>
      <div class="controls">
        <button class="btn-primary" onclick="refreshGraph()">🔄 Refresh</button>
        <button class="btn-secondary" onclick="fitGraph()">📐 Fit to View</button>
        <button class="btn-secondary" onclick="exportPNG()">📸 Export PNG</button>
      </div>
      <div id="node-info" class="node-info">
        <h3 id="selected-name">Selected Node</h3>
        <p><strong>ID:</strong> <span id="selected-id">-</span></p>
        <p><strong>Type:</strong> <span id="selected-type">-</span></p>
        <p><strong>Namespace:</strong> <span id="selected-ns">-</span></p>
      </div>
      <div class="legend">
        <h4>Node Types</h4>
        <div class="legend-item"><div class="legend-color" style="background:#4CAF50"></div>Entity</div>
        <div class="legend-item"><div class="legend-color" style="background:#2196F3"></div>Class</div>
        <div class="legend-item"><div class="legend-color" style="background:#FF9800"></div>Function</div>
        <div class="legend-item"><div class="legend-color" style="background:#9C27B0"></div>Interface</div>
      </div>
    </div>
    <div class="graph-container">
      <div id="cy"></div>
    </div>
  </div>
  <script>
    const API_BASE = '${this.config.apiBasePath || '/api'}';
    let cy;
    let eventSource;

    const typeColors = {
      entity: '#4CAF50', class: '#2196F3', function: '#FF9800',
      interface: '#9C27B0', module: '#607D8B', default: '#9E9E9E'
    };

    async function initGraph() {
      cy = cytoscape({
        container: document.getElementById('cy'),
        style: [
          { selector: 'node', style: {
            'label': 'data(label)', 'text-valign': 'center', 'text-halign': 'center',
            'background-color': 'data(color)', 'color': '#fff', 'font-size': '12px',
            'text-outline-width': 2, 'text-outline-color': 'data(color)',
            'width': 60, 'height': 60
          }},
          { selector: 'edge', style: {
            'label': 'data(label)', 'curve-style': 'bezier', 'target-arrow-shape': 'triangle',
            'line-color': '#999', 'target-arrow-color': '#999', 'font-size': '10px',
            'text-background-color': '#fff', 'text-background-opacity': 0.8,
            'text-background-padding': '2px'
          }},
          { selector: ':selected', style: {
            'border-width': 3, 'border-color': '#ff0066'
          }}
        ],
        layout: { name: 'cose', animate: false }
      });

      cy.on('tap', 'node', function(e) {
        const node = e.target.data();
        document.getElementById('selected-name').textContent = node.label;
        document.getElementById('selected-id').textContent = node.id;
        document.getElementById('selected-type').textContent = node.type || '-';
        document.getElementById('selected-ns').textContent = node.namespace || '-';
        document.getElementById('node-info').classList.add('active');
      });

      cy.on('tap', function(e) {
        if (e.target === cy) {
          document.getElementById('node-info').classList.remove('active');
        }
      });

      await refreshGraph();
      connectSSE();
    }

    async function refreshGraph() {
      try {
        const res = await fetch(API_BASE + '/cytoscape');
        const json = await res.json();
        if (json.success) {
          const elements = json.data.elements.map(el => {
            if (el.data && !el.data.source) {
              el.data.color = typeColors[el.data.type] || typeColors.default;
            }
            return el;
          });
          cy.json({ elements });
          cy.layout({ name: 'cose', animate: true, animationDuration: 500 }).run();
          updateStats();
        }
      } catch (err) { console.error('Failed to refresh:', err); }
    }

    function updateStats() {
      document.getElementById('node-count').textContent = cy.nodes().length;
      document.getElementById('edge-count').textContent = cy.edges().length;
    }

    function fitGraph() { cy.fit(50); }
    function exportPNG() { const png = cy.png({ full: true }); window.open(png, '_blank'); }

    function connectSSE() {
      if (eventSource) eventSource.close();
      eventSource = new EventSource(API_BASE + '/events');
      eventSource.onopen = () => {
        document.getElementById('connection-status').textContent = 'Connected';
        document.getElementById('connection-status').className = 'connection-status status-connected';
      };
      eventSource.onerror = () => {
        document.getElementById('connection-status').textContent = 'Disconnected';
        document.getElementById('connection-status').className = 'connection-status status-disconnected';
      };
      eventSource.addEventListener('update', () => refreshGraph());
    }

    initGraph();
  </script>
</body>
</html>`;
  }
}

/**
 * Factory function to create YataUIServer
 */
export function createYataUIServer(config?: Partial<UIServerConfig>): YataUIServer {
  return new YataUIServer(config);
}
