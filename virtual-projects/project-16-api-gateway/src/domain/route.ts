// REQ-ROUTE-001, REQ-ROUTE-002: Route and RouteTable
// Traces to: DES-ROUTE-001, DES-ROUTE-002

/**
 * HTTP methods supported by routes
 */
export type HttpMethod = 'GET' | 'POST' | 'PUT' | 'DELETE' | 'PATCH' | 'HEAD' | 'OPTIONS';

/**
 * Route ID value object
 */
export interface RouteId {
  readonly value: string;
}

/**
 * Backend instance for load balancing
 * @requirement REQ-ROUTE-003
 */
export interface BackendInstance {
  id: string;
  host: string;
  port: number;
  weight: number;
  healthy: boolean;
}

/**
 * Route configuration input
 * @requirement REQ-ROUTE-001
 */
export interface RouteInput {
  pathPattern: string;
  methods: HttpMethod[];
  backends: BackendInstance[];
  version?: string;
  isPublic?: boolean;
  requiredRoles?: string[];
  cacheTtlSeconds?: number;
}

/**
 * Route entity
 * @requirement REQ-ROUTE-001, REQ-ROUTE-002
 */
export interface Route {
  readonly id: RouteId;
  pathPattern: string;
  pathRegex: RegExp;
  methods: HttpMethod[];
  backends: BackendInstance[];
  version?: string;
  isPublic: boolean;
  requiredRoles: string[];
  cacheTtlSeconds?: number;
  createdAt: Date;
}

let routeCounter = 0;

/**
 * Reset route counter (for testing)
 */
export function resetRouteCounter(): void {
  routeCounter = 0;
}

/**
 * Generate route ID
 */
export function generateRouteId(): RouteId {
  routeCounter++;
  return { value: `ROUTE-${String(routeCounter).padStart(4, '0')}` };
}

/**
 * Convert path pattern to regex
 * Supports wildcards: /api/users/* matches /api/users/123
 * @requirement REQ-ROUTE-001
 */
export function patternToRegex(pattern: string): RegExp {
  // Escape special regex characters except *
  const escaped = pattern.replace(/[.+?^${}()|[\]\\]/g, '\\$&');
  // Convert * to regex pattern
  const regexPattern = escaped.replace(/\*/g, '[^/]+');
  // Match full path
  return new RegExp(`^${regexPattern}$`, 'i');
}

/**
 * Create a route
 * @requirement REQ-ROUTE-001
 */
export function createRoute(input: RouteInput): Route {
  if (!input.pathPattern || input.pathPattern.length === 0) {
    throw new Error('Path pattern is required');
  }
  if (!input.pathPattern.startsWith('/')) {
    throw new Error('Path pattern must start with /');
  }
  if (!input.methods || input.methods.length === 0) {
    throw new Error('At least one HTTP method is required');
  }
  if (!input.backends || input.backends.length === 0) {
    throw new Error('At least one backend is required');
  }

  return {
    id: generateRouteId(),
    pathPattern: input.pathPattern,
    pathRegex: patternToRegex(input.pathPattern),
    methods: input.methods,
    backends: input.backends,
    version: input.version,
    isPublic: input.isPublic ?? false,
    requiredRoles: input.requiredRoles ?? [],
    cacheTtlSeconds: input.cacheTtlSeconds,
    createdAt: new Date(),
  };
}

/**
 * Match result
 */
export interface RouteMatch {
  route: Route;
  params: Record<string, string>;
}

/**
 * Route table for matching requests to routes
 * @requirement REQ-ROUTE-001
 */
export interface RouteTable {
  routes: Route[];
}

/**
 * Create route table
 */
export function createRouteTable(routes: Route[]): RouteTable {
  return { routes };
}

/**
 * Find matching route for request
 * @requirement REQ-ROUTE-001, REQ-ROUTE-002
 */
export function matchRoute(
  table: RouteTable,
  path: string,
  method: HttpMethod,
  version?: string
): RouteMatch | null {
  // Filter by version if specified
  const candidates = version
    ? table.routes.filter((r) => !r.version || r.version === version)
    : table.routes;

  for (const route of candidates) {
    // Check method
    if (!route.methods.includes(method)) {
      continue;
    }

    // Check path pattern
    const match = route.pathRegex.exec(path);
    if (match) {
      return { route, params: {} };
    }
  }

  return null;
}
