// Tests for Route entity
// REQ-ROUTE-001, REQ-ROUTE-002

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createRoute,
  createRouteTable,
  matchRoute,
  patternToRegex,
  resetRouteCounter,
  type RouteInput,
  type BackendInstance,
} from '../src/domain/route.js';

describe('Route', () => {
  beforeEach(() => {
    resetRouteCounter();
  });

  const backend: BackendInstance = {
    id: 'backend-1',
    host: 'localhost',
    port: 3001,
    weight: 1,
    healthy: true,
  };

  describe('patternToRegex', () => {
    it('should match exact paths', () => {
      const regex = patternToRegex('/api/users');
      expect(regex.test('/api/users')).toBe(true);
      expect(regex.test('/api/users/')).toBe(false);
      expect(regex.test('/api/users/123')).toBe(false);
    });

    it('should match wildcard paths', () => {
      const regex = patternToRegex('/api/users/*');
      expect(regex.test('/api/users/123')).toBe(true);
      expect(regex.test('/api/users/abc')).toBe(true);
      expect(regex.test('/api/users/')).toBe(false);
      expect(regex.test('/api/users')).toBe(false);
    });

    it('should be case-insensitive', () => {
      const regex = patternToRegex('/api/Users');
      expect(regex.test('/api/users')).toBe(true);
      expect(regex.test('/API/USERS')).toBe(true);
    });
  });

  describe('createRoute', () => {
    it('should create route with valid input', () => {
      const input: RouteInput = {
        pathPattern: '/api/users',
        methods: ['GET', 'POST'],
        backends: [backend],
        isPublic: true,
      };

      const route = createRoute(input);

      expect(route.id.value).toBe('ROUTE-0001');
      expect(route.pathPattern).toBe('/api/users');
      expect(route.methods).toEqual(['GET', 'POST']);
      expect(route.isPublic).toBe(true);
    });

    it('should default isPublic to false', () => {
      const input: RouteInput = {
        pathPattern: '/api/admin',
        methods: ['GET'],
        backends: [backend],
      };

      const route = createRoute(input);
      expect(route.isPublic).toBe(false);
    });

    it('should throw for empty path pattern', () => {
      const input: RouteInput = {
        pathPattern: '',
        methods: ['GET'],
        backends: [backend],
      };

      expect(() => createRoute(input)).toThrow('Path pattern is required');
    });

    it('should throw for path not starting with /', () => {
      const input: RouteInput = {
        pathPattern: 'api/users',
        methods: ['GET'],
        backends: [backend],
      };

      expect(() => createRoute(input)).toThrow('must start with /');
    });

    it('should throw for empty methods', () => {
      const input: RouteInput = {
        pathPattern: '/api/users',
        methods: [],
        backends: [backend],
      };

      expect(() => createRoute(input)).toThrow('At least one HTTP method');
    });

    it('should throw for empty backends', () => {
      const input: RouteInput = {
        pathPattern: '/api/users',
        methods: ['GET'],
        backends: [],
      };

      expect(() => createRoute(input)).toThrow('At least one backend');
    });
  });

  describe('matchRoute', () => {
    it('should match exact path', () => {
      const route = createRoute({
        pathPattern: '/api/users',
        methods: ['GET'],
        backends: [backend],
      });
      const table = createRouteTable([route]);

      const match = matchRoute(table, '/api/users', 'GET');

      expect(match).not.toBeNull();
      expect(match?.route.id.value).toBe(route.id.value);
    });

    it('should match wildcard path', () => {
      const route = createRoute({
        pathPattern: '/api/users/*',
        methods: ['GET'],
        backends: [backend],
      });
      const table = createRouteTable([route]);

      const match = matchRoute(table, '/api/users/123', 'GET');

      expect(match).not.toBeNull();
    });

    it('should not match wrong method', () => {
      const route = createRoute({
        pathPattern: '/api/users',
        methods: ['GET'],
        backends: [backend],
      });
      const table = createRouteTable([route]);

      const match = matchRoute(table, '/api/users', 'POST');

      expect(match).toBeNull();
    });

    it('should match by version', () => {
      const v1Route = createRoute({
        pathPattern: '/api/users',
        methods: ['GET'],
        backends: [backend],
        version: 'v1',
      });
      const v2Route = createRoute({
        pathPattern: '/api/users',
        methods: ['GET'],
        backends: [backend],
        version: 'v2',
      });
      const table = createRouteTable([v1Route, v2Route]);

      const matchV1 = matchRoute(table, '/api/users', 'GET', 'v1');
      const matchV2 = matchRoute(table, '/api/users', 'GET', 'v2');

      expect(matchV1?.route.version).toBe('v1');
      expect(matchV2?.route.version).toBe('v2');
    });

    it('should return null for no match', () => {
      const route = createRoute({
        pathPattern: '/api/users',
        methods: ['GET'],
        backends: [backend],
      });
      const table = createRouteTable([route]);

      const match = matchRoute(table, '/api/products', 'GET');

      expect(match).toBeNull();
    });
  });
});
