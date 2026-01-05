# API Gateway - Architecture Design

## Document Information
- **Project**: API Gateway
- **Level**: C4 Component
- **Author**: MUSUBIX SDD System
- **Date**: 2025-01-06
- **Status**: Validated

---

## Context Level

### System Context

```
┌─────────────────────────────────────────────────────────────────┐
│                        External World                            │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐                      │
│  │ Web App  │  │ Mobile   │  │ Third    │                      │
│  │ Client   │  │ App      │  │ Party    │                      │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘                      │
│       │             │             │                              │
│       └─────────────┼─────────────┘                              │
│                     │                                            │
│                     ▼                                            │
│           ┌─────────────────┐                                   │
│           │   API Gateway   │◄─────── All requests enter here   │
│           └────────┬────────┘                                   │
│                    │                                             │
│       ┌────────────┼────────────┐                               │
│       │            │            │                                │
│       ▼            ▼            ▼                                │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐                         │
│  │ User    │  │ Order   │  │ Product │                         │
│  │ Service │  │ Service │  │ Service │                         │
│  └─────────┘  └─────────┘  └─────────┘                         │
└─────────────────────────────────────────────────────────────────┘
```

---

## Container Level

### API Gateway Container

| Container | Technology | Purpose |
|-----------|------------|---------|
| Gateway Core | Node.js/TypeScript | Request processing pipeline |
| Cache Store | In-Memory/Redis | Response caching |
| Rate Limit Store | In-Memory | Rate limit counters |
| Config Store | File/Remote | Route and policy configuration |

---

## Component Level

### Domain Layer Components

| Component | Requirement | Description |
|-----------|-------------|-------------|
| Route | REQ-ROUTE-001 | URL path pattern and backend mapping |
| RouteTable | REQ-ROUTE-001 | Collection of routes with matching logic |
| BackendInstance | REQ-ROUTE-003 | Single backend server address |
| LoadBalancer | REQ-ROUTE-003 | Distribution strategy (round-robin, weighted) |
| CircuitBreaker | REQ-ROUTE-004 | Circuit state management (closed, open, half-open) |
| RateLimitBucket | REQ-RATE-001/002 | Sliding window counter per client |
| RateLimitTier | REQ-RATE-004 | Tier configuration (free, standard, premium) |
| ApiKey | REQ-AUTH-001 | API key entity with metadata |
| JwtToken | REQ-AUTH-002 | Parsed JWT with claims |
| AccessPolicy | REQ-AUTH-003 | RBAC policy for route |
| CacheEntry | REQ-CACHE-001/002 | Cached response with TTL |
| Request | REQ-XFORM-001 | Incoming request with headers |
| Response | REQ-XFORM-002 | Outgoing response |

### Application Layer Components

| Service | Requirements | Responsibility |
|---------|--------------|----------------|
| RequestRouter | REQ-ROUTE-001/002 | Match request to route and backend |
| LoadBalancerService | REQ-ROUTE-003 | Select backend instance |
| CircuitBreakerService | REQ-ROUTE-004 | Track failures and manage circuit state |
| RateLimitService | REQ-RATE-001/002/003 | Check and update rate limits |
| AuthenticationService | REQ-AUTH-001/002 | Validate API keys and JWT tokens |
| AuthorizationService | REQ-AUTH-003/004 | Check role-based access |
| CacheService | REQ-CACHE-001/002/003 | Get/set/invalidate cache |
| TransformationService | REQ-XFORM-001/002 | Add headers, compress responses |
| SecurityService | REQ-SEC-001/002 | Validate size, sanitize headers |

### Infrastructure Layer Components

| Component | Purpose |
|-----------|---------|
| InMemoryRateLimitStore | Store rate limit buckets in memory |
| InMemoryCacheStore | Store cached responses in memory |
| RedisCacheStore | Optional Redis-backed cache |
| ConfigFileLoader | Load route config from YAML/JSON |
| HttpClient | Forward requests to backends |
| MetricsCollector | Collect latency and request counts |

---

## Design Patterns Applied

### 1. Chain of Responsibility (Request Pipeline)
```
Request → Security → Auth → RateLimit → Cache → Route → Backend
```

### 2. Strategy Pattern (Load Balancing)
- RoundRobinStrategy
- WeightedStrategy
- LeastConnectionsStrategy

### 3. Circuit Breaker Pattern
```
States: CLOSED → OPEN → HALF_OPEN → CLOSED
```

### 4. Singleton Pattern
- RouteTable (single instance)
- MetricsCollector

### 5. Factory Pattern
- CacheStoreFactory (memory vs redis)
- LoadBalancerFactory

---

## Component Relationships

### Request Flow

```
┌─────────────────────────────────────────────────────────────────┐
│                     Request Processing Pipeline                  │
│                                                                  │
│  Request                                                        │
│     │                                                           │
│     ▼                                                           │
│  ┌─────────────────┐                                           │
│  │ SecurityService │──▶ Check size, sanitize headers           │
│  └────────┬────────┘                                           │
│           │                                                     │
│           ▼                                                     │
│  ┌─────────────────────┐                                       │
│  │ AuthenticationSvc   │──▶ Validate API key / JWT             │
│  └────────┬────────────┘                                       │
│           │                                                     │
│           ▼                                                     │
│  ┌─────────────────────┐                                       │
│  │ AuthorizationSvc    │──▶ Check role permissions             │
│  └────────┬────────────┘                                       │
│           │                                                     │
│           ▼                                                     │
│  ┌─────────────────────┐                                       │
│  │ RateLimitService    │──▶ Check/update rate limit            │
│  └────────┬────────────┘                                       │
│           │                                                     │
│           ▼                                                     │
│  ┌─────────────────────┐                                       │
│  │ CacheService        │──▶ Return cached if available         │
│  └────────┬────────────┘                                       │
│           │                                                     │
│           ▼                                                     │
│  ┌─────────────────────┐                                       │
│  │ RequestRouter       │──▶ Match route and select backend     │
│  └────────┬────────────┘                                       │
│           │                                                     │
│           ▼                                                     │
│  ┌─────────────────────┐                                       │
│  │ CircuitBreakerSvc   │──▶ Check circuit state                │
│  └────────┬────────────┘                                       │
│           │                                                     │
│           ▼                                                     │
│  ┌─────────────────────┐                                       │
│  │ TransformationSvc   │──▶ Add correlation ID                 │
│  └────────┬────────────┘                                       │
│           │                                                     │
│           ▼                                                     │
│       Backend                                                   │
└─────────────────────────────────────────────────────────────────┘
```

---

## Requirement Traceability

| Requirement | Design Element | Component |
|-------------|----------------|-----------|
| REQ-ROUTE-001 | Route, RouteTable | RequestRouter |
| REQ-ROUTE-002 | Route (version field) | RequestRouter |
| REQ-ROUTE-003 | BackendInstance, LoadBalancer | LoadBalancerService |
| REQ-ROUTE-004 | CircuitBreaker | CircuitBreakerService |
| REQ-RATE-001 | RateLimitBucket | RateLimitService |
| REQ-RATE-002 | SlidingWindow algorithm | RateLimitService |
| REQ-RATE-003 | HTTP 429 response | RateLimitService |
| REQ-RATE-004 | RateLimitTier | RateLimitService |
| REQ-AUTH-001 | ApiKey | AuthenticationService |
| REQ-AUTH-002 | JwtToken | AuthenticationService |
| REQ-AUTH-003 | AccessPolicy | AuthorizationService |
| REQ-AUTH-004 | isPublic flag | AuthorizationService |
| REQ-CACHE-001 | CacheEntry | CacheService |
| REQ-CACHE-002 | Cache lookup | CacheService |
| REQ-CACHE-003 | Cache invalidation | CacheService |
| REQ-XFORM-001 | Correlation ID | TransformationService |
| REQ-XFORM-002 | Compression | TransformationService |
| REQ-SEC-001 | Size check | SecurityService |
| REQ-SEC-002 | Header sanitization | SecurityService |
| REQ-PERF-001 | Async processing | All components |
| REQ-PERF-002 | Efficient matching | RequestRouter |

---

## SOLID Compliance

| Principle | Implementation |
|-----------|----------------|
| **Single Responsibility** | Each service handles one concern |
| **Open/Closed** | Strategy pattern for load balancing |
| **Liskov Substitution** | Cache stores are interchangeable |
| **Interface Segregation** | Separate interfaces for each service |
| **Dependency Inversion** | Services depend on abstractions |
