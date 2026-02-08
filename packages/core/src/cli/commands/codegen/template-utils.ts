/**
 * Template Utilities
 *
 * Shared template string helpers for code generation
 *
 * @packageDocumentation
 * @module cli/commands/codegen/template-utils
 *
 * @see REQ-CG-001 - Code Generation
 */

import type { MethodSignature } from '../../../design/component-inference.js';
import type { C4Component, DesignPattern } from './types.js';

/**
 * Parse C4 design document components from table format
 */
export function parseC4DesignComponents(content: string): C4Component[] {
  const components: C4Component[] = [];

  // Match table rows: | ID | Name | Type | Description | or | ID | Name | Type | Description | Pattern |
  // Support both 4 and 5 column formats
  // ID can be alphanumeric with hyphens (e.g., DES-001, COMP-01)
  // Use [^|\n] to avoid matching across lines, and [ \t]* instead of \s* to avoid newlines
  const tableRowRegex = /\|\s*([\w-]+)\s*\|\s*(\w+)\s*\|\s*(\w+)\s*\|\s*([^|\n]+?)\s*\|(?:[ \t]*([^|\n]*?)[ \t]*\|)?/g;
  let match;

  while ((match = tableRowRegex.exec(content)) !== null) {
    const [, id, name, type, description, pattern] = match;
    // Skip header row and separator row
    if (id === 'ID' || id === '----' || id.startsWith('-') || name === '----' || name === 'Name') continue;
    // Skip separator row like |----|----|----|
    if (id.match(/^-+$/)) continue;

    components.push({
      id,
      name,
      type: type.toLowerCase(),
      description: description.trim(),
      pattern: pattern?.trim() || undefined,
    });
  }

  return components;
}

/**
 * Extract design patterns from document
 */
export function extractDesignPatterns(content: string): DesignPattern[] {
  const patterns: DesignPattern[] = [];

  // Match pattern sections: ### PatternName
  const patternSectionRegex = /###\s+(\w+)\s*\n.*?Category:\s*(\w+).*?Intent:\s*(.+?)(?=\n\n|$)/gis;
  let match: RegExpExecArray | null;

  while ((match = patternSectionRegex.exec(content)) !== null) {
    patterns.push({
      name: match[1],
      category: match[2],
      intent: match[3].trim(),
    });
  }

  // Also try simpler pattern: - **Category**: behavioral
  const simplePatternRegex = /###\s+(\w+)\s*\n-\s*\*\*Category\*\*:\s*(\w+)\s*\n-\s*\*\*Intent\*\*:\s*(.+)/gi;
  let simpleMatch: RegExpExecArray | null;

  while ((simpleMatch = simplePatternRegex.exec(content)) !== null) {
    // Avoid duplicates
    if (!patterns.find(p => p.name === simpleMatch![1])) {
      patterns.push({
        name: simpleMatch[1],
        category: simpleMatch[2],
        intent: simpleMatch[3].trim(),
      });
    }
  }

  return patterns;
}

/**
 * Extract EARS requirements from content
 */
export function extractEarsRequirements(content: string): Array<{
  id: string;
  pattern: string;
  priority: string;
  description: string;
}> {
  const requirements: Array<{ id: string; pattern: string; priority: string; description: string }> = [];

  // Match EARS requirements from table or detailed sections
  // Format: | REQ-XX-001 | pattern | P0 | description |
  const tableMatches = content.matchAll(/\|\s*(REQ-[\w-]+)\s*\|\s*([\w-]+)\s*\|\s*(P\d)\s*\|\s*([^|]+)\|/g);
  for (const match of tableMatches) {
    requirements.push({
      id: match[1],
      pattern: match[2].toLowerCase(),
      priority: match[3],
      description: match[4].trim(),
    });
  }

  // Also extract from detailed sections
  // Format: ### REQ-XX-001 (Pattern - P0)
  // > The system SHALL...
  const detailMatches = content.matchAll(/###\s*(REQ-[\w-]+)\s*\((\w+)\s*-\s*(P\d)\)\s*\n+>\s*(.+?)(?=\n\n|\n###|$)/gs);
  for (const match of detailMatches) {
    const existing = requirements.find(r => r.id === match[1]);
    if (!existing) {
      requirements.push({
        id: match[1],
        pattern: match[2].toLowerCase(),
        priority: match[3],
        description: match[4].trim(),
      });
    }
  }

  return requirements;
}

/**
 * Generate method stubs based on component type and description
 */
export function generateMethodStubsForComponent(type: string, description: string): Array<{
  name: string;
  params: string;
  returnType: string;
  description: string;
  async: boolean;
}> {
  const lowerDesc = description.toLowerCase();
  const lowerType = type.toLowerCase();
  const methods: Array<{
    name: string;
    params: string;
    returnType: string;
    description: string;
    async: boolean;
  }> = [];

  // Order/Booking service patterns
  if (lowerDesc.includes('order') || lowerDesc.includes('\u6CE8\u6587') || lowerDesc.includes('\u4E88\u7D04') || lowerDesc.includes('booking')) {
    methods.push(
      {
        name: 'create',
        params: 'data: OrderInput',
        returnType: 'Promise<Order>',
        description: 'Create a new order',
        async: true,
      },
      {
        name: 'submit',
        params: 'orderId: string',
        returnType: 'Promise<Order>',
        description: 'Submit order for processing',
        async: true,
      },
      {
        name: 'cancel',
        params: 'orderId: string, reason?: string',
        returnType: 'Promise<boolean>',
        description: 'Cancel an order',
        async: true,
      },
      {
        name: 'getStatus',
        params: 'orderId: string',
        returnType: 'Promise<OrderStatus>',
        description: 'Get order status',
        async: true,
      },
      {
        name: 'getByCustomer',
        params: 'customerId: string',
        returnType: 'Promise<Order[]>',
        description: 'Get orders by customer',
        async: true,
      }
    );
    return methods;
  }

  // Schedule/Appointment service patterns
  if (lowerDesc.includes('schedule') || lowerDesc.includes('appointment') || lowerDesc.includes('\u30B9\u30B1\u30B8\u30E5\u30FC\u30EB') || lowerDesc.includes('\u4E88\u5B9A')) {
    methods.push(
      {
        name: 'book',
        params: 'slot: TimeSlot, details: BookingDetails',
        returnType: 'Promise<Appointment>',
        description: 'Book an appointment',
        async: true,
      },
      {
        name: 'checkAvailability',
        params: 'date: Date, duration: number',
        returnType: 'Promise<TimeSlot[]>',
        description: 'Check available time slots',
        async: true,
      },
      {
        name: 'reschedule',
        params: 'appointmentId: string, newSlot: TimeSlot',
        returnType: 'Promise<Appointment>',
        description: 'Reschedule an appointment',
        async: true,
      },
      {
        name: 'cancel',
        params: 'appointmentId: string',
        returnType: 'Promise<boolean>',
        description: 'Cancel an appointment',
        async: true,
      }
    );
    return methods;
  }

  // Pricing/Payment service patterns
  if (lowerDesc.includes('pricing') || lowerDesc.includes('payment') || lowerDesc.includes('price') || lowerDesc.includes('\u4FA1\u683C') || lowerDesc.includes('\u6C7A\u6E08')) {
    methods.push(
      {
        name: 'calculate',
        params: 'items: PricingItem[]',
        returnType: 'Promise<PricingResult>',
        description: 'Calculate total price',
        async: true,
      },
      {
        name: 'applyDiscount',
        params: 'basePrice: number, discountCode: string',
        returnType: 'Promise<{ price: number; discount: number }>',
        description: 'Apply discount to price',
        async: true,
      },
      {
        name: 'processPayment',
        params: 'amount: number, paymentMethod: PaymentMethod',
        returnType: 'Promise<PaymentResult>',
        description: 'Process payment',
        async: true,
      },
      {
        name: 'refund',
        params: 'transactionId: string, amount?: number',
        returnType: 'Promise<RefundResult>',
        description: 'Process refund',
        async: true,
      }
    );
    return methods;
  }

  // Inventory service patterns
  if (lowerDesc.includes('inventory') || lowerDesc.includes('stock') || lowerDesc.includes('\u5728\u5EAB')) {
    methods.push(
      {
        name: 'checkStock',
        params: 'itemId: string',
        returnType: 'Promise<StockLevel>',
        description: 'Check stock level',
        async: true,
      },
      {
        name: 'reserve',
        params: 'itemId: string, quantity: number',
        returnType: 'Promise<Reservation>',
        description: 'Reserve stock',
        async: true,
      },
      {
        name: 'release',
        params: 'reservationId: string',
        returnType: 'Promise<boolean>',
        description: 'Release reserved stock',
        async: true,
      },
      {
        name: 'updateStock',
        params: 'itemId: string, delta: number',
        returnType: 'Promise<StockLevel>',
        description: 'Update stock level',
        async: true,
      }
    );
    return methods;
  }

  // Service patterns - CRUD operations (generic fallback)
  if (lowerType === 'service' || lowerDesc.includes('crud') || lowerDesc.includes('\u7BA1\u7406')) {
    methods.push(
      {
        name: 'create',
        params: 'data: CreateInput',
        returnType: 'Promise<Entity>',
        description: 'Create a new entity',
        async: true,
      },
      {
        name: 'getById',
        params: 'id: string',
        returnType: 'Promise<Entity | null>',
        description: 'Get entity by ID',
        async: true,
      },
      {
        name: 'getAll',
        params: 'filter?: FilterOptions',
        returnType: 'Promise<Entity[]>',
        description: 'Get all entities',
        async: true,
      },
      {
        name: 'update',
        params: 'id: string, data: UpdateInput',
        returnType: 'Promise<Entity>',
        description: 'Update an entity',
        async: true,
      },
      {
        name: 'delete',
        params: 'id: string',
        returnType: 'Promise<boolean>',
        description: 'Delete an entity',
        async: true,
      }
    );
    return methods;
  }

  // Repository patterns
  if (lowerType === 'repository' || lowerDesc.includes('storage') || lowerDesc.includes('persist') || lowerDesc.includes('\u6C38\u7D9A\u5316')) {
    methods.push(
      {
        name: 'save',
        params: 'key: string, data: T',
        returnType: 'void',
        description: 'Save data',
        async: false,
      },
      {
        name: 'load',
        params: 'key: string',
        returnType: 'T | null',
        description: 'Load data',
        async: false,
      },
      {
        name: 'remove',
        params: 'key: string',
        returnType: 'void',
        description: 'Remove data',
        async: false,
      },
      {
        name: 'clear',
        params: '',
        returnType: 'void',
        description: 'Clear all data',
        async: false,
      }
    );
    return methods;
  }

  // Validator patterns
  if (lowerType === 'validator' || lowerDesc.includes('validat') || lowerDesc.includes('\u691C\u8A3C') || lowerDesc.includes('\u5165\u529B')) {
    methods.push(
      {
        name: 'validate',
        params: 'input: ValidationInput',
        returnType: 'ValidationResult',
        description: 'Validate input data',
        async: false,
      },
      {
        name: 'validateField',
        params: 'fieldName: string, value: string | number | boolean',
        returnType: '{ valid: boolean; error?: string }',
        description: 'Validate a single field',
        async: false,
      },
      {
        name: 'sanitize',
        params: 'input: string',
        returnType: 'string',
        description: 'Sanitize input string',
        async: false,
      },
      {
        name: 'getValidationRules',
        params: '',
        returnType: 'ValidationRule[]',
        description: 'Get validation rules',
        async: false,
      }
    );
    return methods;
  }

  // Search/Filter patterns
  if (lowerDesc.includes('search') || lowerDesc.includes('filter') || lowerDesc.includes('\u691C\u7D22') || lowerDesc.includes('\u30D5\u30A3\u30EB\u30BF')) {
    methods.push(
      {
        name: 'search',
        params: 'query: string',
        returnType: 'Promise<SearchResult[]>',
        description: 'Search items',
        async: true,
      },
      {
        name: 'filter',
        params: 'criteria: FilterCriteria',
        returnType: 'Promise<Entity[]>',
        description: 'Filter items by criteria',
        async: true,
      },
      {
        name: 'sort',
        params: 'items: Entity[], sortBy: string',
        returnType: 'Entity[]',
        description: 'Sort items',
        async: false,
      }
    );
    return methods;
  }

  // Notification/Alert patterns
  if (lowerDesc.includes('notification') || lowerDesc.includes('alert') || lowerDesc.includes('\u901A\u77E5') || lowerDesc.includes('\u30A2\u30E9\u30FC\u30C8')) {
    methods.push(
      {
        name: 'subscribe',
        params: 'callback: (event: Event) => void',
        returnType: '() => void',
        description: 'Subscribe to events',
        async: false,
      },
      {
        name: 'notify',
        params: 'event: Event',
        returnType: 'void',
        description: 'Notify subscribers',
        async: false,
      },
      {
        name: 'checkConditions',
        params: '',
        returnType: 'Promise<Alert[]>',
        description: 'Check alert conditions',
        async: true,
      }
    );
    return methods;
  }

  // Export/Import patterns
  if (lowerDesc.includes('export') || lowerDesc.includes('import') || lowerDesc.includes('\u30A8\u30AF\u30B9\u30DD\u30FC\u30C8') || lowerDesc.includes('\u30A4\u30F3\u30DD\u30FC\u30C8')) {
    methods.push(
      {
        name: 'exportToJson',
        params: 'data: Entity[]',
        returnType: 'string',
        description: 'Export data to JSON',
        async: false,
      },
      {
        name: 'importFromJson',
        params: 'json: string',
        returnType: '{ success: boolean; imported: number; errors: string[] }',
        description: 'Import data from JSON',
        async: false,
      }
    );
    return methods;
  }

  // Authentication patterns
  if (lowerDesc.includes('auth') || lowerDesc.includes('login') || lowerDesc.includes('\u8A8D\u8A3C')) {
    methods.push(
      {
        name: 'authenticate',
        params: 'credentials: { username: string; password: string }',
        returnType: 'Promise<{ token: string }>',
        description: 'Authenticate user',
        async: true,
      },
      {
        name: 'validateToken',
        params: 'token: string',
        returnType: 'Promise<boolean>',
        description: 'Validate token',
        async: true,
      }
    );
    return methods;
  }

  // Entity/Model patterns
  if (lowerType === 'entity' || lowerType === 'model' || lowerDesc.includes('\u30C7\u30FC\u30BF\u30E2\u30C7\u30EB') || lowerDesc.includes('\u30A8\u30F3\u30C6\u30A3\u30C6\u30A3')) {
    methods.push(
      {
        name: 'toJSON',
        params: '',
        returnType: 'EntityData',
        description: 'Convert to JSON object',
        async: false,
      },
      {
        name: 'clone',
        params: '',
        returnType: 'this',
        description: 'Create a deep clone',
        async: false,
      },
      {
        name: 'equals',
        params: 'other: this',
        returnType: 'boolean',
        description: 'Check equality with another entity',
        async: false,
      },
      {
        name: 'validate',
        params: '',
        returnType: 'boolean',
        description: 'Validate entity state',
        async: false,
      }
    );
    return methods;
  }

  // Component/UI patterns (check before specific domain patterns)
  if (lowerType === 'component' && (lowerDesc.includes('\u8868\u793A') || lowerDesc.includes('ui') || lowerDesc.includes('display') || lowerDesc.includes('view') || lowerDesc.includes('\u753B\u9762'))) {
    methods.push(
      {
        name: 'render',
        params: 'data: RenderData',
        returnType: 'string',
        description: 'Render component',
        async: false,
      },
      {
        name: 'update',
        params: 'props: Props',
        returnType: 'void',
        description: 'Update component with new props',
        async: false,
      }
    );
    return methods;
  }

  // Default method if no patterns matched
  methods.push({
    name: 'execute',
    params: '',
    returnType: 'Promise<void>',
    description: 'Execute main operation',
    async: true,
  });

  return methods;
}

/**
 * Generate domain-specific method implementation
 */
export function generateMethodImplementation(method: MethodSignature, _baseName: string): string {
  const params = method.parameters.map(p => `${p.name}: ${p.type}`).join(', ');
  const asyncKeyword = method.async !== false ? 'async ' : '';
  // returnType already includes Promise<T> from MethodSignature, don't wrap again
  const returnType = method.returnType;

  return `
  /**
   * ${method.description}
   */
  ${asyncKeyword}${method.name}(${params}): ${returnType} {
    // TODO: Implement ${method.name}
    throw new Error('${method.name} not implemented');
  }`;
}

/**
 * Generate domain-specific interface methods
 */
export function generateInterfaceMethods(methods: MethodSignature[]): string {
  return methods.map(method => {
    const params = method.parameters.map(p => `${p.name}: ${p.type}`).join(', ');
    // returnType already includes Promise<T> from MethodSignature
    return `  ${method.name}(${params}): ${method.returnType};`;
  }).join('\n');
}
