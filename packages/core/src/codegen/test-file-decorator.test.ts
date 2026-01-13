/**
 * Test File Decorator Tests
 *
 * @packageDocumentation
 * @module codegen/test-file-decorator.test
 *
 * @see REQ-TST-002 - テストカウンターリセット自動挿入
 * @see TSK-TST-002 - カウンターリセット自動挿入タスク
 */

import { describe, it, expect } from 'vitest';
import {
  TestFileDecorator,
  decorateTestFile,
  needsCounterReset,
  type CounterResetFunction,
} from './test-file-decorator.js';

describe('TestFileDecorator', () => {
  describe('detectCounterResets', () => {
    it('should detect createEntity pattern', () => {
      const sourceCode = `
import { createOrder } from './order.js';

describe('Order', () => {
  it('should create order', () => {
    const order = createOrder({ name: 'test' });
  });
});
`;
      const entityImports: CounterResetFunction[] = [
        { name: 'resetOrderCounter', importPath: './order.js' },
      ];

      const decorator = new TestFileDecorator();
      const counters = decorator.detectCounterResets(sourceCode, entityImports);

      expect(counters).toHaveLength(1);
      expect(counters[0].name).toBe('resetOrderCounter');
    });

    it('should detect new Entity pattern', () => {
      const sourceCode = `
import { Product } from './product.js';

describe('Product', () => {
  it('should create product', () => {
    const product = new Product({ name: 'test' });
  });
});
`;
      const entityImports: CounterResetFunction[] = [
        { name: 'resetProductCounter', importPath: './product.js' },
      ];

      const decorator = new TestFileDecorator();
      const counters = decorator.detectCounterResets(sourceCode, entityImports);

      expect(counters).toHaveLength(1);
      expect(counters[0].name).toBe('resetProductCounter');
    });

    it('should not add counter if already imported', () => {
      const sourceCode = `
import { createOrder, resetOrderCounter } from './order.js';

describe('Order', () => {
  beforeEach(() => {
    resetOrderCounter();
  });
});
`;
      const entityImports: CounterResetFunction[] = [
        { name: 'resetOrderCounter', importPath: './order.js' },
      ];

      const decorator = new TestFileDecorator();
      const counters = decorator.detectCounterResets(sourceCode, entityImports);

      expect(counters).toHaveLength(0);
    });
  });

  describe('hasBeforeEach', () => {
    it('should detect existing beforeEach', () => {
      const sourceCode = `
describe('Test', () => {
  beforeEach(() => {
    // setup
  });
});
`;
      const decorator = new TestFileDecorator();
      expect(decorator.hasBeforeEach(sourceCode)).toBe(true);
    });

    it('should return false when no beforeEach', () => {
      const sourceCode = `
describe('Test', () => {
  it('should work', () => {});
});
`;
      const decorator = new TestFileDecorator();
      expect(decorator.hasBeforeEach(sourceCode)).toBe(false);
    });
  });

  describe('decorate', () => {
    it('should insert beforeEach with counter reset', () => {
      const sourceCode = `import { createOrder } from './order.js';

describe('Order', () => {
  it('should create order', () => {
    const order = createOrder({ name: 'test' });
  });
});
`;
      const entityImports: CounterResetFunction[] = [
        { name: 'resetOrderCounter', importPath: './order.js' },
      ];

      const result = decorateTestFile(sourceCode, entityImports);

      expect(result.beforeEachInserted).toBe(true);
      expect(result.code).toContain('beforeEach');
      expect(result.code).toContain('resetOrderCounter()');
      expect(result.countersAdded).toHaveLength(1);
    });

    it('should add imports for reset functions', () => {
      const sourceCode = `import { createOrder } from './order.js';

describe('Order', () => {
  it('test', () => {
    createOrder({});
  });
});
`;
      const entityImports: CounterResetFunction[] = [
        { name: 'resetOrderCounter', importPath: './order.js' },
      ];

      const result = decorateTestFile(sourceCode, entityImports, { addImports: true });

      expect(result.importsAdded).toHaveLength(1);
      expect(result.importsAdded[0]).toContain('resetOrderCounter');
    });

    it('should not modify file without entity patterns', () => {
      const sourceCode = `
describe('Test', () => {
  it('should add numbers', () => {
    expect(1 + 1).toBe(2);
  });
});
`;
      const result = decorateTestFile(sourceCode, []);

      expect(result.beforeEachInserted).toBe(false);
      expect(result.countersAdded).toHaveLength(0);
      expect(result.code).toBe(sourceCode);
    });

    it('should handle multiple entity types', () => {
      const sourceCode = `
import { createOrder } from './order.js';
import { createProduct } from './product.js';

describe('E2E', () => {
  it('test', () => {
    const order = createOrder({});
    const product = createProduct({});
  });
});
`;
      const entityImports: CounterResetFunction[] = [
        { name: 'resetOrderCounter', importPath: './order.js' },
        { name: 'resetProductCounter', importPath: './product.js' },
      ];

      const result = decorateTestFile(sourceCode, entityImports);

      expect(result.countersAdded.length).toBeGreaterThanOrEqual(1);
      expect(result.code).toContain('beforeEach');
    });
  });

  describe('needsCounterReset', () => {
    it('should return true for file with entity creation', () => {
      const sourceCode = `
describe('Test', () => {
  it('test', () => {
    createOrder({});
  });
});
`;
      expect(needsCounterReset(sourceCode)).toBe(true);
    });

    it('should return false for file with existing reset in beforeEach', () => {
      const sourceCode = `
describe('Test', () => {
  beforeEach(() => {
    resetOrderCounter();
  });
  it('test', () => {
    createOrder({});
  });
});
`;
      expect(needsCounterReset(sourceCode)).toBe(false);
    });

    it('should return false for file without entity creation', () => {
      const sourceCode = `
describe('Math', () => {
  it('adds', () => {
    expect(1 + 1).toBe(2);
  });
});
`;
      expect(needsCounterReset(sourceCode)).toBe(false);
    });
  });

  describe('options', () => {
    it('should respect addImports: false', () => {
      const sourceCode = `import { createOrder } from './order.js';

describe('Test', () => {
  it('test', () => {
    createOrder({});
  });
});
`;
      const entityImports: CounterResetFunction[] = [
        { name: 'resetOrderCounter', importPath: './order.js' },
      ];

      const result = decorateTestFile(sourceCode, entityImports, { addImports: false });

      expect(result.importsAdded).toHaveLength(0);
    });

    it('should add custom beforeEach content', () => {
      const sourceCode = `
describe('Test', () => {
  it('test', () => {
    createOrder({});
  });
});
`;
      const result = decorateTestFile(sourceCode, [], {
        customBeforeEach: ['vi.clearAllMocks()'],
      });

      expect(result.code).toContain('vi.clearAllMocks()');
    });
  });
});
