/**
 * MockGenerator - テストモック自動生成モジュール
 * 
 * @description インターフェース定義からテストモック実装を自動生成
 * @requirement REQ-MUSUBIX-LEARN-001 (SDD Workflow Feedback)
 * @version 1.1.3
 * 
 * 学習フィードバック PAT-004 の改善:
 * - インターフェース定義からモック実装を自動生成
 * - Repository, Service, Adapter パターンに対応
 * - テスト失敗の80%削減を目標
 */

export interface MockMethodDefinition {
  name: string;
  parameters: { name: string; type: string }[];
  returnType: string;
  async: boolean;
}

export interface MockInterfaceDefinition {
  name: string;
  methods: MockMethodDefinition[];
  genericType?: string;
}

export interface MockGeneratorOptions {
  /** 生成するテストフレームワーク */
  framework: 'vitest' | 'jest';
  /** Map/Setベースのインメモリストレージを使用 */
  useInMemoryStorage: boolean;
  /** IDフィールド名 */
  idField: string;
}

export interface GeneratedMock {
  interfaceName: string;
  mockName: string;
  code: string;
  imports: string[];
}

const DEFAULT_OPTIONS: MockGeneratorOptions = {
  framework: 'vitest',
  useInMemoryStorage: true,
  idField: 'id',
};

/**
 * MockGenerator - インターフェースからテストモックを自動生成
 */
export class MockGenerator {
  private options: MockGeneratorOptions;

  constructor(options: Partial<MockGeneratorOptions> = {}) {
    this.options = { ...DEFAULT_OPTIONS, ...options };
  }

  /**
   * Repository インターフェースからモック実装を生成
   */
  generateRepositoryMock(
    interfaceDef: MockInterfaceDefinition,
    entityType: string
  ): GeneratedMock {
    const mockFn = this.options.framework === 'vitest' ? 'vi.fn' : 'jest.fn';
    const mockName = `createMock${interfaceDef.name.replace(/^I/, '')}`;
    
    const imports = this.options.framework === 'vitest' 
      ? ["import { vi } from 'vitest';"]
      : ["import { jest } from '@jest/globals';"];

    const code = `
function ${mockName}(): ${interfaceDef.name} {
  const storage = new Map<string, ${entityType}>();

  return {
    save: ${mockFn}(async (entity: ${entityType}) => {
      storage.set(entity.${this.options.idField}, { ...entity });
      return entity;
    }),
    saveMany: ${mockFn}(async (entities: ${entityType}[]) => {
      entities.forEach((e) => storage.set(e.${this.options.idField}, { ...e }));
      return entities;
    }),
    findById: ${mockFn}(async (id: string) => {
      const entity = storage.get(id);
      return entity ? { ...entity } : null;
    }),
    findAll: ${mockFn}(async () => {
      return Array.from(storage.values());
    }),
    update: ${mockFn}(async (id: string, data: Partial<${entityType}>) => {
      const entity = storage.get(id);
      if (!entity) throw new Error('Entity not found');
      const updated = { ...entity, ...data };
      storage.set(id, updated);
      return updated;
    }),
    updateMany: ${mockFn}(async (ids: string[], data: Partial<${entityType}>) => {
      return ids.map((id) => {
        const entity = storage.get(id);
        if (!entity) throw new Error('Entity not found');
        const updated = { ...entity, ...data };
        storage.set(id, updated);
        return updated;
      });
    }),
    delete: ${mockFn}(async (id: string) => {
      return storage.delete(id);
    }),
  };
}`.trim();

    return {
      interfaceName: interfaceDef.name,
      mockName,
      code,
      imports,
    };
  }

  /**
   * Service インターフェースからモック実装を生成
   */
  generateServiceMock(interfaceDef: MockInterfaceDefinition): GeneratedMock {
    const mockFn = this.options.framework === 'vitest' ? 'vi.fn' : 'jest.fn';
    const mockName = `createMock${interfaceDef.name.replace(/^I/, '')}`;
    
    const imports = this.options.framework === 'vitest' 
      ? ["import { vi } from 'vitest';"]
      : ["import { jest } from '@jest/globals';"];

    const methodMocks = interfaceDef.methods.map((method) => {
      const defaultReturn = this.getDefaultReturnValue(method.returnType);
      return `    ${method.name}: ${mockFn}(async (${method.parameters.map(p => `${p.name}: ${p.type}`).join(', ')}) => ${defaultReturn}),`;
    }).join('\n');

    const code = `
function ${mockName}(): ${interfaceDef.name} {
  return {
${methodMocks}
  };
}`.trim();

    return {
      interfaceName: interfaceDef.name,
      mockName,
      code,
      imports,
    };
  }

  /**
   * Adapter インターフェースからモック実装を生成
   */
  generateAdapterMock(
    interfaceDef: MockInterfaceDefinition,
    _testData?: Record<string, unknown[]>
  ): GeneratedMock {
    const mockFn = this.options.framework === 'vitest' ? 'vi.fn' : 'jest.fn';
    const mockName = `createMock${interfaceDef.name.replace(/^I/, '')}`;
    
    const imports = this.options.framework === 'vitest' 
      ? ["import { vi } from 'vitest';"]
      : ["import { jest } from '@jest/globals';"];

    const methodMocks = interfaceDef.methods.map((method) => {
      const defaultReturn = this.getDefaultReturnValue(method.returnType);
      return `    ${method.name}: ${mockFn}(async () => ${defaultReturn}),`;
    }).join('\n');

    const code = `
function ${mockName}(): ${interfaceDef.name} {
  return {
${methodMocks}
  };
}`.trim();

    return {
      interfaceName: interfaceDef.name,
      mockName,
      code,
      imports,
    };
  }

  /**
   * 任意のインターフェースからモック実装を生成（汎用）
   */
  generateMock(interfaceDef: MockInterfaceDefinition): GeneratedMock {
    // インターフェース名からパターンを推論
    const name = interfaceDef.name;
    
    if (name.includes('Repository')) {
      // Entity型を推論（例: IUserRepository → User）
      const entityType = name.replace(/^I/, '').replace(/Repository$/, '');
      return this.generateRepositoryMock(interfaceDef, entityType);
    }
    
    if (name.includes('Service')) {
      return this.generateServiceMock(interfaceDef);
    }
    
    if (name.includes('Adapter')) {
      return this.generateAdapterMock(interfaceDef);
    }
    
    // デフォルトはServiceパターン
    return this.generateServiceMock(interfaceDef);
  }

  /**
   * TypeScriptインターフェース定義文字列を解析
   */
  parseInterface(interfaceCode: string): MockInterfaceDefinition | null {
    // インターフェース名を抽出
    const nameMatch = interfaceCode.match(/interface\s+(\w+)/);
    if (!nameMatch) return null;

    const name = nameMatch[1];
    const methods: MockMethodDefinition[] = [];

    // メソッドシグネチャを抽出
    const methodRegex = /(\w+)\s*\(([^)]*)\)\s*:\s*Promise<([^>]+)>/g;
    let match;

    while ((match = methodRegex.exec(interfaceCode)) !== null) {
      const [, methodName, paramsStr, returnType] = match;
      
      const parameters = paramsStr
        .split(',')
        .filter(p => p.trim())
        .map(p => {
          const parts = p.trim().split(':').map(s => s.trim());
          return { name: parts[0], type: parts[1] || 'unknown' };
        });

      methods.push({
        name: methodName,
        parameters,
        returnType: `Promise<${returnType}>`,
        async: true,
      });
    }

    return { name, methods };
  }

  /**
   * 戻り値型からデフォルト値を生成
   */
  private getDefaultReturnValue(returnType: string): string {
    const innerType = returnType.replace(/Promise<(.+)>/, '$1').trim();
    
    if (innerType === 'void') return 'undefined';
    if (innerType === 'boolean') return 'true';
    if (innerType === 'number') return '0';
    if (innerType === 'string') return "''";
    if (innerType.endsWith('[]')) return '[]';
    if (innerType.includes('|') && innerType.includes('null')) return 'null';
    
    return '{}';
  }
}

/**
 * デフォルトのMockGeneratorインスタンスを作成
 */
export function createMockGenerator(
  options?: Partial<MockGeneratorOptions>
): MockGenerator {
  return new MockGenerator(options);
}

/**
 * シングルトンインスタンス
 */
export const mockGenerator = new MockGenerator();
