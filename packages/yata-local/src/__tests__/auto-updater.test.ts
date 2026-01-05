/**
 * Knowledge Graph Auto Updater Tests
 *
 * @see REQ-YATA-AUTO-001
 */

import { describe, it, expect } from 'vitest';
import {
  KnowledgeGraphUpdater,
  createKnowledgeGraphUpdater,
} from '../auto-updater.js';

describe('KnowledgeGraphUpdater', () => {
  describe('analyzeCode', () => {
    it('should extract class declarations', () => {
      const updater = createKnowledgeGraphUpdater();
      const code = `
export class UserService {
  private users: Map<string, User> = new Map();

  async getUser(id: string): Promise<User | null> {
    return this.users.get(id) ?? null;
  }
}
`;
      const result = updater.analyzeCode(code, 'src/services/user.ts');

      expect(result.errors).toHaveLength(0);
      expect(result.entities).toContainEqual(
        expect.objectContaining({
          type: 'class',
          name: 'UserService',
          namespace: 'services.user',
        })
      );
    });

    it('should extract interface declarations', () => {
      const updater = createKnowledgeGraphUpdater();
      const code = `
export interface User {
  id: string;
  name: string;
  email: string;
}
`;
      const result = updater.analyzeCode(code, 'src/types/user.ts');

      expect(result.entities).toContainEqual(
        expect.objectContaining({
          type: 'interface',
          name: 'User',
        })
      );
    });

    it('should extract function declarations', () => {
      const updater = createKnowledgeGraphUpdater();
      const code = `
export function createUser(name: string): User {
  return { id: generateId(), name };
}

export async function deleteUser(id: string): Promise<void> {
  await userRepository.delete(id);
}
`;
      const result = updater.analyzeCode(code, 'src/utils/user-utils.ts');

      expect(result.entities.filter(e => e.type === 'function')).toHaveLength(2);
      expect(result.entities).toContainEqual(
        expect.objectContaining({
          type: 'function',
          name: 'createUser',
        })
      );
    });

    it('should extract type aliases', () => {
      const updater = createKnowledgeGraphUpdater();
      const code = `
export type UserId = string;
export type UserRole = 'admin' | 'user' | 'guest';
`;
      const result = updater.analyzeCode(code, 'src/types/index.ts');

      expect(result.entities.filter(e => e.type === 'type')).toHaveLength(2);
    });

    it('should extract enum declarations', () => {
      const updater = createKnowledgeGraphUpdater();
      const code = `
export enum Status {
  Active,
  Inactive,
  Pending,
}
`;
      const result = updater.analyzeCode(code, 'src/enums.ts');

      expect(result.entities).toContainEqual(
        expect.objectContaining({
          type: 'enum',
          name: 'Status',
        })
      );
    });

    it('should extract extends relationships', () => {
      const updater = createKnowledgeGraphUpdater();
      const code = `
class BaseService {
  protected logger: Logger;
}

export class UserService extends BaseService {
  private users: Map<string, User>;
}
`;
      const result = updater.analyzeCode(code, 'src/services/user.ts');

      expect(result.relationships).toContainEqual(
        expect.objectContaining({
          sourceName: 'UserService',
          targetName: 'BaseService',
          type: 'extends',
        })
      );
    });

    it('should extract implements relationships', () => {
      const updater = createKnowledgeGraphUpdater();
      const code = `
interface Repository<T> {
  find(id: string): T | null;
}

export class UserRepository implements Repository<User> {
  find(id: string): User | null {
    return null;
  }
}
`;
      const result = updater.analyzeCode(code, 'src/repositories/user.ts');

      expect(result.relationships).toContainEqual(
        expect.objectContaining({
          sourceName: 'UserRepository',
          targetName: 'Repository',
          type: 'implements',
        })
      );
    });

    it('should extract class methods', () => {
      const updater = createKnowledgeGraphUpdater();
      const code = `
export class Calculator {
  add(a: number, b: number): number {
    return a + b;
  }

  subtract(a: number, b: number): number {
    return a - b;
  }

  private validate(n: number): boolean {
    return !isNaN(n);
  }
}
`;
      const result = updater.analyzeCode(code, 'src/calculator.ts');

      const methods = result.entities.filter(e => e.type === 'method');
      expect(methods.length).toBeGreaterThanOrEqual(3);
      expect(methods).toContainEqual(
        expect.objectContaining({
          type: 'method',
          name: 'add',
        })
      );
    });

    it('should extract import relationships', () => {
      const updater = createKnowledgeGraphUpdater();
      const code = `
import { User } from './types/user.js';
import { Repository } from '../common/repository.js';
import * as utils from './utils/index.js';

export class UserService {
  constructor(private repo: Repository<User>) {}
}
`;
      const result = updater.analyzeCode(code, 'src/services/user.ts');

      expect(result.relationships.filter(r => r.type === 'imports').length).toBeGreaterThanOrEqual(1);
    });

    it('should handle abstract classes', () => {
      const updater = createKnowledgeGraphUpdater();
      const code = `
export abstract class BaseEntity {
  abstract getId(): string;
}
`;
      const result = updater.analyzeCode(code, 'src/entities/base.ts');

      expect(result.entities).toContainEqual(
        expect.objectContaining({
          type: 'class',
          name: 'BaseEntity',
          metadata: expect.objectContaining({
            modifiers: ['abstract'],
          }),
        })
      );
    });

    it('should extract namespace from file path', () => {
      const updater = createKnowledgeGraphUpdater();
      const code = `export class Test {}`;

      const result1 = updater.analyzeCode(code, 'src/services/user/index.ts');
      expect(result1.entities[0].namespace).toBe('services.user.index');

      const result2 = updater.analyzeCode(code, 'lib/core/utils.ts');
      expect(result2.entities[0].namespace).toBe('core.utils');
    });

    it('should handle complex file with multiple declarations', () => {
      const updater = createKnowledgeGraphUpdater();
      const code = `
import { Logger } from './logger.js';

export interface IUserService {
  getUser(id: string): User | null;
}

export type UserRole = 'admin' | 'user';

export class UserService implements IUserService {
  private logger: Logger;

  constructor(logger: Logger) {
    this.logger = logger;
  }

  getUser(id: string): User | null {
    this.logger.info('Getting user', id);
    return null;
  }

  async createUser(data: CreateUserDTO): Promise<User> {
    this.logger.info('Creating user');
    return {} as User;
  }
}

export function createUserService(logger: Logger): UserService {
  return new UserService(logger);
}
`;
      const result = updater.analyzeCode(code, 'src/services/user.ts');

      expect(result.errors).toHaveLength(0);
      expect(result.entities.filter(e => e.type === 'interface')).toHaveLength(1);
      expect(result.entities.filter(e => e.type === 'type')).toHaveLength(1);
      expect(result.entities.filter(e => e.type === 'class')).toHaveLength(1);
      expect(result.entities.filter(e => e.type === 'function')).toHaveLength(1);
      expect(result.relationships.some(r => r.type === 'implements')).toBe(true);
    });
  });

  describe('factory function', () => {
    it('should create updater instance', () => {
      const updater = createKnowledgeGraphUpdater();
      expect(updater).toBeInstanceOf(KnowledgeGraphUpdater);
    });
  });
});
