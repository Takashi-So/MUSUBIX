/**
 * @nahisaho/musubix-expert-delegation
 * Test Helpers
 *
 * DES-TST-001
 * Traces to: REQ-TST-001
 */

import type {
  Expert,
  ExpertType,
  DelegationContext,
  DelegationTask,
  DelegationResult,
  TraceLink,
} from '../types/index.js';
import { MockVSCodeLMProvider } from './mocks.js';

/**
 * テスト用のエキスパートを作成
 */
export function createTestExpert(
  type: ExpertType,
  overrides?: Partial<Expert>
): Expert {
  return {
    type,
    name: `Test ${type}`,
    description: `Test expert for ${type}`,
    systemPrompt: `You are a test ${type} expert.`,
    triggers: [],
    capabilities: [{ name: 'advisory', mode: 'advisory', description: 'Advisory mode' }],
    ontologyClass: `test:${type}`,
    ...overrides,
  };
}

/**
 * テスト用のコンテキストを作成
 */
export function createTestContext(
  overrides?: Partial<DelegationContext>
): DelegationContext {
  return {
    userMessage: 'Test message',
    mode: 'advisory',
    ...overrides,
  };
}

/**
 * テスト用のタスクを作成
 */
export function createTestTask(
  overrides?: Partial<DelegationTask>
): DelegationTask {
  return {
    id: `test-task-${Date.now()}`,
    context: createTestContext(),
    mode: 'advisory',
    createdAt: new Date(),
    ...overrides,
  };
}

/**
 * テスト用のトレースリンクを作成
 */
export function createTestTraceLink(
  overrides?: Partial<TraceLink>
): TraceLink {
  return {
    sourceId: 'REQ-TEST-001',
    targetId: 'DES-TEST-001',
    type: 'traces-to',
    ...overrides,
  };
}

/**
 * テスト用の成功結果を作成
 */
export function createTestSuccessResult(
  expertType: ExpertType,
  content: string,
  overrides?: Partial<DelegationResult>
): DelegationResult {
  return {
    success: true,
    expertType,
    mode: 'advisory',
    content,
    confidence: 0.85,
    metadata: {},
    ...overrides,
  };
}

/**
 * テスト用の失敗結果を作成
 */
export function createTestFailureResult(
  expertType: ExpertType,
  reason: string,
  overrides?: Partial<DelegationResult>
): DelegationResult {
  return {
    success: false,
    expertType,
    mode: 'advisory',
    content: reason,
    confidence: 0,
    metadata: { error: reason },
    ...overrides,
  };
}

/**
 * テスト用プロバイダーをセットアップ
 */
export function setupTestProvider(
  responses?: Record<string, string>
): MockVSCodeLMProvider {
  const provider = new MockVSCodeLMProvider();

  if (responses) {
    for (const [pattern, content] of Object.entries(responses)) {
      provider.setResponse(pattern, { content, finishReason: 'stop' });
    }
  }

  return provider;
}

/**
 * 非同期アサーション用ヘルパー
 */
export async function expectAsync<T>(
  promise: Promise<T>,
  assertion: (result: T) => void
): Promise<void> {
  const result = await promise;
  assertion(result);
}

/**
 * エラーを期待するヘルパー
 */
export async function expectError(
  promise: Promise<unknown>,
  errorType?: new (...args: unknown[]) => Error
): Promise<Error> {
  try {
    await promise;
    throw new Error('Expected promise to reject');
  } catch (error) {
    if (errorType && !(error instanceof errorType)) {
      throw new Error(
        `Expected error of type ${errorType.name}, got ${(error as Error).constructor.name}`
      );
    }
    return error as Error;
  }
}

/**
 * 遅延ヘルパー
 */
export function delay(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

/**
 * 複数回実行ヘルパー
 */
export async function repeatAsync<T>(
  fn: () => Promise<T>,
  times: number
): Promise<T[]> {
  const results: T[] = [];
  for (let i = 0; i < times; i++) {
    results.push(await fn());
  }
  return results;
}
