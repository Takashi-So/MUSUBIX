/**
 * Sensitive Data Filter Implementation
 *
 * REQ-INT-004: SensitiveDataFilter - 機密情報のフィルタリング
 *
 * @packageDocumentation
 */

import {
  DEFAULT_FILTER_CONFIG,
  DEFAULT_SENSITIVE_PATTERNS,
  type FilterConfig,
  type FilterResult,
  type FilterStats,
  type SensitiveDataDetection,
  type SensitiveDataFilter,
  type SensitiveDataPattern,
  type SensitiveDataType,
} from './types.js';

/**
 * 重要度の優先順位
 */
const SEVERITY_PRIORITY: Record<'high' | 'medium' | 'low', number> = {
  high: 3,
  medium: 2,
  low: 1,
};

/**
 * 重要度が閾値以上かチェック
 */
function isSeverityAboveThreshold(
  severity: 'high' | 'medium' | 'low',
  minSeverity: 'high' | 'medium' | 'low'
): boolean {
  return SEVERITY_PRIORITY[severity] >= SEVERITY_PRIORITY[minSeverity];
}

/**
 * テキストから機密データを検出
 */
function detectSensitiveData(
  text: string,
  patterns: readonly SensitiveDataPattern[],
  config: FilterConfig
): SensitiveDataDetection[] {
  const detections: SensitiveDataDetection[] = [];

  for (const patternDef of patterns) {
    // 有効なタイプかチェック
    if (!config.enabledTypes.includes(patternDef.type)) {
      continue;
    }

    // 重要度チェック
    if (!isSeverityAboveThreshold(patternDef.severity, config.minSeverity)) {
      continue;
    }

    // パターンのフラグをリセット（グローバルマッチの場合）
    const pattern = new RegExp(patternDef.pattern.source, patternDef.pattern.flags);

    let match: RegExpExecArray | null;
    while ((match = pattern.exec(text)) !== null) {
      detections.push({
        type: patternDef.type,
        startIndex: match.index,
        endIndex: match.index + match[0].length,
        masked: patternDef.replacement,
        severity: patternDef.severity,
        description: patternDef.description,
      });

      // 無限ループ防止
      if (!pattern.global) break;
    }
  }

  // 位置でソート
  return detections.sort((a, b) => a.startIndex - b.startIndex);
}

/**
 * 検出結果を統合（重複を除去）
 */
function mergeDetections(
  detections: SensitiveDataDetection[]
): SensitiveDataDetection[] {
  if (detections.length <= 1) return detections;

  const merged: SensitiveDataDetection[] = [];
  let current = detections[0];

  for (let i = 1; i < detections.length; i++) {
    const next = detections[i];

    // 重複チェック（範囲が重なっている場合）
    if (next.startIndex < current.endIndex) {
      // より高い重要度を優先
      if (
        SEVERITY_PRIORITY[next.severity] > SEVERITY_PRIORITY[current.severity]
      ) {
        current = next;
      } else if (next.endIndex > current.endIndex) {
        // より長いマッチを採用
        current = {
          ...current,
          endIndex: next.endIndex,
        };
      }
    } else {
      merged.push(current);
      current = next;
    }
  }
  merged.push(current);

  return merged;
}

/**
 * テキストをフィルタリング
 */
function filterText(
  text: string,
  detections: SensitiveDataDetection[]
): string {
  if (detections.length === 0) return text;

  const parts: string[] = [];
  let lastIndex = 0;

  for (const detection of detections) {
    // マッチ前の部分を追加
    if (detection.startIndex > lastIndex) {
      parts.push(text.slice(lastIndex, detection.startIndex));
    }
    // マスクされた値を追加
    parts.push(detection.masked);
    lastIndex = detection.endIndex;
  }

  // 残りの部分を追加
  if (lastIndex < text.length) {
    parts.push(text.slice(lastIndex));
  }

  return parts.join('');
}

/**
 * フィルタリング統計を生成
 */
function generateStats(
  detections: SensitiveDataDetection[],
  processingTimeMs: number
): FilterStats {
  const byType: Record<SensitiveDataType, number> = {} as Record<SensitiveDataType, number>;
  const bySeverity: Record<'high' | 'medium' | 'low', number> = {
    high: 0,
    medium: 0,
    low: 0,
  };

  for (const detection of detections) {
    byType[detection.type] = (byType[detection.type] ?? 0) + 1;
    bySeverity[detection.severity]++;
  }

  return {
    totalDetections: detections.length,
    byType,
    bySeverity,
    processingTimeMs,
  };
}

/**
 * SensitiveDataFilter を作成
 *
 * REQ-INT-004: 機密情報のフィルタリング
 */
export function createSensitiveDataFilter(
  config: Partial<FilterConfig> = {}
): SensitiveDataFilter {
  const mergedConfig: FilterConfig = {
    ...DEFAULT_FILTER_CONFIG,
    ...config,
    enabledTypes: config.enabledTypes ?? DEFAULT_FILTER_CONFIG.enabledTypes,
    customPatterns: config.customPatterns ?? DEFAULT_FILTER_CONFIG.customPatterns,
  };

  const patterns: SensitiveDataPattern[] = [
    ...DEFAULT_SENSITIVE_PATTERNS,
    ...mergedConfig.customPatterns,
  ];

  return {
    filter(text: string): FilterResult {
      const startTime = performance.now();

      const rawDetections = detectSensitiveData(text, patterns, mergedConfig);
      const detections = mergeDetections(rawDetections);
      const filtered = filterText(text, detections);

      const processingTimeMs = performance.now() - startTime;

      return {
        filtered,
        detections,
        wasModified: detections.length > 0,
        stats: generateStats(detections, processingTimeMs),
      };
    },

    containsSensitiveData(text: string): boolean {
      const detections = detectSensitiveData(text, patterns, mergedConfig);
      return detections.length > 0;
    },

    detect(text: string): SensitiveDataDetection[] {
      const rawDetections = detectSensitiveData(text, patterns, mergedConfig);
      return mergeDetections(rawDetections);
    },

    getConfig(): FilterConfig {
      return { ...mergedConfig };
    },

    addPattern(pattern: SensitiveDataPattern): void {
      patterns.push(pattern);
    },

    getPatterns(): readonly SensitiveDataPattern[] {
      return [...patterns];
    },
  };
}

/**
 * デフォルトのフィルターインスタンス
 */
let defaultFilter: SensitiveDataFilter | null = null;

/**
 * デフォルトフィルターを取得
 */
export function getDefaultFilter(): SensitiveDataFilter {
  if (!defaultFilter) {
    defaultFilter = createSensitiveDataFilter();
  }
  return defaultFilter;
}

/**
 * テキストをフィルタリング（ユーティリティ関数）
 */
export function filterSensitiveData(text: string): FilterResult {
  return getDefaultFilter().filter(text);
}

/**
 * 機密データが含まれるかチェック（ユーティリティ関数）
 */
export function containsSensitiveData(text: string): boolean {
  return getDefaultFilter().containsSensitiveData(text);
}

/**
 * フィルター結果をMarkdown形式でフォーマット
 */
export function formatFilterResultAsMarkdown(result: FilterResult): string {
  if (!result.wasModified) {
    return '✅ 機密データは検出されませんでした';
  }

  const lines: string[] = [
    '⚠️ **機密データが検出されました**',
    '',
    `**検出数**: ${result.stats.totalDetections}`,
    `**処理時間**: ${result.stats.processingTimeMs.toFixed(2)}ms`,
    '',
    '## 検出された機密データ',
    '',
    '| 種類 | 重要度 | 説明 |',
    '|------|--------|------|',
  ];

  for (const detection of result.detections) {
    lines.push(
      `| ${detection.type} | ${detection.severity} | ${detection.description} |`
    );
  }

  if (Object.keys(result.stats.byType).length > 0) {
    lines.push('', '## 種類別集計', '');
    for (const [type, count] of Object.entries(result.stats.byType)) {
      if (count > 0) {
        lines.push(`- **${type}**: ${count}件`);
      }
    }
  }

  return lines.join('\n');
}
