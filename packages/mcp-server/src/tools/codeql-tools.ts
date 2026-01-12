/**
 * CodeQL MCP Tools
 *
 * Implements: TSK-CODEQL-004〜006, DES-CODEQL-004〜006, REQ-CODEQL-006
 * @see DES-DX-v3.1.0 Section CodeQL Module MCP Tools
 */

import type { Tool, CallToolResult, TextContent } from '@modelcontextprotocol/sdk/types.js';

/**
 * Tool: codeql_parse_sarif - Parse SARIF file
 */
export const codeqlParseSarifTool: Tool = {
  name: 'codeql_parse_sarif',
  description: 'Parse a CodeQL SARIF 2.1.0 report file and extract security findings with CWE mappings.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      filePath: {
        type: 'string',
        description: 'Path to the SARIF file',
      },
      basePath: {
        type: 'string',
        description: 'Base path for resolving relative file URIs',
      },
      minSeverity: {
        type: 'string',
        enum: ['critical', 'high', 'medium', 'low', 'info'],
        description: 'Minimum severity to include (default: all)',
      },
      includeRaw: {
        type: 'boolean',
        description: 'Include raw SARIF result data',
      },
    },
    required: ['filePath'],
  },
};

/**
 * Tool: codeql_aggregate - Aggregate multiple reports
 */
export const codeqlAggregateTool: Tool = {
  name: 'codeql_aggregate',
  description: 'Aggregate multiple CodeQL scan results into a unified report with statistics.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      filePaths: {
        type: 'array',
        items: { type: 'string' },
        description: 'Paths to SARIF files to aggregate',
      },
      format: {
        type: 'string',
        enum: ['json', 'markdown', 'summary'],
        description: 'Output format (default: summary)',
      },
    },
    required: ['filePaths'],
  },
};

/**
 * Tool: codeql_cwe_lookup - Look up CWE information
 */
export const codeqlCweLookupTool: Tool = {
  name: 'codeql_cwe_lookup',
  description: 'Look up CWE information including Japanese explanations and recommended fixes.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      cweId: {
        type: 'string',
        description: 'CWE ID (e.g., "CWE-79" or "79")',
      },
    },
    required: ['cweId'],
  },
};

/**
 * Tool: codeql_list_cwes - List CWE entries
 */
export const codeqlListCwesTool: Tool = {
  name: 'codeql_list_cwes',
  description: 'List all known CWE entries, optionally filtered by category or severity.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      category: {
        type: 'string',
        enum: ['injection', 'auth', 'crypto', 'file', 'secrets', 'memory', 'info-disclosure', 'config', 'validation', 'redirect'],
        description: 'Filter by category',
      },
      severity: {
        type: 'string',
        enum: ['critical', 'high', 'medium', 'low'],
        description: 'Filter by severity',
      },
    },
    required: [],
  },
};

/**
 * Tool: codeql_summary - Get finding summary
 */
export const codeqlSummaryTool: Tool = {
  name: 'codeql_summary',
  description: 'Get a summary of security findings from parsed SARIF data.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      filePath: {
        type: 'string',
        description: 'Path to SARIF file',
      },
      groupBy: {
        type: 'string',
        enum: ['severity', 'rule', 'file', 'cwe'],
        description: 'How to group the summary (default: severity)',
      },
    },
    required: ['filePath'],
  },
};

/**
 * Tool: codeql_fix_suggestions - Get fix suggestions
 */
export const codeqlFixSuggestionsTool: Tool = {
  name: 'codeql_fix_suggestions',
  description: 'Get fix suggestions for security findings based on CWE information.',
  inputSchema: {
    type: 'object' as const,
    properties: {
      ruleId: {
        type: 'string',
        description: 'CodeQL rule ID',
      },
      cweId: {
        type: 'string',
        description: 'CWE ID',
      },
      codeSnippet: {
        type: 'string',
        description: 'Code snippet with the vulnerability',
      },
    },
    required: [],
  },
};

/**
 * Handle codeql_parse_sarif
 */
export async function handleCodeQLParseSarif(args: {
  filePath: string;
  basePath?: string;
  minSeverity?: string;
  includeRaw?: boolean;
}): Promise<CallToolResult> {
  try {
    const { SARIFParser } = await import('@nahisaho/musubix-core');

    const parser = new SARIFParser({
      basePath: args.basePath,
      minSeverity: args.minSeverity as 'critical' | 'high' | 'medium' | 'low' | 'info',
      includeRaw: args.includeRaw,
      includeCWE: true,
      includeExplanations: true,
    });

    const result = await parser.parseFile(args.filePath);

    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: true,
            tool: result.tool,
            stats: result.stats,
            findings: result.findings.slice(0, 50), // Limit for MCP response
            message: result.findings.length > 50
              ? `Showing 50 of ${result.findings.length} findings`
              : `Found ${result.findings.length} findings`,
          }, null, 2),
        } as TextContent,
      ],
    };
  } catch (error) {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: false,
            error: error instanceof Error ? error.message : String(error),
          }),
        } as TextContent,
      ],
      isError: true,
    };
  }
}

/**
 * Handle codeql_aggregate
 */
export async function handleCodeQLAggregate(args: {
  filePaths: string[];
  format?: 'json' | 'markdown' | 'summary';
}): Promise<CallToolResult> {
  try {
    const { SARIFParser, ResultAggregator } = await import('@nahisaho/musubix-core');

    const parser = new SARIFParser({ includeCWE: true, includeExplanations: true });
    const aggregator = new ResultAggregator();

    const results = await Promise.all(
      args.filePaths.map((path) => parser.parseFile(path))
    );

    const merged = aggregator.mergeResults(results);
    const report = aggregator.aggregate(merged);

    const format = args.format ?? 'summary';

    if (format === 'markdown') {
      return {
        content: [{ type: 'text', text: aggregator.toMarkdown(report) } as TextContent],
      };
    }

    if (format === 'json') {
      return {
        content: [{ type: 'text', text: aggregator.toJSON(report) } as TextContent],
      };
    }

    // Summary format
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: true,
            summary: report.summary,
            topIssues: report.topIssues,
            criticalCount: report.critical.length,
          }, null, 2),
        } as TextContent,
      ],
    };
  } catch (error) {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: false,
            error: error instanceof Error ? error.message : String(error),
          }),
        } as TextContent,
      ],
      isError: true,
    };
  }
}

/**
 * Handle codeql_cwe_lookup
 */
export async function handleCodeQLCweLookup(args: {
  cweId: string;
}): Promise<CallToolResult> {
  try {
    const { mapCWE } = await import('@nahisaho/musubix-core');

    const cweInfo = mapCWE(args.cweId);

    if (!cweInfo) {
      return {
        content: [
          {
            type: 'text',
            text: JSON.stringify({
              success: false,
              error: `CWE ${args.cweId} not found in database`,
            }),
          } as TextContent,
        ],
      };
    }

    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: true,
            cwe: cweInfo,
          }, null, 2),
        } as TextContent,
      ],
    };
  } catch (error) {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: false,
            error: error instanceof Error ? error.message : String(error),
          }),
        } as TextContent,
      ],
      isError: true,
    };
  }
}

/**
 * Handle codeql_list_cwes
 */
export async function handleCodeQLListCwes(args: {
  category?: string;
  severity?: string;
}): Promise<CallToolResult> {
  try {
    const { getAllCWEs, getCWEsByCategory, getCWEsBySeverity } = await import('@nahisaho/musubix-core');

    let cwes = getAllCWEs();

    if (args.category) {
      cwes = getCWEsByCategory(args.category);
    }

    if (args.severity) {
      cwes = getCWEsBySeverity(args.severity as 'critical' | 'high' | 'medium' | 'low');
    }

    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: true,
            count: cwes.length,
            cwes: cwes.map((c) => ({
              id: c.id,
              name: c.name,
              nameJa: c.nameJa,
              severity: c.severity,
              category: c.category,
            })),
          }, null, 2),
        } as TextContent,
      ],
    };
  } catch (error) {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: false,
            error: error instanceof Error ? error.message : String(error),
          }),
        } as TextContent,
      ],
      isError: true,
    };
  }
}

/**
 * Handle codeql_summary
 */
export async function handleCodeQLSummary(args: {
  filePath: string;
  groupBy?: 'severity' | 'rule' | 'file' | 'cwe';
}): Promise<CallToolResult> {
  try {
    const { SARIFParser, ResultAggregator } = await import('@nahisaho/musubix-core');

    const parser = new SARIFParser({ includeCWE: true });
    const result = await parser.parseFile(args.filePath);

    const aggregator = new ResultAggregator({
      sortBy: args.groupBy === 'severity' ? 'severity' : args.groupBy === 'file' ? 'file' : 'rule',
    });

    const report = aggregator.aggregate(result);

    const groupBy = args.groupBy ?? 'severity';
    let grouped: Record<string, number> = {};

    if (groupBy === 'severity') {
      grouped = report.summary.bySeverity;
    } else if (groupBy === 'cwe') {
      grouped = report.summary.byCategory;
    } else if (groupBy === 'rule') {
      for (const [rule, findings] of report.byRule) {
        grouped[rule] = findings.length;
      }
    } else if (groupBy === 'file') {
      for (const [file, findings] of report.byFile) {
        grouped[file] = findings.length;
      }
    }

    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: true,
            groupBy,
            summary: report.summary,
            grouped,
            topIssues: report.topIssues.slice(0, 5),
          }, null, 2),
        } as TextContent,
      ],
    };
  } catch (error) {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: false,
            error: error instanceof Error ? error.message : String(error),
          }),
        } as TextContent,
      ],
      isError: true,
    };
  }
}

/**
 * Handle codeql_fix_suggestions
 */
export async function handleCodeQLFixSuggestions(args: {
  ruleId?: string;
  cweId?: string;
  codeSnippet?: string;
}): Promise<CallToolResult> {
  try {
    const { mapCWE } = await import('@nahisaho/musubix-core');

    const suggestions: string[] = [];
    let cweInfo = null;

    if (args.cweId) {
      cweInfo = mapCWE(args.cweId);
      if (cweInfo) {
        suggestions.push(`## ${cweInfo.nameJa} (${cweInfo.id})`);
        suggestions.push('');
        suggestions.push('### 説明');
        suggestions.push(cweInfo.explanation);
        suggestions.push('');
        suggestions.push('### 推奨される対策');
        
        // Add specific recommendations based on category
        switch (cweInfo.category) {
          case 'injection':
            suggestions.push('- 入力値の検証とサニタイズを実装する');
            suggestions.push('- パラメータ化クエリ（プリペアドステートメント）を使用する');
            suggestions.push('- 出力時のエスケープ処理を適用する');
            suggestions.push('- ホワイトリスト方式の入力検証を採用する');
            break;
          case 'auth':
            suggestions.push('- 標準的な認証フレームワークを使用する');
            suggestions.push('- 多要素認証（MFA）の導入を検討する');
            suggestions.push('- セッション管理を強化する');
            suggestions.push('- 最小権限の原則を適用する');
            break;
          case 'crypto':
            suggestions.push('- 最新の暗号アルゴリズムを使用する（AES-256、SHA-256以上）');
            suggestions.push('- 適切な鍵管理を実装する');
            suggestions.push('- TLS 1.2以上を使用する');
            suggestions.push('- 暗号化ライブラリは定期的に更新する');
            break;
          case 'secrets':
            suggestions.push('- 環境変数または秘密管理サービスを使用する');
            suggestions.push('- ハードコードされた認証情報を削除する');
            suggestions.push('- 認証情報のローテーションを実装する');
            suggestions.push('- .gitignoreで機密ファイルを除外する');
            break;
          default:
            suggestions.push('- セキュリティベストプラクティスに従う');
            suggestions.push('- コードレビューでセキュリティを確認する');
            suggestions.push('- 定期的なセキュリティテストを実施する');
        }
      }
    }

    if (!cweInfo && args.ruleId) {
      suggestions.push(`## Rule: ${args.ruleId}`);
      suggestions.push('');
      suggestions.push('CWE IDを指定するとより詳細な修正提案を取得できます。');
    }

    return {
      content: [
        {
          type: 'text',
          text: suggestions.length > 0
            ? suggestions.join('\n')
            : JSON.stringify({
                success: false,
                error: 'Please provide either cweId or ruleId',
              }),
        } as TextContent,
      ],
    };
  } catch (error) {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            success: false,
            error: error instanceof Error ? error.message : String(error),
          }),
        } as TextContent,
      ],
      isError: true,
    };
  }
}

/**
 * All CodeQL tools
 */
export const codeqlTools: Tool[] = [
  codeqlParseSarifTool,
  codeqlAggregateTool,
  codeqlCweLookupTool,
  codeqlListCwesTool,
  codeqlSummaryTool,
  codeqlFixSuggestionsTool,
];

/**
 * Get CodeQL tools
 */
export function getCodeQLTools(): Tool[] {
  return codeqlTools;
}

/**
 * Handle CodeQL tool calls
 */
export async function handleCodeQLTool(
  name: string,
  args: Record<string, unknown>
): Promise<CallToolResult> {
  switch (name) {
    case 'codeql_parse_sarif':
      return handleCodeQLParseSarif(args as Parameters<typeof handleCodeQLParseSarif>[0]);
    case 'codeql_aggregate':
      return handleCodeQLAggregate(args as Parameters<typeof handleCodeQLAggregate>[0]);
    case 'codeql_cwe_lookup':
      return handleCodeQLCweLookup(args as Parameters<typeof handleCodeQLCweLookup>[0]);
    case 'codeql_list_cwes':
      return handleCodeQLListCwes(args as Parameters<typeof handleCodeQLListCwes>[0]);
    case 'codeql_summary':
      return handleCodeQLSummary(args as Parameters<typeof handleCodeQLSummary>[0]);
    case 'codeql_fix_suggestions':
      return handleCodeQLFixSuggestions(args as Parameters<typeof handleCodeQLFixSuggestions>[0]);
    default:
      return {
        content: [{ type: 'text', text: `Unknown CodeQL tool: ${name}` } as TextContent],
        isError: true,
      };
  }
}
