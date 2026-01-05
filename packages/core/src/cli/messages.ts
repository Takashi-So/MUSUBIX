/**
 * @fileoverview CLI Error Messages - Japanese translations
 * @traceability REQ-I18N-001
 */

export const CLI_MESSAGES = {
  en: {
    // General
    welcome: 'Welcome to MUSUBIX - Neuro-Symbolic AI Coding System',
    version: 'Version',
    
    // Errors
    error: {
      fileNotFound: 'File not found: {path}',
      invalidFormat: 'Invalid format: {format}. Expected: {expected}',
      missingArgument: 'Missing required argument: {arg}',
      invalidOption: 'Invalid option: {option}',
      parseError: 'Failed to parse file: {file}',
      validationFailed: 'Validation failed: {count} error(s) found',
      connectionFailed: 'Connection failed: {target}',
      timeout: 'Operation timed out after {seconds} seconds',
      permissionDenied: 'Permission denied: {path}',
      unknownCommand: 'Unknown command: {command}',
    },
    
    // Success messages
    success: {
      initialized: 'Project initialized successfully',
      validated: 'Validation passed',
      generated: 'Generated {count} file(s)',
      exported: 'Exported to {path}',
      imported: 'Imported {count} item(s)',
      saved: 'Saved successfully',
    },
    
    // Commands
    commands: {
      init: {
        description: 'Initialize a new MUSUBIX project',
        creating: 'Creating project structure...',
        done: 'Project initialized in {path}',
      },
      requirements: {
        description: 'Analyze and validate requirements',
        analyzing: 'Analyzing requirements...',
        validating: 'Validating EARS format...',
        found: 'Found {count} requirement(s)',
      },
      design: {
        description: 'Generate and validate designs',
        generating: 'Generating design...',
        patterns: 'Detecting patterns...',
      },
      learn: {
        description: 'Manage self-learning system',
        status: 'Learning Status',
        patterns: 'Learned Patterns',
        exporting: 'Exporting learning data...',
        importing: 'Importing learning data...',
      },
      ontology: {
        description: 'Knowledge graph operations',
        validating: 'Validating knowledge graph...',
        checking: 'Checking for circular dependencies...',
        stats: 'Knowledge Graph Statistics',
      },
    },
    
    // Labels
    labels: {
      total: 'Total',
      passed: 'Passed',
      failed: 'Failed',
      warnings: 'Warnings',
      errors: 'Errors',
      confidence: 'Confidence',
      traceability: 'Traceability',
    },
  },
  
  ja: {
    // 一般
    welcome: 'MUSUBIX へようこそ - ニューロシンボリックAIコーディングシステム',
    version: 'バージョン',
    
    // エラー
    error: {
      fileNotFound: 'ファイルが見つかりません: {path}',
      invalidFormat: '無効なフォーマット: {format}。期待値: {expected}',
      missingArgument: '必須引数が不足しています: {arg}',
      invalidOption: '無効なオプション: {option}',
      parseError: 'ファイルの解析に失敗しました: {file}',
      validationFailed: '検証失敗: {count} 件のエラーが見つかりました',
      connectionFailed: '接続に失敗しました: {target}',
      timeout: '操作がタイムアウトしました ({seconds} 秒)',
      permissionDenied: 'アクセス権限がありません: {path}',
      unknownCommand: '不明なコマンド: {command}',
    },
    
    // 成功メッセージ
    success: {
      initialized: 'プロジェクトを正常に初期化しました',
      validated: '検証に合格しました',
      generated: '{count} 個のファイルを生成しました',
      exported: '{path} にエクスポートしました',
      imported: '{count} 件をインポートしました',
      saved: '正常に保存しました',
    },
    
    // コマンド
    commands: {
      init: {
        description: '新しいMUSUBIXプロジェクトを初期化',
        creating: 'プロジェクト構造を作成中...',
        done: 'プロジェクトを {path} に初期化しました',
      },
      requirements: {
        description: '要件の分析と検証',
        analyzing: '要件を分析中...',
        validating: 'EARS形式を検証中...',
        found: '{count} 件の要件が見つかりました',
      },
      design: {
        description: '設計の生成と検証',
        generating: '設計を生成中...',
        patterns: 'パターンを検出中...',
      },
      learn: {
        description: '自己学習システムの管理',
        status: '学習状態',
        patterns: '学習済みパターン',
        exporting: '学習データをエクスポート中...',
        importing: '学習データをインポート中...',
      },
      ontology: {
        description: '知識グラフ操作',
        validating: '知識グラフを検証中...',
        checking: '循環依存をチェック中...',
        stats: '知識グラフ統計',
      },
    },
    
    // ラベル
    labels: {
      total: '合計',
      passed: '合格',
      failed: '失敗',
      warnings: '警告',
      errors: 'エラー',
      confidence: '信頼度',
      traceability: 'トレーサビリティ',
    },
  },
};

/**
 * Get message for current locale
 */
export function getMessage(
  key: string,
  locale: 'en' | 'ja' = 'en',
  params: Record<string, string | number> = {}
): string {
  const messages = CLI_MESSAGES[locale] || CLI_MESSAGES.en;
  const keys = key.split('.');
  
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  let value: any = messages;
  for (const k of keys) {
    value = value?.[k];
    if (value === undefined) break;
  }
  
  if (typeof value !== 'string') {
    // Fallback to English
    value = CLI_MESSAGES.en;
    for (const k of keys) {
      value = value?.[k];
      if (value === undefined) break;
    }
  }
  
  if (typeof value !== 'string') {
    return key; // Return key if not found
  }
  
  // Replace placeholders
  return value.replace(/\{(\w+)\}/g, (_, name) => 
    String(params[name] ?? `{${name}}`)
  );
}

/**
 * Detect system locale
 */
export function detectLocale(): 'en' | 'ja' {
  const env = process.env.LANG || process.env.LC_ALL || process.env.LANGUAGE || '';
  if (env.toLowerCase().startsWith('ja')) {
    return 'ja';
  }
  return 'en';
}

/**
 * CLI message helper with auto-detection
 */
export function t(key: string, params: Record<string, string | number> = {}): string {
  return getMessage(key, detectLocale(), params);
}
