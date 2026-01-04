/**
 * AdapterNaming - Adapter命名規則モジュール
 * 
 * @description Adapterパターンの命名規則を標準化
 * @requirement REQ-MUSUBIX-LEARN-003 (SDD Workflow Feedback)
 * @version 1.1.4
 * 
 * 学習フィードバック PAT-006 の改善:
 * - 命名規則の一貫性: IXxxServiceAdapter
 * - Service/Repository/Gateway の明確な区分
 * - 混乱を防ぐ標準命名パターン
 */

/**
 * Adapter命名パターン
 */
export type AdapterType = 'service' | 'repository' | 'gateway';

/**
 * Adapterの標準命名規則
 * 
 * パターン: I{Domain}{Type}Adapter
 * 
 * 例:
 * - IMemberServiceAdapter (会員サービスアダプター)
 * - ITicketServiceAdapter (チケットサービスアダプター)
 * - IPaymentGatewayAdapter (決済ゲートウェイアダプター)
 */
export interface AdapterNamingRule {
  /** ドメイン名（例: Member, Ticket, Payment） */
  domain: string;
  /** Adapterタイプ */
  type: AdapterType;
  /** 生成されるインターフェース名 */
  interfaceName: string;
  /** 生成される実装クラス名 */
  implementationName: string;
}

/**
 * AdapterNamingHelper - Adapter命名ヘルパー
 */
export class AdapterNamingHelper {
  /**
   * Adapterインターフェース名を生成
   * 
   * @param domain - ドメイン名
   * @param type - Adapterタイプ
   * @returns インターフェース名
   */
  static generateInterfaceName(domain: string, type: AdapterType): string {
    const capitalizedDomain = domain.charAt(0).toUpperCase() + domain.slice(1);
    const typeMap: Record<AdapterType, string> = {
      service: 'Service',
      repository: 'Repository',
      gateway: 'Gateway',
    };
    return `I${capitalizedDomain}${typeMap[type]}Adapter`;
  }

  /**
   * Adapter実装クラス名を生成
   * 
   * @param domain - ドメイン名
   * @param type - Adapterタイプ
   * @param variant - バリアント（例: InMemory, Http, Mock）
   * @returns 実装クラス名
   */
  static generateImplementationName(
    domain: string, 
    type: AdapterType,
    variant: string = ''
  ): string {
    const capitalizedDomain = domain.charAt(0).toUpperCase() + domain.slice(1);
    const typeMap: Record<AdapterType, string> = {
      service: 'Service',
      repository: 'Repository',
      gateway: 'Gateway',
    };
    const prefix = variant ? `${variant}` : '';
    return `${prefix}${capitalizedDomain}${typeMap[type]}Adapter`;
  }

  /**
   * 命名規則に従った完全なAdapter定義を生成
   * 
   * @param domain - ドメイン名
   * @param type - Adapterタイプ
   * @returns 命名ルール
   */
  static generateNamingRule(domain: string, type: AdapterType): AdapterNamingRule {
    return {
      domain,
      type,
      interfaceName: this.generateInterfaceName(domain, type),
      implementationName: this.generateImplementationName(domain, type),
    };
  }

  /**
   * 既存のAdapter名を標準形式に正規化
   * 
   * @param currentName - 現在のAdapter名
   * @returns 正規化された名前と推奨事項
   */
  static normalizeAdapterName(currentName: string): {
    normalized: string;
    wasCorrect: boolean;
    suggestion?: string;
  } {
    // パターン: I{Domain}Adapter → I{Domain}ServiceAdapter
    const shortPattern = /^I([A-Z][a-zA-Z]+)Adapter$/;
    const shortMatch = currentName.match(shortPattern);
    
    if (shortMatch) {
      const domain = shortMatch[1];
      const normalized = `I${domain}ServiceAdapter`;
      return {
        normalized,
        wasCorrect: false,
        suggestion: `'${currentName}' should be renamed to '${normalized}' for consistency`,
      };
    }

    // パターン: I{Domain}ServiceAdapter（正しい形式）
    const correctPattern = /^I([A-Z][a-zA-Z]+)(Service|Repository|Gateway)Adapter$/;
    if (correctPattern.test(currentName)) {
      return {
        normalized: currentName,
        wasCorrect: true,
      };
    }

    // その他のパターン
    return {
      normalized: currentName,
      wasCorrect: false,
      suggestion: `'${currentName}' does not follow the naming convention: I{Domain}{Type}Adapter`,
    };
  }

  /**
   * TypeScriptコード内のAdapter命名を検証
   * 
   * @param code - 検証対象のコード
   * @returns 検証結果と推奨事項
   */
  static validateAdapterNames(code: string): {
    valid: string[];
    invalid: { name: string; suggestion: string }[];
  } {
    const adapterPattern = /interface\s+(I[A-Z][a-zA-Z]*Adapter)/g;
    const valid: string[] = [];
    const invalid: { name: string; suggestion: string }[] = [];

    let match;
    while ((match = adapterPattern.exec(code)) !== null) {
      const name = match[1];
      const result = this.normalizeAdapterName(name);
      
      if (result.wasCorrect) {
        valid.push(name);
      } else if (result.suggestion) {
        invalid.push({ name, suggestion: result.suggestion });
      }
    }

    return { valid, invalid };
  }
}

/**
 * Adapter命名の標準テンプレート
 */
export const ADAPTER_TEMPLATES = {
  /**
   * サービスアダプターテンプレート
   */
  serviceAdapter: (domain: string) => `
/**
 * ${domain}サービスアダプターインターフェース
 */
export interface I${domain}ServiceAdapter {
  // サービスメソッドを定義
}
`,

  /**
   * リポジトリアダプターテンプレート
   */
  repositoryAdapter: (domain: string) => `
/**
 * ${domain}リポジトリアダプターインターフェース
 */
export interface I${domain}RepositoryAdapter {
  // リポジトリメソッドを定義
}
`,

  /**
   * ゲートウェイアダプターテンプレート
   */
  gatewayAdapter: (domain: string) => `
/**
 * ${domain}ゲートウェイアダプターインターフェース
 */
export interface I${domain}GatewayAdapter {
  // 外部連携メソッドを定義
}
`,
};

// シングルトンインスタンス
export const adapterNamingHelper = new AdapterNamingHelper();

// ファクトリ関数
export function createAdapterNamingHelper(): typeof AdapterNamingHelper {
  return AdapterNamingHelper;
}
