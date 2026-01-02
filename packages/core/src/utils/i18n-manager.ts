/**
 * Internationalization (i18n) Manager
 * 
 * Manages multi-language support for messages, labels, and content
 * 
 * @packageDocumentation
 * @module utils/i18n
 * 
 * @see REQ-I18N-001 - Internationalization Support
 * @see Article VII - Seamless Integration
 */

/**
 * Supported locale
 */
export type SupportedLocale = 'en' | 'ja' | 'zh' | 'ko' | 'de' | 'fr' | 'es' | 'pt';

/**
 * Translation key path
 */
export type TranslationKey = string;

/**
 * Translation value
 */
export type TranslationValue = string | Record<string, unknown>;

/**
 * Translation dictionary
 */
export type TranslationDictionary = Record<TranslationKey, TranslationValue>;

/**
 * Locale data
 */
export interface LocaleData {
  /** Locale code */
  locale: SupportedLocale;
  /** Display name */
  name: string;
  /** Native name */
  nativeName: string;
  /** Direction */
  direction: 'ltr' | 'rtl';
  /** Translations */
  translations: TranslationDictionary;
}

/**
 * Plural rules
 */
export interface PluralRules {
  /** Zero form */
  zero?: string;
  /** One form */
  one: string;
  /** Two form */
  two?: string;
  /** Few form */
  few?: string;
  /** Many form */
  many?: string;
  /** Other form */
  other: string;
}

/**
 * Date/time format options
 */
export interface DateTimeFormatOptions {
  /** Date style */
  dateStyle?: 'full' | 'long' | 'medium' | 'short';
  /** Time style */
  timeStyle?: 'full' | 'long' | 'medium' | 'short';
  /** Hour cycle */
  hourCycle?: 'h11' | 'h12' | 'h23' | 'h24';
}

/**
 * Number format options
 */
export interface NumberFormatOptions {
  /** Style */
  style?: 'decimal' | 'currency' | 'percent' | 'unit';
  /** Currency code */
  currency?: string;
  /** Minimum fraction digits */
  minimumFractionDigits?: number;
  /** Maximum fraction digits */
  maximumFractionDigits?: number;
  /** Unit */
  unit?: string;
}

/**
 * I18n configuration
 */
export interface I18nConfig {
  /** Default locale */
  defaultLocale: SupportedLocale;
  /** Fallback locale */
  fallbackLocale: SupportedLocale;
  /** Load path pattern */
  loadPath?: string;
  /** Cache translations */
  cache: boolean;
  /** Debug mode */
  debug: boolean;
  /** Missing key handler */
  missingKeyHandler?: (key: string, locale: SupportedLocale) => string;
}

/**
 * Default configuration
 */
export const DEFAULT_I18N_CONFIG: I18nConfig = {
  defaultLocale: 'en',
  fallbackLocale: 'en',
  cache: true,
  debug: false,
};

/**
 * Built-in English translations
 */
const EN_TRANSLATIONS: TranslationDictionary = {
  // Common
  'common.yes': 'Yes',
  'common.no': 'No',
  'common.ok': 'OK',
  'common.cancel': 'Cancel',
  'common.save': 'Save',
  'common.delete': 'Delete',
  'common.edit': 'Edit',
  'common.create': 'Create',
  'common.search': 'Search',
  'common.loading': 'Loading...',
  'common.error': 'Error',
  'common.success': 'Success',
  'common.warning': 'Warning',
  'common.info': 'Information',

  // Requirements
  'requirements.title': 'Requirements',
  'requirements.create': 'Create Requirement',
  'requirements.edit': 'Edit Requirement',
  'requirements.delete': 'Delete Requirement',
  'requirements.notFound': 'Requirement not found',
  'requirements.validation.titleRequired': 'Title is required',
  'requirements.validation.typeRequired': 'Type is required',

  // Design
  'design.title': 'Design',
  'design.c4.context': 'Context Diagram',
  'design.c4.container': 'Container Diagram',
  'design.c4.component': 'Component Diagram',
  'design.adr.title': 'Architecture Decision Records',

  // Tasks
  'tasks.title': 'Tasks',
  'tasks.status.pending': 'Pending',
  'tasks.status.inProgress': 'In Progress',
  'tasks.status.completed': 'Completed',
  'tasks.status.blocked': 'Blocked',

  // Validation
  'validation.title': 'Validation',
  'validation.passed': 'Validation Passed',
  'validation.failed': 'Validation Failed',
  'validation.errors': '{{count}} error(s) found',
  'validation.warnings': '{{count}} warning(s) found',

  // Errors
  'errors.generic': 'An error occurred',
  'errors.network': 'Network error',
  'errors.unauthorized': 'Unauthorized access',
  'errors.forbidden': 'Access forbidden',
  'errors.notFound': 'Resource not found',
  'errors.serverError': 'Server error',
};

/**
 * Built-in Japanese translations
 */
const JA_TRANSLATIONS: TranslationDictionary = {
  // Common
  'common.yes': 'はい',
  'common.no': 'いいえ',
  'common.ok': 'OK',
  'common.cancel': 'キャンセル',
  'common.save': '保存',
  'common.delete': '削除',
  'common.edit': '編集',
  'common.create': '作成',
  'common.search': '検索',
  'common.loading': '読み込み中...',
  'common.error': 'エラー',
  'common.success': '成功',
  'common.warning': '警告',
  'common.info': '情報',

  // Requirements
  'requirements.title': '要件',
  'requirements.create': '要件を作成',
  'requirements.edit': '要件を編集',
  'requirements.delete': '要件を削除',
  'requirements.notFound': '要件が見つかりません',
  'requirements.validation.titleRequired': 'タイトルは必須です',
  'requirements.validation.typeRequired': 'タイプは必須です',

  // Design
  'design.title': '設計',
  'design.c4.context': 'コンテキスト図',
  'design.c4.container': 'コンテナ図',
  'design.c4.component': 'コンポーネント図',
  'design.adr.title': 'アーキテクチャ決定記録',

  // Tasks
  'tasks.title': 'タスク',
  'tasks.status.pending': '未着手',
  'tasks.status.inProgress': '進行中',
  'tasks.status.completed': '完了',
  'tasks.status.blocked': 'ブロック中',

  // Validation
  'validation.title': '検証',
  'validation.passed': '検証成功',
  'validation.failed': '検証失敗',
  'validation.errors': '{{count}}件のエラー',
  'validation.warnings': '{{count}}件の警告',

  // Errors
  'errors.generic': 'エラーが発生しました',
  'errors.network': 'ネットワークエラー',
  'errors.unauthorized': '認証が必要です',
  'errors.forbidden': 'アクセスが拒否されました',
  'errors.notFound': 'リソースが見つかりません',
  'errors.serverError': 'サーバーエラー',
};

/**
 * Built-in locales
 */
const BUILT_IN_LOCALES: Record<SupportedLocale, LocaleData> = {
  en: {
    locale: 'en',
    name: 'English',
    nativeName: 'English',
    direction: 'ltr',
    translations: EN_TRANSLATIONS,
  },
  ja: {
    locale: 'ja',
    name: 'Japanese',
    nativeName: '日本語',
    direction: 'ltr',
    translations: JA_TRANSLATIONS,
  },
  zh: {
    locale: 'zh',
    name: 'Chinese',
    nativeName: '中文',
    direction: 'ltr',
    translations: {},
  },
  ko: {
    locale: 'ko',
    name: 'Korean',
    nativeName: '한국어',
    direction: 'ltr',
    translations: {},
  },
  de: {
    locale: 'de',
    name: 'German',
    nativeName: 'Deutsch',
    direction: 'ltr',
    translations: {},
  },
  fr: {
    locale: 'fr',
    name: 'French',
    nativeName: 'Français',
    direction: 'ltr',
    translations: {},
  },
  es: {
    locale: 'es',
    name: 'Spanish',
    nativeName: 'Español',
    direction: 'ltr',
    translations: {},
  },
  pt: {
    locale: 'pt',
    name: 'Portuguese',
    nativeName: 'Português',
    direction: 'ltr',
    translations: {},
  },
};

/**
 * Interpolation options
 */
export interface InterpolationOptions {
  /** Variables to interpolate */
  [key: string]: string | number | boolean | undefined;
}

/**
 * I18n Manager
 */
export class I18nManager {
  private config: I18nConfig;
  private currentLocale: SupportedLocale;
  private locales: Map<SupportedLocale, LocaleData> = new Map();
  private cache: Map<string, string> = new Map();
  private loadedLocales: Set<SupportedLocale> = new Set();

  constructor(config?: Partial<I18nConfig>) {
    this.config = { ...DEFAULT_I18N_CONFIG, ...config };
    this.currentLocale = this.config.defaultLocale;

    // Load built-in locales
    for (const [locale, data] of Object.entries(BUILT_IN_LOCALES)) {
      this.locales.set(locale as SupportedLocale, data);
      this.loadedLocales.add(locale as SupportedLocale);
    }
  }

  /**
   * Get current locale
   */
  getLocale(): SupportedLocale {
    return this.currentLocale;
  }

  /**
   * Set current locale
   */
  setLocale(locale: SupportedLocale): void {
    if (!this.isLocaleSupported(locale)) {
      if (this.config.debug) {
        console.warn(`Locale ${locale} is not supported, using fallback`);
      }
      return;
    }
    this.currentLocale = locale;
    this.cache.clear();
  }

  /**
   * Check if locale is supported
   */
  isLocaleSupported(locale: string): locale is SupportedLocale {
    return this.locales.has(locale as SupportedLocale);
  }

  /**
   * Get all supported locales
   */
  getSupportedLocales(): SupportedLocale[] {
    return Array.from(this.locales.keys());
  }

  /**
   * Get locale data
   */
  getLocaleData(locale?: SupportedLocale): LocaleData | undefined {
    return this.locales.get(locale ?? this.currentLocale);
  }

  /**
   * Translate a key
   */
  t(key: TranslationKey, options?: InterpolationOptions): string {
    // Check cache
    const cacheKey = `${this.currentLocale}:${key}:${JSON.stringify(options ?? {})}`;
    if (this.config.cache && this.cache.has(cacheKey)) {
      return this.cache.get(cacheKey)!;
    }

    // Get translation
    let translation = this.getTranslation(key, this.currentLocale);

    // Fallback to default locale
    if (!translation && this.currentLocale !== this.config.fallbackLocale) {
      translation = this.getTranslation(key, this.config.fallbackLocale);
    }

    // Handle missing translation
    if (!translation) {
      if (this.config.missingKeyHandler) {
        translation = this.config.missingKeyHandler(key, this.currentLocale);
      } else if (this.config.debug) {
        console.warn(`Missing translation: ${key} for locale ${this.currentLocale}`);
        translation = `[${key}]`;
      } else {
        translation = key;
      }
    }

    // Interpolate
    if (options) {
      translation = this.interpolate(translation, options);
    }

    // Cache result
    if (this.config.cache) {
      this.cache.set(cacheKey, translation);
    }

    return translation;
  }

  /**
   * Translate with plural support
   */
  tp(key: TranslationKey, count: number, options?: InterpolationOptions): string {
    const pluralKey = this.getPluralKey(key, count);
    return this.t(pluralKey, { ...options, count });
  }

  /**
   * Get translation value
   */
  private getTranslation(key: TranslationKey, locale: SupportedLocale): string | undefined {
    const localeData = this.locales.get(locale);
    if (!localeData) return undefined;

    // Handle nested keys
    const parts = key.split('.');
    let value: TranslationValue | undefined = localeData.translations;

    for (const part of parts) {
      if (typeof value === 'object' && value !== null) {
        value = (value as Record<string, TranslationValue>)[part];
      } else {
        return undefined;
      }
    }

    return typeof value === 'string' ? value : undefined;
  }

  /**
   * Get plural key based on count
   */
  private getPluralKey(key: TranslationKey, count: number): TranslationKey {
    const pluralForm = this.getPluralForm(count);
    const pluralKey = `${key}.${pluralForm}`;
    
    // Check if plural key exists
    if (this.getTranslation(pluralKey, this.currentLocale)) {
      return pluralKey;
    }

    // Fallback to 'other'
    const otherKey = `${key}.other`;
    if (this.getTranslation(otherKey, this.currentLocale)) {
      return otherKey;
    }

    return key;
  }

  /**
   * Get plural form based on count
   */
  private getPluralForm(count: number): string {
    // Simplified plural rules for common locales
    const locale = this.currentLocale;

    if (locale === 'ja' || locale === 'zh' || locale === 'ko') {
      // East Asian languages typically don't have plural forms
      return 'other';
    }

    // English and similar languages
    if (count === 0) return 'zero';
    if (count === 1) return 'one';
    if (count === 2) return 'two';
    return 'other';
  }

  /**
   * Interpolate variables in translation
   */
  private interpolate(text: string, options: InterpolationOptions): string {
    return text.replace(/\{\{(\w+)\}\}/g, (match, key) => {
      const value = options[key];
      return value !== undefined ? String(value) : match;
    });
  }

  /**
   * Add translations for a locale
   */
  addTranslations(
    locale: SupportedLocale,
    translations: TranslationDictionary
  ): void {
    const existing = this.locales.get(locale);
    if (existing) {
      existing.translations = {
        ...existing.translations,
        ...translations,
      };
    } else {
      this.locales.set(locale, {
        locale,
        name: locale,
        nativeName: locale,
        direction: 'ltr',
        translations,
      });
    }
    this.loadedLocales.add(locale);
    this.cache.clear();
  }

  /**
   * Load translations from object
   */
  loadTranslations(data: Record<SupportedLocale, TranslationDictionary>): void {
    for (const [locale, translations] of Object.entries(data)) {
      this.addTranslations(locale as SupportedLocale, translations);
    }
  }

  /**
   * Format date
   */
  formatDate(date: Date, options?: DateTimeFormatOptions): string {
    const formatter = new Intl.DateTimeFormat(this.currentLocale, options);
    return formatter.format(date);
  }

  /**
   * Format number
   */
  formatNumber(value: number, options?: NumberFormatOptions): string {
    const formatter = new Intl.NumberFormat(this.currentLocale, options);
    return formatter.format(value);
  }

  /**
   * Format currency
   */
  formatCurrency(value: number, currency: string): string {
    return this.formatNumber(value, {
      style: 'currency',
      currency,
    });
  }

  /**
   * Format percentage
   */
  formatPercent(value: number): string {
    return this.formatNumber(value, {
      style: 'percent',
      minimumFractionDigits: 0,
      maximumFractionDigits: 2,
    });
  }

  /**
   * Format relative time
   */
  formatRelativeTime(date: Date, referenceDate?: Date): string {
    const now = referenceDate ?? new Date();
    const diffMs = date.getTime() - now.getTime();
    const diffSec = Math.round(diffMs / 1000);
    const diffMin = Math.round(diffSec / 60);
    const diffHour = Math.round(diffMin / 60);
    const diffDay = Math.round(diffHour / 24);

    const rtf = new Intl.RelativeTimeFormat(this.currentLocale, { numeric: 'auto' });

    if (Math.abs(diffSec) < 60) {
      return rtf.format(diffSec, 'second');
    }
    if (Math.abs(diffMin) < 60) {
      return rtf.format(diffMin, 'minute');
    }
    if (Math.abs(diffHour) < 24) {
      return rtf.format(diffHour, 'hour');
    }
    if (Math.abs(diffDay) < 30) {
      return rtf.format(diffDay, 'day');
    }

    // Fall back to date formatting
    return this.formatDate(date, { dateStyle: 'medium' });
  }

  /**
   * Get text direction for current locale
   */
  getTextDirection(): 'ltr' | 'rtl' {
    return this.locales.get(this.currentLocale)?.direction ?? 'ltr';
  }

  /**
   * Check if current locale is RTL
   */
  isRTL(): boolean {
    return this.getTextDirection() === 'rtl';
  }

  /**
   * Get display name for locale
   */
  getLocaleDisplayName(locale?: SupportedLocale): string {
    const data = this.locales.get(locale ?? this.currentLocale);
    return data?.nativeName ?? locale ?? this.currentLocale;
  }

  /**
   * Create scoped translator
   */
  scope(namespace: string): (key: string, options?: InterpolationOptions) => string {
    return (key: string, options?: InterpolationOptions) => {
      return this.t(`${namespace}.${key}`, options);
    };
  }

  /**
   * Check if translation exists
   */
  exists(key: TranslationKey, locale?: SupportedLocale): boolean {
    return this.getTranslation(key, locale ?? this.currentLocale) !== undefined;
  }

  /**
   * Get all keys for a namespace
   */
  getKeys(namespace?: string): string[] {
    const localeData = this.locales.get(this.currentLocale);
    if (!localeData) return [];

    const keys = Object.keys(localeData.translations);
    
    if (namespace) {
      return keys.filter((k) => k.startsWith(`${namespace}.`));
    }

    return keys;
  }

  /**
   * Clear translation cache
   */
  clearCache(): void {
    this.cache.clear();
  }

  /**
   * Export translations for locale
   */
  exportTranslations(locale?: SupportedLocale): TranslationDictionary {
    const localeData = this.locales.get(locale ?? this.currentLocale);
    return { ...localeData?.translations };
  }

  /**
   * Get statistics
   */
  getStats(): {
    currentLocale: SupportedLocale;
    supportedLocales: number;
    loadedLocales: number;
    translationKeys: number;
    cacheSize: number;
  } {
    const localeData = this.locales.get(this.currentLocale);
    return {
      currentLocale: this.currentLocale,
      supportedLocales: this.locales.size,
      loadedLocales: this.loadedLocales.size,
      translationKeys: localeData ? Object.keys(localeData.translations).length : 0,
      cacheSize: this.cache.size,
    };
  }
}

/**
 * Create I18n manager instance
 */
export function createI18nManager(config?: Partial<I18nConfig>): I18nManager {
  return new I18nManager(config);
}

/**
 * Default global instance
 */
let globalI18n: I18nManager | null = null;

/**
 * Get global I18n instance
 */
export function getI18n(): I18nManager {
  if (!globalI18n) {
    globalI18n = new I18nManager();
  }
  return globalI18n;
}

/**
 * Initialize global I18n
 */
export function initI18n(config?: Partial<I18nConfig>): I18nManager {
  globalI18n = new I18nManager(config);
  return globalI18n;
}

/**
 * Shorthand translate function
 */
export function t(key: TranslationKey, options?: InterpolationOptions): string {
  return getI18n().t(key, options);
}

/**
 * Shorthand translate with plural
 */
export function tp(key: TranslationKey, count: number, options?: InterpolationOptions): string {
  return getI18n().tp(key, count, options);
}
