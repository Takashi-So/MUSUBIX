/**
 * Design Patterns
 *
 * Pattern detection, domain inference, and recommendation logic
 *
 * @packageDocumentation
 * @module cli/commands/design/patterns
 */

import type { DesignPattern } from './types.js';

/**
 * SOLID principles validation rules
 */
export const SOLID_PRINCIPLES = {
  S: 'Single Responsibility Principle',
  O: 'Open/Closed Principle',
  L: 'Liskov Substitution Principle',
  I: 'Interface Segregation Principle',
  D: 'Dependency Inversion Principle',
};

/**
 * Known design patterns
 */
export const KNOWN_PATTERNS: Record<string, DesignPattern> = {
  factory: {
    name: 'Factory',
    category: 'creational',
    intent: 'Define an interface for creating objects without specifying concrete classes',
    applicability: ['Object creation logic is complex', 'System needs to be independent of how objects are created'],
    consequences: {
      positive: ['Isolates concrete classes', 'Easy to introduce new products'],
      negative: ['May require new subclasses for minor variations'],
    },
  },
  singleton: {
    name: 'Singleton',
    category: 'creational',
    intent: 'Ensure a class has only one instance',
    applicability: ['Exactly one instance is needed', 'Global access point required'],
    consequences: {
      positive: ['Controlled access to sole instance', 'Reduced namespace'],
      negative: ['Difficult to test', 'Hidden dependencies'],
    },
  },
  observer: {
    name: 'Observer',
    category: 'behavioral',
    intent: 'Define a one-to-many dependency between objects',
    applicability: ['Changes to one object require changes to others', 'Objects should be loosely coupled'],
    consequences: {
      positive: ['Loose coupling', 'Broadcast communication'],
      negative: ['Unexpected updates', 'Memory leaks if not managed'],
    },
  },
  strategy: {
    name: 'Strategy',
    category: 'behavioral',
    intent: 'Define a family of algorithms and make them interchangeable',
    applicability: ['Multiple algorithms exist for a task', 'Behavior varies based on context'],
    consequences: {
      positive: ['Algorithms can vary independently', 'Eliminates conditional statements'],
      negative: ['Increased number of objects', 'Clients must be aware of strategies'],
    },
  },
  adapter: {
    name: 'Adapter',
    category: 'structural',
    intent: 'Convert interface of a class into another interface clients expect',
    applicability: ['Use existing class with incompatible interface', 'Create reusable class with unrelated classes'],
    consequences: {
      positive: ['Increased reusability', 'Flexibility in design'],
      negative: ['Increased complexity', 'Performance overhead'],
    },
  },
};

/**
 * Helper function for keyword matching
 * Uses word boundary for English, includes for Japanese (no word boundaries in Japanese)
 */
export function hasKeywordMatch(text: string, keyword: string): boolean {
  const isJapanese = /[\u3040-\u309F\u30A0-\u30FF\u4E00-\u9FAF]/.test(keyword);
  if (isJapanese) {
    return text.includes(keyword.toLowerCase());
  }
  const escaped = keyword.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const pattern = new RegExp(`\\b${escaped}\\b`, 'i');
  return pattern.test(text);
}

/**
 * Detect primary domain(s) from content based on domain-specific keywords
 * Uses word boundary matching to avoid false positives (English) and includes for Japanese
 */
export function detectDomainFromContent(content: string): string[] {
  const domains: string[] = [];
  const contentLower = content.toLowerCase();

  // Domain detection patterns with weighted keywords
  const domainPatterns: Record<string, { required: string[]; optional: string[] }> = {
    agriculture: {
      required: ['crop', '作物', 'harvest', '収穫', 'farm', '農業', 'farmer'],
      optional: ['plant', 'weather', 'field', 'soil', 'irrigation', 'yield', '栽培', '農機', 'fertilizer'],
    },
    library: {
      required: ['book', '図書', 'library', '貸出', 'loan'],
      optional: ['borrow', 'patron', 'catalog', 'overdue', '会員', '延滞', 'isbn'],
    },
    fitness: {
      required: ['workout', 'exercise', 'fitness', 'gym', 'トレーニング'],
      optional: ['trainer', 'muscle', 'cardio', 'weight', 'health', '運動', 'ワークアウト'],
    },
    petcare: {
      required: ['pet', 'ペット', 'veterinary', '獣医'],
      optional: ['dog', 'cat', 'grooming', 'vaccination', 'animal', '動物'],
    },
    music: {
      required: ['music', 'song', '楽曲', 'playlist', 'streaming', '音楽'],
      optional: ['artist', 'album', 'melody', 'audio', '曲', 'mp3'],
    },
    vehicle: {
      required: ['vehicle', '車両', 'car', 'automobile', '自動車'],
      optional: ['mileage', 'repair', 'inspection', '整備', '修理', 'odometer'],
    },
    event: {
      required: ['conference', 'seminar', 'workshop', 'イベント管理', 'attendee', 'イベント', 'チケット販売', '参加者管理', 'チェックイン'],
      optional: ['venue', 'speaker', '会場', 'ticket', 'チケット', 'rsvp', 'qr', '入場', '登壇', '参加者'],
    },
    insurance: {
      required: ['insurance', '保険', 'claim', 'policy'],
      optional: ['premium', 'coverage', 'assessment', 'underwriting', '請求', '査定'],
    },
    recruitment: {
      required: ['candidate', '候補者', 'job', '求人', 'recruit', '採用', 'hiring'],
      optional: ['interview', 'resume', 'offer', '面接', '履歴書', 'applicant'],
    },
    warehouse: {
      required: ['warehouse', '倉庫', 'shipment', '出荷', 'logistics'],
      optional: ['picking', 'packing', 'receiving', 'inventory', 'storage', '在庫'],
    },
    ecommerce: {
      required: ['cart', 'カート', 'checkout', 'shop', 'ecommerce', '買い物'],
      optional: ['product', 'order', 'payment', 'discount', '商品', '注文'],
    },
    healthcare: {
      required: ['patient', '患者', 'medical', '医療', 'clinic', '診療', 'prescription', '処方'],
      optional: ['doctor', 'nurse', 'appointment', 'diagnosis', 'treatment', 'lab', 'telemedicine', 'hospital'],
    },
    education: {
      required: ['student', '学生', 'course', '講座', 'grade', '成績', 'enrollment', '入学'],
      optional: ['teacher', 'classroom', 'assignment', 'tutor', 'certificate', 'lesson', '授業', '出席'],
    },
    restaurant: {
      required: ['menu', 'メニュー', 'table', 'テーブル', 'kitchen', '厨房', 'restaurant', 'レストラン'],
      optional: ['order', 'recipe', 'reservation', 'chef', 'dish', 'food', '料理', '注文'],
    },
    hotel: {
      required: ['room', '客室', 'guest', 'ゲスト', 'booking', 'ホテル', 'hotel', 'housekeeping'],
      optional: ['check-in', 'checkout', 'amenity', 'concierge', 'suite', 'reservation', '宿泊'],
    },
    banking: {
      required: ['account', '口座', 'transaction', '取引', 'loan', 'ローン', 'banking', '銀行'],
      optional: ['deposit', 'withdrawal', 'interest', 'credit', 'transfer', '振込', 'balance', 'ATM'],
    },
    realestate: {
      required: ['property', '物件', 'tenant', '入居者', 'lease', '賃貸', 'real estate', '不動産'],
      optional: ['listing', 'rent', 'mortgage', 'inspection', 'landlord', 'showing', '家賃'],
    },
    travel: {
      required: ['flight', 'フライト', 'itinerary', '旅程', 'travel', '旅行', 'booking', '航空券'],
      optional: ['visa', 'hotel', 'tour', 'currency', 'luggage', 'passport', '観光'],
    },
    manufacturing: {
      required: ['production', '生産', 'quality', '品質', 'assembly', '組立', 'manufacturing', '製造'],
      optional: ['defect', 'machine', 'shift', 'material', 'work order', 'inspection', '工程'],
    },
    logistics: {
      required: ['delivery', '配送', 'route', 'ルート', 'freight', '物流', 'logistics', 'tracking'],
      optional: ['driver', 'container', 'customs', 'warehouse', 'dispatch', 'carrier', '運送'],
    },
    game: {
      required: ['game', 'ゲーム', 'player', 'プレイヤー', 'matching', 'マッチング'],
      optional: ['ranking', 'item', 'gacha', 'guild', 'quest', 'ギルド', 'アイテム', 'ランキング'],
    },
    sports: {
      required: ['sports', 'スポーツ', 'gym', 'ジム', 'trainer', 'インストラクター'],
      optional: ['member', 'lesson', 'class', 'membership', 'coach', 'workout'],
    },
    media: {
      required: ['media', 'メディア', 'content', 'コンテンツ', 'article', '記事', 'publish'],
      optional: ['editor', 'writer', 'subscription', 'advertisement', '広告', '購読'],
    },
    legal: {
      required: ['law', '法律', 'lawyer', '弁護士', 'case', '案件', 'legal'],
      optional: ['lawsuit', 'contract', 'client', 'billing', '訴訟', '契約書'],
    },
    accounting: {
      required: ['accounting', '会計', 'journal', '仕訳', 'ledger', '勘定', 'fiscal'],
      optional: ['tax', 'expense', 'invoice', 'budget', '税務', '経費', '決算'],
    },
    hr: {
      required: ['hr', '人事', 'employee', '従業員', 'recruit', '採用', 'payroll', '給与'],
      optional: ['attendance', 'evaluation', 'training', 'leave', '勤怠', '評価', '研修'],
    },
    crm: {
      required: ['crm', 'customer', '顧客', 'lead', 'リード', 'sales', '営業'],
      optional: ['opportunity', 'deal', 'followup', 'pipeline', '商談', '見積'],
    },
    marketing: {
      required: ['marketing', 'マーケティング', 'campaign', 'キャンペーン', 'advertisement', '広告'],
      optional: ['target', 'conversion', 'roi', 'analytics', 'segment', 'コンバージョン'],
    },
    social: {
      required: ['sns', 'social', 'ソーシャル', 'post', '投稿', 'follow', 'フォロー'],
      optional: ['like', 'comment', 'share', 'timeline', 'いいね', 'コメント', 'シェア'],
    },
    iot: {
      required: ['iot', 'sensor', 'センサー', 'device', 'デバイス', 'smart'],
      optional: ['monitor', 'alert', 'dashboard', 'automation', '監視', 'アラート'],
    },
    energy: {
      required: ['energy', 'エネルギー', 'power', '電力', 'grid', 'electricity'],
      optional: ['consumption', 'renewable', 'battery', 'solar', '消費', '発電', '蓄電'],
    },
    construction: {
      required: ['construction', '建設', 'site', '現場', 'project', '工事'],
      optional: ['contractor', 'design', 'estimate', 'safety', '施工', '設計', '安全'],
    },
    aviation: {
      required: ['aviation', '航空', 'airport', '空港', 'boarding', '搭乗'],
      optional: ['checkin', 'baggage', 'seat', 'terminal', '手荷物', '座席'],
    },
    shipping: {
      required: ['shipping', '海運', 'vessel', '船舶', 'container', 'コンテナ', 'port', '港'],
      optional: ['cargo', 'route', 'bill of lading', '貨物', '航路'],
    },
    railway: {
      required: ['railway', '鉄道', 'train', '列車', 'station', '駅', 'timetable'],
      optional: ['platform', 'ticket', 'schedule', 'pass', 'ダイヤ', '改札', '定期'],
    },
    telecom: {
      required: ['telecom', '通信', 'network', 'ネットワーク', 'line', '回線', 'subscription'],
      optional: ['plan', 'data', 'sim', 'voice', '料金', 'プラン'],
    },
    security: {
      required: ['security', 'セキュリティ', 'auth', '認証', 'access', 'アクセス'],
      optional: ['audit', 'vulnerability', 'encryption', 'firewall', '監査', '暗号化'],
    },
    environment: {
      required: ['environment', '環境', 'co2', 'emission', '排出', 'sustainability'],
      optional: ['recycle', 'waste', 'esg', 'carbon', 'リサイクル', '廃棄物'],
    },
    agritech: {
      required: ['smart farm', 'スマート農業', 'agritech', 'precision agriculture'],
      optional: ['sensor', 'drone', 'irrigation', 'weather', 'soil', '灌漑', '土壌'],
    },
    beauty: {
      required: ['beauty', '美容', 'salon', 'サロン', 'stylist', 'スタイリスト'],
      optional: ['treatment', 'appointment', 'customer', 'menu', '施術', '予約'],
    },
    property: {
      required: ['property management', 'マンション管理', 'condominium', '管理組合'],
      optional: ['maintenance', 'repair', 'common area', 'board', '修繕', '理事会'],
    },
    caregiving: {
      required: ['caregiving', '介護', 'nursing home', '介護施設', 'resident', '入居者'],
      optional: ['care plan', 'staff', 'family', 'shift', 'ケアプラン', 'スタッフ'],
    },
    childcare: {
      required: ['childcare', '保育', 'nursery', '保育園', 'child', '園児', 'parent', '保護者'],
      optional: ['attendance', 'activity', 'allergy', 'event', '出欠', '連絡帳'],
    },
    archive: {
      required: ['archive', 'アーカイブ', 'document', '資料', 'digital', 'デジタル'],
      optional: ['metadata', 'search', 'classification', 'preservation', '検索', '分類'],
    },
    ticketing: {
      required: ['ticket', 'チケット', 'seat', '座席', 'performance', '公演', 'venue'],
      optional: ['booking', 'cancellation', 'qr', 'entrance', '予約', 'キャンセル', '入場'],
    },
    pharmacy: {
      required: ['pharmacy', '薬局', 'prescription', '処方箋', 'drug', '薬', 'dispensing'],
      optional: ['pharmacist', 'medication', 'dosage', 'refill', '調剤', '服薬'],
    },
    veterinary: {
      required: ['veterinary', '獣医', 'animal hospital', '動物病院', 'vaccination'],
      optional: ['pet', 'animal', 'treatment', 'diagnosis', '診察', 'ワクチン'],
    },
    museum: {
      required: ['museum', '博物館', 'exhibit', '展示', 'collection', 'コレクション'],
      optional: ['curator', 'artifact', 'gallery', 'visitor', '学芸員', '収蔵品'],
    },
    cinema: {
      required: ['cinema', '映画館', 'movie', '映画', 'screening', '上映'],
      optional: ['theater', 'showtime', 'popcorn', 'ticket', 'シアター', '座席'],
    },
    parking: {
      required: ['parking', '駐車場', 'vehicle', '車両', 'space', 'スペース'],
      optional: ['gate', 'fee', 'lot', 'slot', 'ゲート', '料金'],
    },
    laundry: {
      required: ['laundry', 'クリーニング', 'cleaning', '洗濯', 'garment'],
      optional: ['pickup', 'delivery', 'stain', 'dry clean', '集配', '仕上げ'],
    },
    rental: {
      required: ['rental', 'レンタル', 'rent', '貸出', 'borrow'],
      optional: ['return', 'deposit', 'duration', 'late fee', '返却', '延滞'],
    },
    subscription: {
      required: ['subscription', 'サブスク', 'recurring', '定期', 'membership'],
      optional: ['billing', 'renewal', 'cancel', 'upgrade', '更新', '解約'],
    },
    crowdfunding: {
      required: ['crowdfunding', 'クラウドファンディング', 'backer', '支援者', 'pledge'],
      optional: ['project', 'reward', 'funding', 'goal', 'リターン', '目標金額'],
    },
    auction: {
      required: ['auction', 'オークション', 'bid', '入札', 'lot'],
      optional: ['bidder', 'hammer', 'reserve', 'lot', '落札', '競り'],
    },
    wedding: {
      required: ['wedding', 'ウェディング', 'bride', '花嫁', 'ceremony', '挙式'],
      optional: ['groom', 'venue', 'guest', 'reception', '新郎', '披露宴'],
    },
    funeral: {
      required: ['funeral', '葬儀', 'deceased', '故人', 'ceremony'],
      optional: ['mourner', 'cremation', 'memorial', 'burial', '葬式', '火葬'],
    },
    charity: {
      required: ['charity', 'チャリティ', 'donation', '寄付', 'nonprofit'],
      optional: ['donor', 'beneficiary', 'volunteer', 'campaign', '支援', 'ボランティア'],
    },
    government: {
      required: ['government', '行政', 'citizen', '市民', 'public service'],
      optional: ['application', 'permit', 'certificate', 'registration', '申請', '届出'],
    },
    election: {
      required: ['election', '選挙', 'vote', '投票', 'ballot'],
      optional: ['voter', 'candidate', 'poll', 'counting', '候補者', '開票'],
    },
    survey: {
      required: ['survey', 'アンケート', 'questionnaire', '調査', 'response'],
      optional: ['question', 'respondent', 'analysis', 'result', '回答', '集計'],
    },
    elearning: {
      required: ['elearning', 'e-learning', 'オンライン学習', 'online course', 'LMS'],
      optional: ['learner', 'quiz', 'progress', 'certificate', '受講', '修了'],
    },
    news: {
      required: ['news', 'ニュース', 'article', '記事', 'headline'],
      optional: ['reporter', 'editor', 'breaking', 'press', '報道', '速報'],
    },
    podcast: {
      required: ['podcast', 'ポッドキャスト', 'episode', 'エピソード', 'audio'],
      optional: ['host', 'listener', 'download', 'subscribe', '配信', 'リスナー'],
    },
    streaming: {
      required: ['streaming', 'ストリーミング', 'live', 'ライブ', 'vod'],
      optional: ['content', 'viewer', 'channel', 'broadcast', '視聴', '配信'],
    },
  };

  for (const [domain, patterns] of Object.entries(domainPatterns)) {
    const hasRequired = patterns.required.some(kw => hasKeywordMatch(contentLower, kw));
    const optionalCount = patterns.optional.filter(kw => hasKeywordMatch(contentLower, kw)).length;

    if (hasRequired || optionalCount >= 3) {
      domains.push(domain);
    }
  }

  return domains;
}

/**
 * Detect applicable patterns
 */
export function detectApplicablePatterns(content: string): DesignPattern[] {
  const patterns: DesignPattern[] = [];
  const contentLower = content.toLowerCase();

  if (contentLower.includes('create') || contentLower.includes('factory') || contentLower.includes('builder')) {
    patterns.push(KNOWN_PATTERNS.factory);
  }
  if (contentLower.includes('single') || contentLower.includes('unique') || contentLower.includes('global')) {
    patterns.push(KNOWN_PATTERNS.singleton);
  }
  if (contentLower.includes('notify') || contentLower.includes('event') || contentLower.includes('subscribe')) {
    patterns.push(KNOWN_PATTERNS.observer);
  }
  if (contentLower.includes('algorithm') || contentLower.includes('strategy') || contentLower.includes('interchangeable')) {
    patterns.push(KNOWN_PATTERNS.strategy);
  }
  if (contentLower.includes('adapter') || contentLower.includes('convert') || contentLower.includes('compatible')) {
    patterns.push(KNOWN_PATTERNS.adapter);
  }

  return patterns;
}

/**
 * Generate pattern recommendations
 */
export function generatePatternRecommendations(analysisContent: string, patterns: DesignPattern[]): string[] {
  const recommendations: string[] = [];

  if (patterns.length === 0) {
    recommendations.push('Consider applying design patterns to improve code structure');
  }

  for (const pattern of patterns) {
    recommendations.push(`${pattern.name}: ${pattern.intent}`);
  }

  if (analysisContent.toLowerCase().includes('complex') || analysisContent.toLowerCase().includes('multiple')) {
    recommendations.push('Consider decomposing complex logic into smaller components');
  }

  return recommendations;
}
