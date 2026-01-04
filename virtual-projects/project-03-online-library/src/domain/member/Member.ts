/**
 * Member Entity
 * @requirements REQ-MEMBER-001, REQ-MEMBER-002, REQ-MEMBER-003, REQ-MEMBER-004
 * @design DES-LIBRARY-001 §3.3
 * @task TSK-LIB-003
 */

/**
 * MemberId - 会員ID値オブジェクト
 */
export class MemberId {
  private static counter = 0;

  constructor(public readonly value: string) {}

  static generate(): MemberId {
    MemberId.counter++;
    const timestamp = Date.now();
    const seq = String(MemberId.counter).padStart(4, '0');
    return new MemberId(`MBR-${timestamp}-${seq}`);
  }

  equals(other: MemberId): boolean {
    return this.value === other.value;
  }

  toString(): string {
    return this.value;
  }
}

/**
 * MemberType - 会員種別
 * @requirements REQ-MEMBER-004 (一般:5冊、学生:10冊、シニア:7冊)
 */
export enum MemberType {
  GENERAL = 'general',   // 一般会員: 5冊
  STUDENT = 'student',   // 学生会員: 10冊
  SENIOR = 'senior',     // シニア会員: 7冊
}

/**
 * MemberStatus - 会員ステータス
 * @requirements REQ-MEMBER-003 (inactive)
 */
export enum MemberStatus {
  ACTIVE = 'active',
  INACTIVE = 'inactive',
  SUSPENDED = 'suspended',
}

/**
 * 貸出上限マッピング
 * @requirements REQ-MEMBER-004
 */
const LOAN_LIMITS: Record<MemberType, number> = {
  [MemberType.GENERAL]: 5,
  [MemberType.STUDENT]: 10,
  [MemberType.SENIOR]: 7,
};

/**
 * CreateMemberParams - 会員作成パラメータ
 */
export interface CreateMemberParams {
  name: string;
  email: string;
  phone: string;
  address: string;
  birthDate: Date;
  memberType: MemberType;
}

/**
 * UpdateMemberParams - 会員更新パラメータ
 */
export interface UpdateMemberParams {
  name?: string;
  email?: string;
  phone?: string;
  address?: string;
  memberType?: MemberType;
}

/**
 * Member - 会員エンティティ（集約ルート）
 * @requirements REQ-MEMBER-001〜005
 * @design DES-LIBRARY-001 §3.3 Member Entity (Aggregate Root)
 */
export class Member {
  private constructor(
    public readonly id: MemberId,
    private _name: string,
    private _email: string,
    private _phone: string,
    private _address: string,
    public readonly birthDate: Date,
    private _memberType: MemberType,
    private _status: MemberStatus,
    public readonly createdAt: Date,
    private _updatedAt: Date,
    private _lastActivityAt: Date
  ) {}

  static create(params: CreateMemberParams): Member {
    // Email validation
    if (!Member.isValidEmail(params.email)) {
      throw new Error('Invalid email format');
    }

    const now = new Date();
    return new Member(
      MemberId.generate(),
      params.name,
      params.email,
      params.phone,
      params.address,
      params.birthDate,
      params.memberType,
      MemberStatus.ACTIVE,
      now,
      now,
      now
    );
  }

  private static isValidEmail(email: string): boolean {
    const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
    return emailRegex.test(email);
  }

  // Getters
  get name(): string {
    return this._name;
  }

  get email(): string {
    return this._email;
  }

  get phone(): string {
    return this._phone;
  }

  get address(): string {
    return this._address;
  }

  get memberType(): MemberType {
    return this._memberType;
  }

  get status(): MemberStatus {
    return this._status;
  }

  get updatedAt(): Date {
    return this._updatedAt;
  }

  get lastActivityAt(): Date {
    return this._lastActivityAt;
  }

  /**
   * 貸出上限を取得
   * @requirements REQ-MEMBER-004
   */
  getLoanLimit(): number {
    return LOAN_LIMITS[this._memberType];
  }

  /**
   * 貸出可能かどうか
   * @requirements REQ-MEMBER-005
   */
  isEligibleForLoan(): boolean {
    return this._status === MemberStatus.ACTIVE;
  }

  /**
   * 会員情報を更新
   * @requirements REQ-MEMBER-002
   */
  update(params: UpdateMemberParams): void {
    if (params.name !== undefined) {
      this._name = params.name;
    }
    if (params.email !== undefined) {
      if (!Member.isValidEmail(params.email)) {
        throw new Error('Invalid email format');
      }
      this._email = params.email;
    }
    if (params.phone !== undefined) {
      this._phone = params.phone;
    }
    if (params.address !== undefined) {
      this._address = params.address;
    }
    if (params.memberType !== undefined) {
      this._memberType = params.memberType;
    }
    this._updatedAt = new Date();
  }

  /**
   * アクティビティを記録
   */
  recordActivity(): void {
    this._lastActivityAt = new Date();
  }

  /**
   * 会員を非アクティブ化
   * @requirements REQ-MEMBER-003
   */
  deactivate(): void {
    this._status = MemberStatus.INACTIVE;
    this._updatedAt = new Date();
  }

  /**
   * 会員をアクティブ化
   */
  activate(): void {
    this._status = MemberStatus.ACTIVE;
    this._updatedAt = new Date();
  }

  /**
   * 会員を停止
   */
  suspend(): void {
    this._status = MemberStatus.SUSPENDED;
    this._updatedAt = new Date();
  }

  /**
   * 180日以上非アクティブかチェック
   * @requirements REQ-MEMBER-003
   */
  isInactiveFor180Days(): boolean {
    const now = new Date();
    const diffTime = now.getTime() - this._lastActivityAt.getTime();
    const diffDays = diffTime / (1000 * 60 * 60 * 24);
    return diffDays >= 180;
  }

  /**
   * 復元用ファクトリメソッド
   */
  static reconstruct(
    id: MemberId,
    name: string,
    email: string,
    phone: string,
    address: string,
    birthDate: Date,
    memberType: MemberType,
    status: MemberStatus,
    createdAt: Date,
    updatedAt: Date,
    lastActivityAt: Date
  ): Member {
    return new Member(
      id,
      name,
      email,
      phone,
      address,
      birthDate,
      memberType,
      status,
      createdAt,
      updatedAt,
      lastActivityAt
    );
  }
}
