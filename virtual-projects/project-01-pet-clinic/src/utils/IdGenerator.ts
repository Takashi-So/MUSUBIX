/**
 * IdGenerator - ユニークID生成ユーティリティ
 * 
 * @requirement REQ-MEDICAL-001, REQ-RESERVE-001, REQ-PET-001
 * @design DES-PETCLINIC-001 Section 3.3
 * @pattern Factory
 */
export class IdGenerator {
  private counter = 0;

  constructor(private readonly prefix: string) {}

  /**
   * ユニークIDを生成
   * @returns {string} PREFIX-timestamp-counter形式のID
   */
  generate(): string {
    this.counter++;
    return `${this.prefix}-${Date.now()}-${this.counter}`;
  }

  /**
   * UUIDv4を生成
   * @returns {string} UUID v4形式のID
   */
  static uuid(): string {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, (c) => {
      const r = (Math.random() * 16) | 0;
      const v = c === 'x' ? r : (r & 0x3) | 0x8;
      return v.toString(16);
    });
  }
}

// 事前設定ジェネレーター
export const idGenerators = {
  pet: new IdGenerator('PET'),
  reservation: new IdGenerator('RES'),
  medical: new IdGenerator('MED'),
  vet: new IdGenerator('VET'),
  user: new IdGenerator('USR'),
};
