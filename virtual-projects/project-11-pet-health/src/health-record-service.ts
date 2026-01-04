// PetCare - 健康記録サービス実装
// REQ-PET-001-03, REQ-PET-001-04 対応

import {
  HealthRecord,
  HealthRecordInput,
  WeightAlert,
  QueryOptions,
  TEMPERATURE_MIN,
  TEMPERATURE_MAX,
  WEIGHT_CHANGE_ALERT_THRESHOLD,
} from './types';

// IdGenerator パターン
class HealthRecordIdGenerator {
  private counter = 0;

  generate(): string {
    const timestamp = Date.now();
    this.counter++;
    return `HR-${timestamp}-${this.counter}`;
  }
}

// リポジトリインターフェース
export interface IHealthRecordRepository {
  save(record: HealthRecord): Promise<HealthRecord>;
  findByPetId(petId: string, options?: QueryOptions): Promise<HealthRecord[]>;
  findLatestByPetId(petId: string): Promise<HealthRecord | null>;
}

// インメモリリポジトリ実装
export class InMemoryHealthRecordRepository implements IHealthRecordRepository {
  private records: Map<string, HealthRecord> = new Map();

  async save(record: HealthRecord): Promise<HealthRecord> {
    this.records.set(record.id, record);
    return record;
  }

  async findByPetId(petId: string, options?: QueryOptions): Promise<HealthRecord[]> {
    let results = Array.from(this.records.values())
      .filter((r) => r.petId === petId)
      .sort((a, b) => b.recordedAt.getTime() - a.recordedAt.getTime());

    if (options?.startDate) {
      results = results.filter((r) => r.recordedAt >= options.startDate!);
    }
    if (options?.endDate) {
      results = results.filter((r) => r.recordedAt <= options.endDate!);
    }
    if (options?.limit) {
      results = results.slice(0, options.limit);
    }

    return results;
  }

  async findLatestByPetId(petId: string): Promise<HealthRecord | null> {
    const records = await this.findByPetId(petId, { limit: 1 });
    return records[0] || null;
  }

  clear(): void {
    this.records.clear();
  }
}

// 健康アラートサービス
export class HealthAlertService {
  /**
   * 体重変動をチェック
   * REQ-PET-001-04: WHILE ペットの体重が前回記録から10%以上変動している状態
   *                 THE システム SHALL オーナーに健康アラートを通知すること
   */
  checkWeightChange(
    petId: string,
    petName: string,
    previousWeight: number,
    currentWeight: number
  ): WeightAlert | null {
    if (previousWeight <= 0) return null;

    const changePercent = Math.abs(currentWeight - previousWeight) / previousWeight;

    if (changePercent >= WEIGHT_CHANGE_ALERT_THRESHOLD) {
      return {
        petId,
        petName,
        previousWeight,
        currentWeight,
        changePercent,
        alertType: currentWeight > previousWeight ? 'increase' : 'decrease',
        createdAt: new Date(),
      };
    }

    return null;
  }
}

// 健康記録サービス
export class HealthRecordService {
  private idGenerator = new HealthRecordIdGenerator();
  private alertService = new HealthAlertService();

  constructor(private repository: IHealthRecordRepository) {}

  /**
   * 健康記録を作成
   * REQ-PET-001-03: WHEN オーナーまたはスタッフが健康記録を入力する
   *                 THE システム SHALL 日時、体重、体温、症状、メモを記録すること
   */
  async create(
    petId: string,
    petName: string,
    input: HealthRecordInput,
    recordedBy: string
  ): Promise<{ record: HealthRecord; alert: WeightAlert | null }> {
    // バリデーション
    if (input.weight <= 0) {
      throw new Error('Weight must be greater than 0');
    }

    if (input.temperature !== undefined) {
      if (input.temperature < TEMPERATURE_MIN || input.temperature > TEMPERATURE_MAX) {
        throw new Error(`Temperature must be between ${TEMPERATURE_MIN} and ${TEMPERATURE_MAX}`);
      }
    }

    const now = new Date();
    const record: HealthRecord = {
      id: this.idGenerator.generate(),
      petId,
      recordedAt: input.recordedAt || now,
      weight: input.weight,
      temperature: input.temperature,
      symptoms: input.symptoms || [],
      notes: input.notes,
      recordedBy,
      createdAt: now,
    };

    const savedRecord = await this.repository.save(record);

    // 前回記録との比較でアラートチェック
    const previousRecord = await this.repository.findLatestByPetId(petId);
    let alert: WeightAlert | null = null;

    if (previousRecord && previousRecord.id !== savedRecord.id) {
      alert = this.alertService.checkWeightChange(
        petId,
        petName,
        previousRecord.weight,
        input.weight
      );
    }

    return { record: savedRecord, alert };
  }

  /**
   * 健康記録履歴を取得
   */
  async getHistory(petId: string, options?: QueryOptions): Promise<HealthRecord[]> {
    return this.repository.findByPetId(petId, options);
  }

  /**
   * 最新の健康記録を取得
   */
  async getLatest(petId: string): Promise<HealthRecord | null> {
    return this.repository.findLatestByPetId(petId);
  }
}
