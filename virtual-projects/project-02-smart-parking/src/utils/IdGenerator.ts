/**
 * IdGenerator - ユニークID生成ユーティリティ
 * @design DES-PARKING-001
 */
export class IdGenerator {
  private counter = 0;

  constructor(private readonly prefix: string) {}

  generate(): string {
    this.counter++;
    return `${this.prefix}-${Date.now()}-${this.counter}`;
  }
}

const spaceGenerator = new IdGenerator('SPACE');
const entryGenerator = new IdGenerator('ENTRY');
const paymentGenerator = new IdGenerator('PAY');

export function generateSpaceId(): string {
  return spaceGenerator.generate();
}

export function generateEntryId(): string {
  return entryGenerator.generate();
}

export function generatePaymentId(): string {
  return paymentGenerator.generate();
}

export const idGenerators = {
  space: spaceGenerator,
  entry: entryGenerator,
  payment: paymentGenerator,
};
