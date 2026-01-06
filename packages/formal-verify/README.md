# @nahisaho/musubix-formal-verify

MUSUBIX v1.7.5 Formal Verification Edition - 形式検証ツールパッケージ

## 概要

Z3ソルバー統合、事前条件/事後条件検証、EARS→SMT変換、トレーサビリティDBを提供します。

## インストール

```bash
npm install @nahisaho/musubix-formal-verify
```

## 機能

### Z3統合

```typescript
import { Z3Adapter } from '@nahisaho/musubix-formal-verify/z3';

const z3 = await Z3Adapter.create();
const result = await z3.checkSat('(declare-const x Int) (assert (> x 0))');
console.log(result); // 'sat' | 'unsat' | 'unknown'
```

### 事前条件/事後条件検証

```typescript
import { PreconditionVerifier, PostconditionVerifier } from '@nahisaho/musubix-formal-verify/verifiers';

const preVerifier = new PreconditionVerifier(z3);
const result = await preVerifier.verify({
  condition: 'amount > 0 && amount <= balance',
  variables: { amount: 'Int', balance: 'Int' }
});
```

### EARS→SMT変換

```typescript
import { EarsToSmtConverter } from '@nahisaho/musubix-formal-verify/converters';

const converter = new EarsToSmtConverter();
const smt = converter.convert('WHEN user clicks submit, THE system SHALL save the data');
```

### トレーサビリティDB

```typescript
import { TraceabilityDB, ImpactAnalyzer } from '@nahisaho/musubix-formal-verify/traceability';

const db = new TraceabilityDB('./trace.db');
await db.addLink({ source: 'REQ-001', target: 'DES-001', type: 'implements' });

const analyzer = new ImpactAnalyzer(db);
const impact = await analyzer.analyze('REQ-001');
```

## ライセンス

MIT
