# MUSUBIX SDDオントロジー構築 要件定義書

**文書ID**: REQ-SDD-ONTO-001  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-05  
**ステータス**: Draft  
**準拠規格**: EARS（Easy Approach to Requirements Syntax）  
**ロードマップ参照**: Phase 3 - 学習・推論拡張

---

## 1. 概要

### 1.1 目的

Software-Driven Development（SDD）ドメインの形式オントロジーを構築し、要件・設計・コード・テストの概念と関係を形式的に表現することで、知識ベースの推論と一貫性検証を可能にする。

### 1.2 スコープ

- SDDコア概念の定義（Requirement, Design, Code, Test）
- EARS形式の形式化
- トレーサビリティ関係の定義
- 9憲法条項の形式化
- 設計パターンの知識表現

### 1.3 オントロジー名前空間

| プレフィックス | IRI | 用途 |
|--------------|-----|------|
| `sdd:` | `http://musubix.dev/ontology/sdd#` | SDDコア概念 |
| `ears:` | `http://musubix.dev/ontology/ears#` | EARS形式 |
| `const:` | `http://musubix.dev/ontology/constitution#` | 9憲法条項 |
| `pattern:` | `http://musubix.dev/ontology/pattern#` | 設計パターン |

---

## 2. 機能要件

### REQ-SDD-ONTO-001-F001: コア概念階層

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
THE システム SHALL SDDのコア概念階層を定義し,  
AND THE システム SHALL Requirement, Design, Code, Testの4大概念を提供し,  
AND THE システム SHALL 各概念のサブクラスを定義し,  
AND THE システム SHALL 概念間の相互排他性・網羅性を保証する。

**概念階層**:
```
sdd:Artifact (抽象)
├── sdd:Requirement
│   ├── sdd:FunctionalRequirement
│   │   ├── ears:UbiquitousRequirement
│   │   ├── ears:EventDrivenRequirement
│   │   ├── ears:StateDrivenRequirement
│   │   └── ears:OptionalRequirement
│   └── sdd:NonFunctionalRequirement
│       ├── ears:UnwantedRequirement
│       ├── sdd:PerformanceRequirement
│       ├── sdd:SecurityRequirement
│       └── sdd:UsabilityRequirement
├── sdd:Design
│   ├── sdd:ArchitectureDesign
│   │   ├── sdd:C4Context
│   │   ├── sdd:C4Container
│   │   ├── sdd:C4Component
│   │   └── sdd:C4Code
│   └── sdd:DetailedDesign
│       ├── sdd:Interface
│       ├── sdd:DataModel
│       └── sdd:Algorithm
├── sdd:Code
│   ├── sdd:Module
│   ├── sdd:Class
│   ├── sdd:Function
│   └── sdd:Variable
└── sdd:Test
    ├── sdd:UnitTest
    ├── sdd:IntegrationTest
    ├── sdd:E2ETest
    └── sdd:SecurityTest
```

**検証方法**: オントロジーバリデーション  
**受入基準**:
- [ ] 4大概念が定義されている
- [ ] サブクラス階層が完全
- [ ] OWL構文として有効

**トレーサビリティ**: DES-SDD-ONTO-001, TSK-SDD-ONTO-001

---

### REQ-SDD-ONTO-001-F002: EARS形式の形式化

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
THE システム SHALL 5つのEARSパターンをオントロジークラスとして定義し,  
AND THE システム SHALL 各パターンの構成要素（トリガー、条件、アクション）をプロパティとして定義し,  
AND THE システム SHALL EARSテンプレートを検証ルールとして表現する。

**EARS形式定義**:
```turtle
ears:UbiquitousRequirement a owl:Class ;
    rdfs:subClassOf sdd:FunctionalRequirement ;
    rdfs:comment "THE [system] SHALL [requirement]" .

ears:EventDrivenRequirement a owl:Class ;
    rdfs:subClassOf sdd:FunctionalRequirement ;
    rdfs:comment "WHEN [trigger], THE [system] SHALL [response]" .

ears:StateDrivenRequirement a owl:Class ;
    rdfs:subClassOf sdd:FunctionalRequirement ;
    rdfs:comment "WHILE [state], THE [system] SHALL [response]" .

ears:UnwantedRequirement a owl:Class ;
    rdfs:subClassOf sdd:NonFunctionalRequirement ;
    rdfs:comment "THE [system] SHALL NOT [unwanted behavior]" .

ears:OptionalRequirement a owl:Class ;
    rdfs:subClassOf sdd:FunctionalRequirement ;
    rdfs:comment "IF [condition], THEN THE [system] SHALL [response]" .

# プロパティ
ears:hasTrigger a owl:DatatypeProperty ;
    rdfs:domain ears:EventDrivenRequirement ;
    rdfs:range xsd:string .

ears:hasState a owl:DatatypeProperty ;
    rdfs:domain ears:StateDrivenRequirement ;
    rdfs:range xsd:string .

ears:hasCondition a owl:DatatypeProperty ;
    rdfs:domain ears:OptionalRequirement ;
    rdfs:range xsd:string .

ears:hasResponse a owl:DatatypeProperty ;
    rdfs:domain sdd:FunctionalRequirement ;
    rdfs:range xsd:string .
```

**検証方法**: オントロジーバリデーション、EARS変換テスト  
**受入基準**:
- [ ] 5つのEARSパターンが定義されている
- [ ] 構成要素プロパティが完全
- [ ] 実際のEARS要件がインスタンス化できる

**トレーサビリティ**: DES-SDD-ONTO-002, TSK-SDD-ONTO-002

---

### REQ-SDD-ONTO-001-F003: トレーサビリティ関係

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
THE システム SHALL 要件↔設計↔コード↔テストのトレーサビリティ関係を定義し,  
AND THE システム SHALL 関係の特性（推移的、対称的等）を指定し,  
AND THE システム SHALL 逆関係を自動生成可能にする。

**トレーサビリティ関係**:
```turtle
# 順方向関係
sdd:designedBy a owl:ObjectProperty ;
    rdfs:domain sdd:Requirement ;
    rdfs:range sdd:Design ;
    owl:inverseOf sdd:implements .

sdd:implements a owl:ObjectProperty ;
    rdfs:domain sdd:Design ;
    rdfs:range sdd:Requirement .

sdd:codedBy a owl:ObjectProperty ;
    rdfs:domain sdd:Design ;
    rdfs:range sdd:Code ;
    owl:inverseOf sdd:realizes .

sdd:realizes a owl:ObjectProperty ;
    rdfs:domain sdd:Code ;
    rdfs:range sdd:Design .

sdd:testedBy a owl:ObjectProperty ;
    rdfs:domain sdd:Code ;
    rdfs:range sdd:Test ;
    owl:inverseOf sdd:tests .

sdd:tests a owl:ObjectProperty ;
    rdfs:domain sdd:Test ;
    rdfs:range sdd:Code .

sdd:verifies a owl:ObjectProperty ;
    rdfs:domain sdd:Test ;
    rdfs:range sdd:Requirement .

# 推移的関係
sdd:dependsOn a owl:ObjectProperty, owl:TransitiveProperty ;
    rdfs:domain sdd:Artifact ;
    rdfs:range sdd:Artifact .

# 完全トレーサビリティパス
sdd:tracesTo a owl:ObjectProperty, owl:TransitiveProperty ;
    rdfs:comment "任意のアーティファクト間のトレーサビリティ" .
```

**検証方法**: オントロジーバリデーション、推論テスト  
**受入基準**:
- [ ] 全トレーサビリティ関係が定義されている
- [ ] 逆関係が正しく推論される
- [ ] 推移的関係が正しく動作する

**トレーサビリティ**: DES-SDD-ONTO-003, TSK-SDD-ONTO-003

---

### REQ-SDD-ONTO-001-F004: 9憲法条項の形式化

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
THE システム SHALL 9憲法条項をオントロジー公理として形式化し,  
AND THE システム SHALL 各条項の違反条件を検出可能にし,  
AND THE システム SHALL 条項間の関係を定義する。

**憲法条項オントロジー**:
```turtle
const:ConstitutionArticle a owl:Class .

const:Article1_LibraryFirst a const:ConstitutionArticle ;
    const:articleNumber 1 ;
    const:name "Library-First Principle" ;
    const:description "機能は独立ライブラリとして開始" .

const:Article2_CLIInterface a const:ConstitutionArticle ;
    const:articleNumber 2 ;
    const:name "CLI Interface Mandate" ;
    const:description "すべてのライブラリはCLI公開必須" .

const:Article3_TestFirst a const:ConstitutionArticle ;
    const:articleNumber 3 ;
    const:name "Test-First Imperative" ;
    const:description "Red-Green-Blueサイクルでテスト先行" .

const:Article4_EARSFormat a const:ConstitutionArticle ;
    const:articleNumber 4 ;
    const:name "EARS Requirement Format" ;
    const:description "要件はEARS形式で記述" .

const:Article5_Traceability a const:ConstitutionArticle ;
    const:articleNumber 5 ;
    const:name "Complete Traceability" ;
    const:description "要件↔設計↔コード↔テストの100%追跡" .

const:Article6_ProjectMemory a const:ConstitutionArticle ;
    const:articleNumber 6 ;
    const:name "Project Memory Reference" ;
    const:description "steering/を参照してから決定" .

const:Article7_DesignPatterns a const:ConstitutionArticle ;
    const:articleNumber 7 ;
    const:name "Design Pattern Documentation" ;
    const:description "設計パターン適用の文書化" .

const:Article8_DecisionRecords a const:ConstitutionArticle ;
    const:articleNumber 8 ;
    const:name "ADR Requirement" ;
    const:description "すべての決定をADRで記録" .

const:Article9_QualityGates a const:ConstitutionArticle ;
    const:articleNumber 9 ;
    const:name "Quality Gate Enforcement" ;
    const:description "フェーズ移行前の品質検証" .

# 違反検出ルール（SWRL形式の概念）
const:violatesArticle a owl:ObjectProperty ;
    rdfs:domain sdd:Artifact ;
    rdfs:range const:ConstitutionArticle .
```

**検証方法**: オントロジーバリデーション、違反検出テスト  
**受入基準**:
- [ ] 9条項すべてが形式化されている
- [ ] 違反条件が定義されている
- [ ] 違反検出クエリが動作する

**トレーサビリティ**: DES-SDD-ONTO-004, TSK-SDD-ONTO-004

---

### REQ-SDD-ONTO-001-F005: 設計パターンの知識表現

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
THE システム SHALL GoF設計パターンをオントロジークラスとして定義し,  
AND THE システム SHALL パターンの構成要素（参加者、関係）を表現し,  
AND THE システム SHALL パターン適用のコンテキストを記述可能にする。

**設計パターンオントロジー**:
```turtle
pattern:DesignPattern a owl:Class .

# 生成パターン
pattern:CreationalPattern rdfs:subClassOf pattern:DesignPattern .
pattern:Factory rdfs:subClassOf pattern:CreationalPattern .
pattern:Singleton rdfs:subClassOf pattern:CreationalPattern .
pattern:Builder rdfs:subClassOf pattern:CreationalPattern .

# 構造パターン
pattern:StructuralPattern rdfs:subClassOf pattern:DesignPattern .
pattern:Adapter rdfs:subClassOf pattern:StructuralPattern .
pattern:Decorator rdfs:subClassOf pattern:StructuralPattern .
pattern:Repository rdfs:subClassOf pattern:StructuralPattern .

# 振る舞いパターン
pattern:BehavioralPattern rdfs:subClassOf pattern:DesignPattern .
pattern:Strategy rdfs:subClassOf pattern:BehavioralPattern .
pattern:Observer rdfs:subClassOf pattern:BehavioralPattern .
pattern:Command rdfs:subClassOf pattern:BehavioralPattern .

# パターン適用
pattern:appliesPattern a owl:ObjectProperty ;
    rdfs:domain sdd:Design ;
    rdfs:range pattern:DesignPattern .

pattern:hasParticipant a owl:ObjectProperty ;
    rdfs:domain pattern:DesignPattern ;
    rdfs:range sdd:Code .
```

**検証方法**: オントロジーバリデーション  
**受入基準**:
- [ ] 主要設計パターンが定義されている
- [ ] パターン適用が記録できる
- [ ] パターン検出クエリが動作する

**トレーサビリティ**: DES-SDD-ONTO-005, TSK-SDD-ONTO-005

---

### REQ-SDD-ONTO-001-F006: 推論ルールの定義

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
THE システム SHALL OWL 2 RL推論ルールを定義し,  
AND THE システム SHALL 暗黙的関係の推論を可能にし,  
AND THE システム SHALL 制約違反の検出ルールを提供する。

**推論ルール例**:
```turtle
# ルール1: テストがコードをテストし、コードが設計を実現し、設計が要件を実装する場合、
#          テストは要件を検証する
# OWL 2 RLでの表現（プロパティチェーン）
sdd:verifies owl:propertyChainAxiom (sdd:tests sdd:realizes sdd:implements) .

# ルール2: 未テストコードの検出（SPARQLルール）
# SELECT ?code WHERE {
#   ?code a sdd:Code .
#   FILTER NOT EXISTS { ?test sdd:tests ?code }
# }

# ルール3: トレーサビリティ不完全の検出
# SELECT ?req WHERE {
#   ?req a sdd:Requirement .
#   FILTER NOT EXISTS { ?test sdd:verifies ?req }
# }
```

**検証方法**: 推論テスト、クエリテスト  
**受入基準**:
- [ ] プロパティチェーン推論が動作する
- [ ] 違反検出クエリが正しく動作する

**トレーサビリティ**: DES-SDD-ONTO-006, TSK-SDD-ONTO-006

---

## 3. 完全オントロジー仕様

### 3.1 SDDオントロジー全体（Turtle形式）

```turtle
@prefix sdd: <http://musubix.dev/ontology/sdd#> .
@prefix ears: <http://musubix.dev/ontology/ears#> .
@prefix const: <http://musubix.dev/ontology/constitution#> .
@prefix pattern: <http://musubix.dev/ontology/pattern#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .

# オントロジーメタデータ
<http://musubix.dev/ontology/sdd> a owl:Ontology ;
    rdfs:label "MUSUBIX SDD Ontology" ;
    rdfs:comment "Software-Driven Development のための形式オントロジー" ;
    owl:versionInfo "1.0.0" .

# ===================
# コア概念
# ===================

sdd:Artifact a owl:Class ;
    rdfs:label "Artifact" ;
    rdfs:comment "SDD成果物の抽象基底クラス" .

sdd:Requirement a owl:Class ;
    rdfs:subClassOf sdd:Artifact ;
    rdfs:label "Requirement" .

sdd:Design a owl:Class ;
    rdfs:subClassOf sdd:Artifact ;
    rdfs:label "Design" .

sdd:Code a owl:Class ;
    rdfs:subClassOf sdd:Artifact ;
    rdfs:label "Code" .

sdd:Test a owl:Class ;
    rdfs:subClassOf sdd:Artifact ;
    rdfs:label "Test" .

# ===================
# 共通プロパティ
# ===================

sdd:hasId a owl:DatatypeProperty, owl:FunctionalProperty ;
    rdfs:domain sdd:Artifact ;
    rdfs:range xsd:string .

sdd:hasVersion a owl:DatatypeProperty ;
    rdfs:domain sdd:Artifact ;
    rdfs:range xsd:string .

sdd:createdAt a owl:DatatypeProperty ;
    rdfs:domain sdd:Artifact ;
    rdfs:range xsd:dateTime .

sdd:modifiedAt a owl:DatatypeProperty ;
    rdfs:domain sdd:Artifact ;
    rdfs:range xsd:dateTime .

sdd:hasPriority a owl:DatatypeProperty ;
    rdfs:domain sdd:Requirement ;
    rdfs:range xsd:string .

# ===================
# トレーサビリティ関係
# ===================

sdd:implements a owl:ObjectProperty ;
    rdfs:domain sdd:Design ;
    rdfs:range sdd:Requirement ;
    owl:inverseOf sdd:implementedBy .

sdd:implementedBy a owl:ObjectProperty ;
    rdfs:domain sdd:Requirement ;
    rdfs:range sdd:Design .

sdd:realizes a owl:ObjectProperty ;
    rdfs:domain sdd:Code ;
    rdfs:range sdd:Design ;
    owl:inverseOf sdd:realizedBy .

sdd:realizedBy a owl:ObjectProperty ;
    rdfs:domain sdd:Design ;
    rdfs:range sdd:Code .

sdd:tests a owl:ObjectProperty ;
    rdfs:domain sdd:Test ;
    rdfs:range sdd:Code ;
    owl:inverseOf sdd:testedBy .

sdd:testedBy a owl:ObjectProperty ;
    rdfs:domain sdd:Code ;
    rdfs:range sdd:Test .

sdd:verifies a owl:ObjectProperty ;
    rdfs:domain sdd:Test ;
    rdfs:range sdd:Requirement ;
    owl:propertyChainAxiom (sdd:tests sdd:realizes sdd:implements) .

sdd:dependsOn a owl:ObjectProperty, owl:TransitiveProperty ;
    rdfs:domain sdd:Artifact ;
    rdfs:range sdd:Artifact .
```

---

## 4. 非機能要件

### REQ-SDD-ONTO-001-NF001: 標準準拠

**要件**:  
THE システム SHALL OWL 2 RL プロファイルに完全準拠し,  
AND THE システム SHALL W3C RDF/OWL標準に準拠する。

### REQ-SDD-ONTO-001-NF002: 拡張性

**要件**:  
THE システム SHALL カスタム概念・関係の追加を許可し,  
AND THE システム SHALL 外部オントロジーのインポートをサポートする。

### REQ-SDD-ONTO-001-NF003: ドキュメント

**要件**:  
THE システム SHALL すべての概念・関係にrdfs:labelとrdfs:commentを提供し,  
AND THE システム SHALL オントロジーのHTML ドキュメントを生成可能にする。

### REQ-SDD-ONTO-001-NF004: バージョン管理

**要件**:  
THE システム SHALL オントロジーにセマンティックバージョニング（MAJOR.MINOR.PATCH）を適用し,  
AND THE システム SHALL 後方互換性のある変更はMINOR、破壊的変更はMAJORでバージョンアップし,  
AND THE システム SHALL owl:versionInfoとowl:priorVersionで履歴を追跡する。

### REQ-SDD-ONTO-001-NF005: 国際化（i18n）

**要件**:  
THE システム SHALL rdfs:labelに言語タグ（@en, @ja）を付与し,  
AND THE システム SHALL 日本語ラベルを別ファイル（sdd-ontology-ja.ttl）で管理し,  
AND THE システム SHALL クエリ時に言語フィルタリングをサポートする。

---

## 5. 制約事項

- OWL 2 DL全体ではなくRLプロファイルのみ
- 日本語ラベルは別途i18nファイルで管理（sdd-ontology-ja.ttl）
- 推論エンジンはN3.js + カスタムOWL-RLルールを想定

---

### REQ-SDD-ONTO-001-NF006: オントロジー整合性

**種別**: UNWANTED  
**優先度**: P0（必須）

**要件**:  
THE システム SHALL NOT 矛盾する公理を定義し,  
AND THE システム SHALL NOT 循環参照を含むクラス階層を許可し,  
AND THE システム SHALL NOT 未定義の概念への参照を許可する。

**検証方法**: オントロジーバリデーション  
**受入基準**:
- [ ] OWLバリデータでエラーがない
- [ ] 循環参照検出が動作する
- [ ] 未定義参照検出が動作する

---

## 6. 依存関係

| 依存先 | 種別 | 説明 |
|-------|------|------|
| REQ-ONTO-001 | 機能依存 | オントロジー推論MCPで使用 |
| OWL 2 RL | 標準仕様 | 推論可能サブセット |
| SPARQL 1.1 | 標準仕様 | クエリ言語 |

---

## 7. 用語定義

| 用語 | 定義 |
|------|------|
| SDD | Software-Driven Development |
| オントロジー | ドメイン知識の形式的表現 |
| OWL | Web Ontology Language |
| Turtle | RDFのシリアライゼーション形式 |
| プロパティチェーン | 複数の関係を連鎖させた推論ルール |
| OWL 2 RL | ルールベース推論可能なOWLサブセット |

---

## 8. SPARQLクエリ例

### 8.1 未検証要件の検出

```sparql
PREFIX sdd: <http://musubix.dev/ontology/sdd#>

SELECT ?req ?reqId
WHERE {
  ?req a sdd:Requirement ;
       sdd:hasId ?reqId .
  FILTER NOT EXISTS {
    ?test sdd:verifies ?req .
  }
}
```

### 8.2 トレーサビリティパスの取得

```sparql
PREFIX sdd: <http://musubix.dev/ontology/sdd#>

SELECT ?req ?design ?code ?test
WHERE {
  ?req a sdd:Requirement .
  ?design sdd:implements ?req .
  ?code sdd:realizes ?design .
  ?test sdd:tests ?code .
}
```

### 8.3 憲法条項違反の検出

```sparql
PREFIX sdd: <http://musubix.dev/ontology/sdd#>
PREFIX const: <http://musubix.dev/ontology/constitution#>

SELECT ?artifact ?article ?articleName
WHERE {
  ?artifact const:violatesArticle ?article .
  ?article const:name ?articleName .
}
```

---

**文書履歴**:
| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|---------|--------|
| 1.0 | 2026-01-05 | 初版作成 | Claude |
