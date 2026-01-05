# MUSUBIX Ontology Reasoning MCP 要件定義書

**文書ID**: REQ-ONTO-001  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-05  
**ステータス**: Draft  
**準拠規格**: EARS（Easy Approach to Requirements Syntax）  
**ロードマップ参照**: Phase 3 - 学習・推論拡張

---

## 1. 概要

### 1.1 目的

OWL/RDFベースの形式オントロジーによる深い意味推論を実現するOntology Reasoning MCPサーバーを開発し、ソフトウェア開発ドメインの知識を構造化・推論する機能を提供する。

### 1.2 スコープ

- ドメインオントロジー定義
- 形式推論エンジン
- 一貫性検証
- SPARQLクエリサポート
- EARS要件とオントロジーのマッピング

### 1.3 技術スタック

| 技術 | 用途 | 備考 |
|------|------|------|
| OWL 2 RL | オントロジー言語 | 推論可能サブセット |
| N3.js | RDFパース・シリアライズ | TypeScriptネイティブ |
| rdflib.js | RDFグラフ操作 | ブラウザ/Node.js対応 |
| SPARQL.js | SPARQLパース | SPARQL 1.1対応 |
| Comunica | SPARQLクエリ実行 | モジュラー設計 |
| MCP Server SDK | サーバー実装 | @modelcontextprotocol/sdk |

---

## 2. 機能要件

### REQ-ONTO-001-F001: ドメインオントロジー定義

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN ユーザーがドメインオントロジーの定義を要求した時,  
THE システム SHALL 概念（クラス）の階層構造を定義可能にし,  
AND THE システム SHALL 関係（プロパティ）を定義可能にし,  
AND THE システム SHALL 公理（推論ルール）を定義可能にし,  
AND THE システム SHALL オントロジーをOWL形式で永続化する。

**検証方法**: ユニットテスト、統合テスト  
**受入基準**:
- [ ] クラス階層が定義できる
- [ ] ObjectProperty/DataPropertyが定義できる
- [ ] 推論ルール（公理）が設定できる
- [ ] OWL/RDF形式で保存される

**トレーサビリティ**: DES-ONTO-001, TSK-ONTO-001

---

### REQ-ONTO-001-F002: 含意推論

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN ファクト（トリプル）の集合とオントロジーIRIが与えられた時,  
THE システム SHALL OWL 2 RLルールに基づいて含意を推論し,  
AND THE システム SHALL 推論されたトリプルを返却し,  
AND THE システム SHALL 推論の証明木（説明）を生成する。

**検証方法**: ユニットテスト、統合テスト  
**受入基準**:
- [ ] 推移的関係が正しく推論される
- [ ] クラス継承が正しく推論される
- [ ] 証明木が生成される

**トレーサビリティ**: DES-ONTO-002, TSK-ONTO-002

---

### REQ-ONTO-001-F003: 一貫性検証

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN 知識ベースの一貫性検証が要求された時,  
THE システム SHALL オントロジー制約に対する違反を検出し,  
AND THE システム SHALL 矛盾するトリプルを識別し,  
AND THE システム SHALL 矛盾の理由を説明する。

**検証方法**: ユニットテスト  
**受入基準**:
- [ ] 不整合が検出される
- [ ] 矛盾トリプルが特定される
- [ ] 修正提案が生成される

**トレーサビリティ**: DES-ONTO-003, TSK-ONTO-003

---

### REQ-ONTO-001-F004: SPARQLクエリ

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN SPARQLクエリが与えられた時,  
THE システム SHALL SPARQL 1.1構文を解析し,  
AND THE システム SHALL オントロジーに対してクエリを実行し,  
AND THE システム SHALL 結果をJSON形式で返却する。

**検証方法**: ユニットテスト、統合テスト  
**受入基準**:
- [ ] SELECT/CONSTRUCT/ASKクエリが実行できる
- [ ] フィルター条件が正しく適用される
- [ ] 推論結果を含むクエリが可能

**トレーサビリティ**: DES-ONTO-004, TSK-ONTO-004

---

### REQ-ONTO-001-F005: EARS要件マッピング

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHEN EARS形式の要件が与えられた時,  
THE システム SHALL 要件をオントロジー概念にマッピングし,  
AND THE システム SHALL 関連する関係を識別し,  
AND THE システム SHALL マッピングできない要件を報告する。

**検証方法**: ユニットテスト、統合テスト  
**受入基準**:
- [ ] EARS要件がパースされる
- [ ] 概念へのマッピングが生成される
- [ ] 未マッピング要件が報告される

**トレーサビリティ**: DES-ONTO-005, TSK-ONTO-005

---

### REQ-ONTO-001-F006: オントロジーインポート

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHEN 外部オントロジーのインポートが要求された時,  
THE システム SHALL OWL/RDF/Turtle形式を読み込み,  
AND THE システム SHALL 名前空間を管理し,  
AND THE システム SHALL 既存オントロジーとマージする。

**検証方法**: ユニットテスト  
**受入基準**:
- [ ] OWL/RDF/Turtle形式が読み込める
- [ ] 名前空間の衝突が検出される
- [ ] マージが正しく行われる

**トレーサビリティ**: DES-ONTO-006, TSK-ONTO-006

---

### REQ-ONTO-001-F007: クエリエラーハンドリング

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHEN 無効なSPARQLクエリが与えられた時,  
THE システム SHALL 構文エラーの位置を特定し,  
AND THE システム SHALL エラーの種類と原因を説明し,  
AND THE システム SHALL 修正提案を生成する。

**検証方法**: ユニットテスト  
**受入基準**:
- [ ] 構文エラーが検出される
- [ ] エラー位置（行・列）が特定される
- [ ] 修正提案が生成される

**トレーサビリティ**: DES-ONTO-007, TSK-ONTO-007

---

### REQ-ONTO-001-F008: プライバシー保護

**種別**: UNWANTED  
**優先度**: P0（必須）

**要件**:  
THE システム SHALL NOT オントロジーデータを外部サーバーに送信し,  
AND THE システム SHALL NOT ユーザーの同意なく知識ベースを共有する。

**検証方法**: セキュリティレビュー  
**受入基準**:
- [ ] オントロジーがローカルストレージのみに保存される
- [ ] 外部通信がない

**トレーサビリティ**: DES-ONTO-008, TSK-ONTO-008

---

## 3. MCPツール仕様

### 3.1 define_domain_ontology

```typescript
{
  "name": "define_domain_ontology",
  "description": "ドメイン固有のオントロジーを定義",
  "inputSchema": {
    "type": "object",
    "properties": {
      "concepts": {
        "type": "array",
        "items": {
          "type": "object",
          "properties": {
            "name": { "type": "string" },
            "parent": { "type": "string" },
            "description": { "type": "string" }
          }
        }
      },
      "relations": {
        "type": "array",
        "items": {
          "type": "object",
          "properties": {
            "name": { "type": "string" },
            "domain": { "type": "string" },
            "range": { "type": "string" },
            "characteristics": { "type": "array" }
          }
        }
      },
      "axioms": {
        "type": "array",
        "items": { "type": "string" }
      }
    },
    "required": ["concepts"]
  },
  "outputSchema": {
    "type": "object",
    "properties": {
      "ontology_iri": { "type": "string" },
      "validation_result": { "type": "object" }
    }
  }
}
```

### 3.2 infer_implications

```typescript
{
  "name": "infer_implications",
  "description": "オントロジーから含意を推論",
  "inputSchema": {
    "type": "object",
    "properties": {
      "facts": {
        "type": "array",
        "items": {
          "type": "object",
          "properties": {
            "subject": { "type": "string" },
            "predicate": { "type": "string" },
            "object": { "type": "string" }
          }
        }
      },
      "ontology_iri": { "type": "string" }
    },
    "required": ["facts", "ontology_iri"]
  },
  "outputSchema": {
    "type": "object",
    "properties": {
      "inferred": { "type": "array" },
      "explanation": { "type": "object" }
    }
  }
}
```

### 3.3 check_consistency

```typescript
{
  "name": "check_consistency",
  "description": "知識ベースの一貫性をチェック",
  "inputSchema": {
    "type": "object",
    "properties": {
      "knowledge_base": { "type": "array" },
      "ontology_iri": { "type": "string" }
    },
    "required": ["knowledge_base", "ontology_iri"]
  },
  "outputSchema": {
    "type": "object",
    "properties": {
      "consistent": { "type": "boolean" },
      "conflicts": { "type": "array" }
    }
  }
}
```

### 3.4 query_knowledge

```typescript
{
  "name": "query_knowledge",
  "description": "SPARQLで知識をクエリ",
  "inputSchema": {
    "type": "object",
    "properties": {
      "sparql": { "type": "string" },
      "ontology_iri": { "type": "string" }
    },
    "required": ["sparql", "ontology_iri"]
  },
  "outputSchema": {
    "type": "object",
    "properties": {
      "results": { "type": "array" }
    }
  }
}
```

### 3.5 map_requirements_to_ontology

```typescript
{
  "name": "map_requirements_to_ontology",
  "description": "EARS要件をオントロジー概念にマッピング",
  "inputSchema": {
    "type": "object",
    "properties": {
      "ears_requirements": { "type": "array" },
      "ontology_iri": { "type": "string" }
    },
    "required": ["ears_requirements", "ontology_iri"]
  },
  "outputSchema": {
    "type": "object",
    "properties": {
      "mappings": { "type": "array" },
      "unmapped": { "type": "array" }
    }
  }
}
```

---

## 4. 非機能要件

### REQ-ONTO-001-NF001: パフォーマンス

**要件**:  
THE システム SHALL 10,000トリプルの知識ベースに対する推論を10秒以内に完了し,  
AND THE システム SHALL SPARQLクエリを1秒以内に実行する。

### REQ-ONTO-001-NF002: 標準準拠

**要件**:  
THE システム SHALL OWL 2 RL プロファイルに完全準拠し,  
AND THE システム SHALL SPARQL 1.1 Query仕様に準拠する。

### REQ-ONTO-001-NF003: 相互運用性

**要件**:  
THE システム SHALL 標準的なオントロジー形式（OWL, RDF, Turtle, JSON-LD）をサポートし,  
AND THE システム SHALL 既存オントロジー（Schema.org, Dublin Core等）をインポート可能にする。

---

## 5. 制約事項

- OWL 2 DL全体ではなくRL（ルールベース）サブセットのみサポート
- 大規模オントロジー（100万トリプル以上）は非サポート
- 分散推論は非サポート（単一ノード実行のみ）

---

## 6. 依存関係

| 依存先 | 種別 | 説明 |
|-------|------|------|
| REQ-SDD-ONTO-001 | 機能依存 | SDDオントロジーを使用 |
| REQ-SYMB-001 | 機能依存 | シンボリック推論との連携 |
| @apache-jena/jena | 外部ライブラリ | 推論エンジン |
| rdflib | 外部ライブラリ | RDF操作（Python代替） |

---

## 7. SDDオントロジープレビュー

```turtle
@prefix sdd: <http://musubix.dev/ontology/sdd#> .
@prefix ears: <http://musubix.dev/ontology/ears#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

# 概念階層
sdd:Requirement a owl:Class .
sdd:FunctionalRequirement rdfs:subClassOf sdd:Requirement .
sdd:NonFunctionalRequirement rdfs:subClassOf sdd:Requirement .

sdd:Design a owl:Class .
sdd:Component rdfs:subClassOf sdd:Design .
sdd:Interface rdfs:subClassOf sdd:Design .

sdd:Code a owl:Class .
sdd:Function rdfs:subClassOf sdd:Code .
sdd:Class rdfs:subClassOf sdd:Code .

sdd:Test a owl:Class .
sdd:UnitTest rdfs:subClassOf sdd:Test .
sdd:IntegrationTest rdfs:subClassOf sdd:Test .

# EARS形式クラス
ears:UbiquitousRequirement rdfs:subClassOf sdd:FunctionalRequirement .
ears:EventDrivenRequirement rdfs:subClassOf sdd:FunctionalRequirement .
ears:StateDrivenRequirement rdfs:subClassOf sdd:FunctionalRequirement .
ears:UnwantedRequirement rdfs:subClassOf sdd:NonFunctionalRequirement .
ears:OptionalRequirement rdfs:subClassOf sdd:FunctionalRequirement .

# 関係
sdd:implements a owl:ObjectProperty ;
    rdfs:domain sdd:Component ;
    rdfs:range sdd:Requirement .

sdd:dependsOn a owl:ObjectProperty, owl:TransitiveProperty ;
    rdfs:domain sdd:Component ;
    rdfs:range sdd:Component .

sdd:tests a owl:ObjectProperty ;
    rdfs:domain sdd:Test ;
    rdfs:range sdd:Code .

sdd:verifies a owl:ObjectProperty ;
    rdfs:domain sdd:Test ;
    rdfs:range sdd:Requirement .
```

---

## 8. 用語定義

| 用語 | 定義 |
|------|------|
| オントロジー | ドメイン知識の形式的表現 |
| トリプル | 主語-述語-目的語の3つ組 |
| OWL | Web Ontology Language |
| SPARQL | RDFデータのクエリ言語 |
| 推論 | 明示的ファクトから暗黙的ファクトを導出 |
| IRI | Internationalized Resource Identifier |

---

**文書履歴**:
| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|---------|--------|
| 1.0 | 2026-01-05 | 初版作成 | Claude |
