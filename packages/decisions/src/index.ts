/**
 * @musubix/decisions - ADR Manager
 * 
 * Architecture Decision Records management for MUSUBIX v3.0
 * 
 * @packageDocumentation
 */

// ============================================================
// ADR Types
// ============================================================

/**
 * ADR status
 */
export type ADRStatus = 'proposed' | 'accepted' | 'deprecated' | 'superseded';

/**
 * ADR draft for creation
 */
export interface ADRDraft {
  title: string;
  context: string;
  decision: string;
  rationale?: string;
  alternatives?: string[];
  consequences?: string[];
  relatedRequirements?: string[];
  decider?: string;
}

/**
 * ADR filter
 */
export interface ADRFilter {
  status?: ADRStatus;
  keyword?: string;
}

/**
 * Architecture Decision Record
 */
export interface ADR {
  /** ID (e.g., "0001") */
  id: string;
  /** Title */
  title: string;
  /** Status */
  status: ADRStatus;
  /** Date (YYYY-MM-DD) */
  date: string;
  /** Person who made the decision */
  decider: string;
  /** Context/background */
  context: string;
  /** The decision made */
  decision: string;
  /** Rationale for the decision */
  rationale: string;
  /** Alternatives considered */
  alternatives: string[];
  /** Consequences of the decision */
  consequences: string[];
  /** Related requirement IDs */
  relatedRequirements: string[];
  /** Related ADR IDs */
  relatedADRs: string[];
}

// ============================================================
// Decision Manager Interface
// ============================================================

/**
 * Decision manager interface
 */
export interface IDecisionManager {
  create(draft: ADRDraft): Promise<ADR>;
  get(id: string): Promise<ADR | undefined>;
  list(filter?: ADRFilter): Promise<ADR[]>;
  update(id: string, updates: Partial<ADR>): Promise<ADR>;
  accept(id: string): Promise<ADR>;
  deprecate(id: string, supersededBy?: string): Promise<ADR>;
  generateIndex(): Promise<void>;
  search(query: string): Promise<ADR[]>;
  findByRequirement(reqId: string): Promise<ADR[]>;
}

// ============================================================
// Factory Function
// ============================================================

/**
 * Create a new decision manager
 */
export function createDecisionManager(basePath: string): IDecisionManager {
  return new DecisionManager(basePath);
}

// ============================================================
// Implementation
// ============================================================

import * as fs from 'node:fs/promises';
import * as path from 'node:path';

/**
 * Decision manager implementation
 */
export class DecisionManager implements IDecisionManager {
  private basePath: string;
  private adrs: Map<string, ADR> = new Map();
  private loaded: boolean = false;

  constructor(basePath: string) {
    this.basePath = basePath;
  }

  private getNextId(): string {
    const ids = Array.from(this.adrs.keys())
      .map(id => parseInt(id, 10))
      .filter(n => !isNaN(n));
    const maxId = ids.length > 0 ? Math.max(...ids) : 0;
    return String(maxId + 1).padStart(4, '0');
  }

  private getFilePath(id: string, title: string): string {
    const slug = title
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, '-')
      .replace(/^-|-$/g, '');
    return path.join(this.basePath, `${id}-${slug}.md`);
  }

  private formatADR(adr: ADR): string {
    return `# ADR-${adr.id}: ${adr.title}

| 項目 | 内容 |
|------|------|
| **ステータス** | ${adr.status.charAt(0).toUpperCase() + adr.status.slice(1)} |
| **日付** | ${adr.date} |
| **決定者** | ${adr.decider} |
| **関連要件** | ${adr.relatedRequirements.join(', ') || '-'} |

## コンテキスト

${adr.context}

## 決定

${adr.decision}

## 理由

${adr.rationale}

## 代替案

${adr.alternatives.length > 0 ? adr.alternatives.map(a => `- ${a}`).join('\n') : '- なし'}

## 影響

${adr.consequences.length > 0 ? adr.consequences.map(c => `- ${c}`).join('\n') : '- なし'}

## 関連

${adr.relatedADRs.length > 0 ? adr.relatedADRs.map(r => `- [ADR-${r}](./${r}-*.md)`).join('\n') : '- なし'}
`;
  }

  private parseADR(content: string, filePath: string): ADR | null {
    const fileName = path.basename(filePath, '.md');
    const idMatch = fileName.match(/^(\d{4})-/);
    if (!idMatch) return null;
    const id = idMatch[1];

    const titleMatch = content.match(/^# ADR-\d{4}: (.+)$/m);
    const statusMatch = content.match(/\*\*ステータス\*\*\s*\|\s*(\w+)/);
    const dateMatch = content.match(/\*\*日付\*\*\s*\|\s*(\d{4}-\d{2}-\d{2})/);
    const deciderMatch = content.match(/\*\*決定者\*\*\s*\|\s*(.+?)\s*\|/);
    const reqMatch = content.match(/\*\*関連要件\*\*\s*\|\s*(.+?)\s*\|/);

    const contextMatch = content.match(/## コンテキスト\n\n([\s\S]*?)(?=\n## )/);
    const decisionMatch = content.match(/## 決定\n\n([\s\S]*?)(?=\n## )/);
    const rationaleMatch = content.match(/## 理由\n\n([\s\S]*?)(?=\n## )/);
    const alternativesMatch = content.match(/## 代替案\n\n([\s\S]*?)(?=\n## )/);
    const consequencesMatch = content.match(/## 影響\n\n([\s\S]*?)(?=\n## |$)/);

    const parseList = (text?: string): string[] => {
      if (!text) return [];
      return text
        .split('\n')
        .filter(line => line.startsWith('- '))
        .map(line => line.slice(2).trim())
        .filter(item => item !== 'なし');
    };

    return {
      id,
      title: titleMatch?.[1] ?? '',
      status: (statusMatch?.[1]?.toLowerCase() as ADRStatus) ?? 'proposed',
      date: dateMatch?.[1] ?? new Date().toISOString().slice(0, 10),
      decider: deciderMatch?.[1]?.trim() ?? '',
      context: contextMatch?.[1]?.trim() ?? '',
      decision: decisionMatch?.[1]?.trim() ?? '',
      rationale: rationaleMatch?.[1]?.trim() ?? '',
      alternatives: parseList(alternativesMatch?.[1]),
      consequences: parseList(consequencesMatch?.[1]),
      relatedRequirements: reqMatch?.[1] !== '-' ? reqMatch?.[1]?.split(',').map(s => s.trim()) ?? [] : [],
      relatedADRs: [],
    };
  }

  private async loadAll(): Promise<void> {
    if (this.loaded) return;

    try {
      const files = await fs.readdir(this.basePath);
      for (const file of files) {
        if (file.endsWith('.md') && /^\d{4}-/.test(file)) {
          const content = await fs.readFile(path.join(this.basePath, file), 'utf-8');
          const adr = this.parseADR(content, file);
          if (adr) {
            this.adrs.set(adr.id, adr);
          }
        }
      }
      this.loaded = true;
    } catch {
      // Directory doesn't exist
      this.loaded = true;
    }
  }

  async create(draft: ADRDraft): Promise<ADR> {
    await this.loadAll();
    await fs.mkdir(this.basePath, { recursive: true });

    const id = this.getNextId();
    const adr: ADR = {
      id,
      title: draft.title,
      status: 'proposed',
      date: new Date().toISOString().slice(0, 10),
      decider: draft.decider ?? 'Unknown',
      context: draft.context,
      decision: draft.decision,
      rationale: draft.rationale ?? '',
      alternatives: draft.alternatives ?? [],
      consequences: draft.consequences ?? [],
      relatedRequirements: draft.relatedRequirements ?? [],
      relatedADRs: [],
    };

    const filePath = this.getFilePath(id, draft.title);
    await fs.writeFile(filePath, this.formatADR(adr), 'utf-8');
    this.adrs.set(id, adr);

    return adr;
  }

  async get(id: string): Promise<ADR | undefined> {
    await this.loadAll();
    return this.adrs.get(id);
  }

  async list(filter?: ADRFilter): Promise<ADR[]> {
    await this.loadAll();

    let results = Array.from(this.adrs.values());

    if (filter?.status) {
      results = results.filter(adr => adr.status === filter.status);
    }

    if (filter?.keyword) {
      const keyword = filter.keyword.toLowerCase();
      results = results.filter(
        adr =>
          adr.title.toLowerCase().includes(keyword) ||
          adr.context.toLowerCase().includes(keyword) ||
          adr.decision.toLowerCase().includes(keyword)
      );
    }

    return results.sort((a, b) => a.id.localeCompare(b.id));
  }

  async update(id: string, updates: Partial<ADR>): Promise<ADR> {
    await this.loadAll();

    const adr = this.adrs.get(id);
    if (!adr) {
      throw new Error(`ADR not found: ${id}`);
    }

    const updated: ADR = { ...adr, ...updates, id: adr.id };
    const filePath = this.getFilePath(id, updated.title);
    await fs.writeFile(filePath, this.formatADR(updated), 'utf-8');
    this.adrs.set(id, updated);

    return updated;
  }

  async accept(id: string): Promise<ADR> {
    return this.update(id, { status: 'accepted' });
  }

  async deprecate(id: string, supersededBy?: string): Promise<ADR> {
    const updates: Partial<ADR> = {
      status: supersededBy ? 'superseded' : 'deprecated',
    };

    if (supersededBy) {
      const adr = await this.get(id);
      if (adr) {
        updates.relatedADRs = [...adr.relatedADRs, supersededBy];
      }
    }

    return this.update(id, updates);
  }

  async generateIndex(): Promise<void> {
    await this.loadAll();
    await fs.mkdir(this.basePath, { recursive: true });

    const adrs = await this.list();
    const byStatus: Record<ADRStatus, ADR[]> = {
      proposed: [],
      accepted: [],
      deprecated: [],
      superseded: [],
    };

    for (const adr of adrs) {
      byStatus[adr.status].push(adr);
    }

    const content = `# Architecture Decision Records

このディレクトリには、プロジェクトのアーキテクチャ決定記録（ADR）が含まれています。

## 概要

| ステータス | 件数 |
|-----------|------|
| Accepted | ${byStatus.accepted.length} |
| Proposed | ${byStatus.proposed.length} |
| Deprecated | ${byStatus.deprecated.length} |
| Superseded | ${byStatus.superseded.length} |

## Accepted

${byStatus.accepted.length > 0 
  ? byStatus.accepted.map(a => `- [ADR-${a.id}: ${a.title}](./${a.id}-${a.title.toLowerCase().replace(/[^a-z0-9]+/g, '-')}.md)`).join('\n')
  : '- なし'}

## Proposed

${byStatus.proposed.length > 0 
  ? byStatus.proposed.map(a => `- [ADR-${a.id}: ${a.title}](./${a.id}-${a.title.toLowerCase().replace(/[^a-z0-9]+/g, '-')}.md)`).join('\n')
  : '- なし'}

## Deprecated / Superseded

${[...byStatus.deprecated, ...byStatus.superseded].length > 0 
  ? [...byStatus.deprecated, ...byStatus.superseded].map(a => `- [ADR-${a.id}: ${a.title}](./${a.id}-${a.title.toLowerCase().replace(/[^a-z0-9]+/g, '-')}.md) (${a.status})`).join('\n')
  : '- なし'}
`;

    await fs.writeFile(path.join(this.basePath, 'index.md'), content, 'utf-8');
  }

  async search(query: string): Promise<ADR[]> {
    return this.list({ keyword: query });
  }

  async findByRequirement(reqId: string): Promise<ADR[]> {
    await this.loadAll();
    return Array.from(this.adrs.values()).filter(adr =>
      adr.relatedRequirements.includes(reqId)
    );
  }
}

// ============================================================
// Template
// ============================================================

/**
 * ADR template content
 */
export const ADR_TEMPLATE = `# ADR-NNNN: タイトル

| 項目 | 内容 |
|------|------|
| **ステータス** | Proposed |
| **日付** | YYYY-MM-DD |
| **決定者** | 名前 |
| **関連要件** | REQ-XXX-NNN |

## コンテキスト

[決定が必要になった背景・問題]

## 決定

[採用した解決策]

## 理由

[なぜこの決定に至ったか]

## 代替案

- [検討したが採用しなかった案1]
- [検討したが採用しなかった案2]

## 影響

- [この決定による影響1]
- [この決定によるトレードオフ]

## 関連

- [関連ADR](./NNNN-title.md)
- [関連要件](../specs/REQ-XXX.md)
`;
