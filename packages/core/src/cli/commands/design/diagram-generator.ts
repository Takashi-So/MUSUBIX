/**
 * Diagram Generator
 *
 * Generates Mermaid, PlantUML, and Markdown design documents
 *
 * @packageDocumentation
 * @module cli/commands/design/diagram-generator
 */

import type { C4Model, DesignPattern, ADRDocument } from './types.js';

/**
 * Generate Mermaid diagram with enhanced formatting
 */
export function generateMermaidDiagram(model: C4Model): string {
  const componentNames = model.elements
    .filter(e => e.type !== 'person')
    .slice(0, 3)
    .map(e => e.name);
  const titleSuffix = componentNames.length > 0 ? ` - ${componentNames.join(', ')}${model.elements.length > 4 ? '...' : ''}` : '';
  const diagramTitle = `${model.level.charAt(0).toUpperCase() + model.level.slice(1)} Diagram${titleSuffix}`;

  let diagram = `---\ntitle: ${diagramTitle}\n---\nflowchart TD\n`;

  const persons = model.elements.filter(e => e.type === 'person');
  const systems = model.elements.filter(e => e.type === 'software_system');
  const containers = model.elements.filter(e => e.type === 'container');
  const components = model.elements.filter(e => e.type === 'component');

  diagram += `\n  %% Styling\n`;
  diagram += `  classDef person fill:#08427b,stroke:#052e56,color:#fff\n`;
  diagram += `  classDef system fill:#1168bd,stroke:#0b4884,color:#fff\n`;
  diagram += `  classDef container fill:#438dd5,stroke:#2e6295,color:#fff\n`;
  diagram += `  classDef component fill:#85bbf0,stroke:#5d82a8,color:#000\n`;
  diagram += `\n`;

  if (persons.length > 0) {
    diagram += `  subgraph Actors["👤 Actors"]\n`;
    for (const person of persons) {
      diagram += `    ${person.id}(["${person.name}"])\n`;
    }
    diagram += `  end\n\n`;
  }

  const nonPersonElements = [...systems, ...containers, ...components];

  if (nonPersonElements.length > 0) {
    if (systems.length > 0 && (containers.length > 0 || components.length > 0)) {
      diagram += `  subgraph Systems["🖥️ External Systems"]\n`;
      for (const sys of systems) {
        diagram += `    ${sys.id}["${sys.name}<br/><small>${sys.description || ''}</small>"]\n`;
      }
      diagram += `  end\n\n`;
    } else {
      for (const sys of systems) {
        diagram += `  ${sys.id}["${sys.name}<br/><small>${sys.description || ''}</small>"]\n`;
      }
    }

    if (containers.length > 0) {
      diagram += `  subgraph Containers["📦 Containers"]\n`;
      for (const container of containers) {
        const tech = container.technology ? `[${container.technology}]` : '';
        diagram += `    ${container.id}[["${container.name}${tech}<br/><small>${container.description || ''}</small>"]]\n`;
      }
      diagram += `  end\n\n`;
    }

    if (components.length > 0) {
      const services = components.filter(c => c.name.includes('Service'));
      const repositories = components.filter(c => c.name.includes('Repository') || c.name.includes('Data'));
      const managers = components.filter(c => c.name.includes('Manager'));
      const others = components.filter(c =>
        !c.name.includes('Service') &&
        !c.name.includes('Repository') &&
        !c.name.includes('Data') &&
        !c.name.includes('Manager')
      );

      if (services.length > 0 || managers.length > 0) {
        diagram += `  subgraph Services["⚙️ Services"]\n`;
        for (const svc of [...services, ...managers]) {
          const tech = svc.technology ? `[${svc.technology}]` : '';
          diagram += `    ${svc.id}[["${svc.name}${tech}"]]\n`;
        }
        diagram += `  end\n\n`;
      }

      if (repositories.length > 0) {
        diagram += `  subgraph DataLayer["💾 Data Layer"]\n`;
        for (const repo of repositories) {
          diagram += `    ${repo.id}[("${repo.name}")]\n`;
        }
        diagram += `  end\n\n`;
      }

      for (const other of others) {
        const tech = other.technology ? `[${other.technology}]` : '';
        diagram += `  ${other.id}[["${other.name}${tech}"]]\n`;
      }
    }
  }

  diagram += `\n  %% Relationships\n`;
  for (const rel of model.relationships) {
    diagram += `  ${rel.source} -->|"${rel.description}"| ${rel.target}\n`;
  }

  diagram += `\n  %% Apply styles\n`;
  if (persons.length > 0) {
    diagram += `  class ${persons.map(p => p.id).join(',')} person\n`;
  }
  if (systems.length > 0) {
    diagram += `  class ${systems.map(s => s.id).join(',')} system\n`;
  }
  if (containers.length > 0) {
    diagram += `  class ${containers.map(c => c.id).join(',')} container\n`;
  }
  if (components.length > 0) {
    diagram += `  class ${components.map(c => c.id).join(',')} component\n`;
  }

  return diagram;
}

/**
 * Generate PlantUML diagram
 */
export function generatePlantUMLDiagram(model: C4Model): string {
  let diagram = '@startuml\n';
  diagram += `title ${model.title}\n\n`;

  for (const element of model.elements) {
    if (element.type === 'person') {
      diagram += `actor "${element.name}" as ${element.id}\n`;
    } else {
      diagram += `component "${element.name}" as ${element.id}\n`;
    }
  }

  diagram += '\n';

  for (const rel of model.relationships) {
    diagram += `${rel.source} --> ${rel.target} : ${rel.description}\n`;
  }

  diagram += '@enduml\n';
  return diagram;
}

/**
 * Generate markdown design document
 */
export function generateMarkdownDesign(
  model: C4Model,
  patterns: DesignPattern[],
  traceability: Array<{ requirement: string; designElement: string }>
): string {
  let output = `# Design Document\n\n`;
  output += `## C4 ${model.title}\n\n`;

  output += `### Elements\n\n`;
  output += `| ID | Name | Type | Description |\n`;
  output += `|----|------|------|-------------|\n`;
  for (const el of model.elements) {
    output += `| ${el.id} | ${el.name} | ${el.type} | ${el.description} |\n`;
  }

  output += `\n### Relationships\n\n`;
  output += `| Source | Target | Description |\n`;
  output += `|--------|--------|-------------|\n`;
  for (const rel of model.relationships) {
    output += `| ${rel.source} | ${rel.target} | ${rel.description} |\n`;
  }

  if (patterns.length > 0) {
    output += `\n## Design Patterns\n\n`;
    for (const pattern of patterns) {
      output += `### ${pattern.name}\n`;
      output += `- **Category**: ${pattern.category}\n`;
      output += `- **Intent**: ${pattern.intent}\n\n`;
    }
  }

  if (traceability.length > 0) {
    output += `\n## Traceability\n\n`;
    output += `| Requirement | Design Element |\n`;
    output += `|-------------|----------------|\n`;
    for (const trace of traceability) {
      output += `| ${trace.requirement} | ${trace.designElement} |\n`;
    }
  }

  return output;
}

/**
 * Generate ADR markdown
 */
export function generateADRMarkdown(adrDoc: ADRDocument): string {
  return `# ${adrDoc.id}: ${adrDoc.title}

- **Date**: ${adrDoc.date}
- **Status**: ${adrDoc.status}

## Context

${adrDoc.context}

## Decision

${adrDoc.decision}

## Consequences

${adrDoc.consequences.map(c => `- ${c}`).join('\n')}

## Related Requirements

${adrDoc.relatedRequirements.length > 0 ? adrDoc.relatedRequirements.map(r => `- ${r}`).join('\n') : '- None'}
`;
}
