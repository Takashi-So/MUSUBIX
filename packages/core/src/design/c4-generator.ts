/**
 * C4 Model Generator
 * 
 * Generates C4 architecture diagrams from design specifications
 * 
 * @packageDocumentation
 * @module design/c4-generator
 * 
 * @see REQ-DES-004 - C4 Model Generation
 * @see Article IV - Design-Implementation Consistency
 */

/**
 * C4 diagram level
 */
export type C4Level = 'context' | 'container' | 'component' | 'code';

/**
 * C4 element type
 */
export type C4ElementType =
  | 'person'
  | 'software-system'
  | 'container'
  | 'component'
  | 'code-element'
  | 'enterprise-boundary'
  | 'system-boundary'
  | 'container-boundary';

/**
 * C4 relationship type
 */
export type C4RelationshipType =
  | 'uses'
  | 'calls'
  | 'sends'
  | 'reads'
  | 'writes'
  | 'subscribes'
  | 'publishes'
  | 'depends-on'
  | 'extends'
  | 'implements';

/**
 * C4 element
 */
export interface C4Element {
  /** Element ID */
  id: string;
  /** Element type */
  type: C4ElementType;
  /** Name */
  name: string;
  /** Description */
  description: string;
  /** Technology */
  technology?: string;
  /** Tags */
  tags?: string[];
  /** Properties */
  properties?: Record<string, string>;
  /** External system */
  external?: boolean;
  /** Container ID (for components) */
  containerId?: string;
  /** System ID (for containers) */
  systemId?: string;
}

/**
 * C4 relationship
 */
export interface C4Relationship {
  /** Relationship ID */
  id: string;
  /** Source element ID */
  sourceId: string;
  /** Target element ID */
  targetId: string;
  /** Relationship type */
  type: C4RelationshipType;
  /** Description */
  description: string;
  /** Technology/protocol */
  technology?: string;
  /** Tags */
  tags?: string[];
}

/**
 * C4 diagram
 */
export interface C4Diagram {
  /** Diagram ID */
  id: string;
  /** Diagram title */
  title: string;
  /** Level */
  level: C4Level;
  /** Scope (system/container being detailed) */
  scope?: string;
  /** Elements */
  elements: C4Element[];
  /** Relationships */
  relationships: C4Relationship[];
  /** Description */
  description?: string;
  /** Generated at */
  generatedAt: Date;
}

/**
 * C4 model (complete set of diagrams)
 */
export interface C4Model {
  /** Model ID */
  id: string;
  /** Model name */
  name: string;
  /** Diagrams */
  diagrams: C4Diagram[];
  /** All elements */
  elements: C4Element[];
  /** All relationships */
  relationships: C4Relationship[];
  /** Generated at */
  generatedAt: Date;
}

/**
 * Design input for generation
 */
export interface DesignInput {
  /** System name */
  systemName: string;
  /** System description */
  systemDescription: string;
  /** Users/actors */
  users?: Array<{
    name: string;
    description: string;
  }>;
  /** External systems */
  externalSystems?: Array<{
    name: string;
    description: string;
  }>;
  /** Containers/services */
  containers?: Array<{
    name: string;
    description: string;
    technology: string;
    type?: 'web-app' | 'api' | 'database' | 'queue' | 'storage' | 'service';
  }>;
  /** Components */
  components?: Array<{
    name: string;
    description: string;
    technology?: string;
    containerId: string;
  }>;
  /** Interactions */
  interactions?: Array<{
    from: string;
    to: string;
    description: string;
    technology?: string;
  }>;
}

/**
 * Output format
 */
export type OutputFormat = 'structurizr' | 'plantuml' | 'mermaid' | 'json';

/**
 * Generator config
 */
export interface C4GeneratorConfig {
  /** Output format */
  outputFormat: OutputFormat;
  /** Include all levels */
  includeAllLevels: boolean;
  /** Generate code level diagrams */
  includeCodeLevel: boolean;
  /** Auto-detect containers */
  autoDetectContainers: boolean;
  /** Style configuration */
  style?: C4Style;
}

/**
 * C4 style configuration
 */
export interface C4Style {
  /** Person color */
  personColor?: string;
  /** Software system color */
  softwareSystemColor?: string;
  /** Container color */
  containerColor?: string;
  /** Component color */
  componentColor?: string;
  /** External system color */
  externalColor?: string;
  /** Database color */
  databaseColor?: string;
}

/**
 * Default configuration
 */
export const DEFAULT_C4_CONFIG: C4GeneratorConfig = {
  outputFormat: 'mermaid',
  includeAllLevels: true,
  includeCodeLevel: false,
  autoDetectContainers: true,
};

/**
 * Default style
 */
export const DEFAULT_C4_STYLE: C4Style = {
  personColor: '#08427B',
  softwareSystemColor: '#1168BD',
  containerColor: '#438DD5',
  componentColor: '#85BBF0',
  externalColor: '#999999',
  databaseColor: '#438DD5',
};

/**
 * C4 Model Generator
 */
export class C4ModelGenerator {
  private config: C4GeneratorConfig;
  private elementCounter = 0;
  private relationshipCounter = 0;

  constructor(config?: Partial<C4GeneratorConfig>) {
    this.config = { ...DEFAULT_C4_CONFIG, ...config };
  }

  /**
   * Generate C4 model from design input
   */
  generate(input: DesignInput): C4Model {
    const elements: C4Element[] = [];
    const relationships: C4Relationship[] = [];
    const diagrams: C4Diagram[] = [];

    // Create main system
    const mainSystem = this.createElement('software-system', input.systemName, input.systemDescription);
    elements.push(mainSystem);

    // Create users
    for (const user of input.users ?? []) {
      const person = this.createElement('person', user.name, user.description);
      elements.push(person);
      
      // Add relationship to main system
      relationships.push(this.createRelationship(person.id, mainSystem.id, 'uses', `Uses ${input.systemName}`));
    }

    // Create external systems
    for (const ext of input.externalSystems ?? []) {
      const system = this.createElement('software-system', ext.name, ext.description, { external: true });
      elements.push(system);
    }

    // Create containers
    const containerMap = new Map<string, C4Element>();
    for (const container of input.containers ?? []) {
      const element = this.createElement('container', container.name, container.description, {
        technology: container.technology,
        systemId: mainSystem.id,
        tags: container.type ? [container.type] : undefined,
      });
      elements.push(element);
      containerMap.set(container.name, element);
    }

    // Create components
    for (const component of input.components ?? []) {
      const container = containerMap.get(component.containerId);
      const element = this.createElement('component', component.name, component.description, {
        technology: component.technology,
        containerId: container?.id,
      });
      elements.push(element);
    }

    // Create relationships from interactions
    for (const interaction of input.interactions ?? []) {
      const source = this.findElement(elements, interaction.from);
      const target = this.findElement(elements, interaction.to);
      
      if (source && target) {
        relationships.push(this.createRelationship(
          source.id,
          target.id,
          'uses',
          interaction.description,
          interaction.technology
        ));
      }
    }

    // Generate diagrams
    diagrams.push(this.generateContextDiagram(mainSystem, elements, relationships));
    
    if (this.config.includeAllLevels) {
      diagrams.push(this.generateContainerDiagram(mainSystem, elements, relationships));
      
      // Generate component diagrams for each container
      for (const container of containerMap.values()) {
        const componentElements = elements.filter(
          (e) => e.type === 'component' && e.containerId === container.id
        );
        if (componentElements.length > 0) {
          diagrams.push(this.generateComponentDiagram(container, elements, relationships));
        }
      }
    }

    return {
      id: `c4-model-${Date.now()}`,
      name: input.systemName,
      diagrams,
      elements,
      relationships,
      generatedAt: new Date(),
    };
  }

  /**
   * Export diagram to specified format
   */
  export(diagram: C4Diagram, format?: OutputFormat): string {
    const fmt = format ?? this.config.outputFormat;
    
    switch (fmt) {
      case 'structurizr':
        return this.toStructurizr(diagram);
      case 'plantuml':
        return this.toPlantUML(diagram);
      case 'mermaid':
        return this.toMermaid(diagram);
      case 'json':
        return JSON.stringify(diagram, null, 2);
      default:
        return this.toMermaid(diagram);
    }
  }

  /**
   * Export entire model
   */
  exportModel(model: C4Model, format?: OutputFormat): string {
    const outputs: string[] = [];
    
    for (const diagram of model.diagrams) {
      outputs.push(`// ${diagram.title}\n${this.export(diagram, format)}`);
    }
    
    return outputs.join('\n\n');
  }

  /**
   * Generate context diagram
   */
  private generateContextDiagram(
    mainSystem: C4Element,
    elements: C4Element[],
    relationships: C4Relationship[]
  ): C4Diagram {
    // Include persons, external systems, and the main system
    const contextElements = elements.filter(
      (e) => e.type === 'person' || e.type === 'software-system'
    );

    // Include relationships between context elements
    const contextRelationships = relationships.filter(
      (r) =>
        contextElements.some((e) => e.id === r.sourceId) &&
        contextElements.some((e) => e.id === r.targetId)
    );

    return {
      id: `context-${mainSystem.id}`,
      title: `System Context: ${mainSystem.name}`,
      level: 'context',
      scope: mainSystem.id,
      elements: contextElements,
      relationships: contextRelationships,
      description: `System context diagram for ${mainSystem.name}`,
      generatedAt: new Date(),
    };
  }

  /**
   * Generate container diagram
   */
  private generateContainerDiagram(
    mainSystem: C4Element,
    elements: C4Element[],
    relationships: C4Relationship[]
  ): C4Diagram {
    // Include persons, containers of main system, and external systems
    const containerElements = elements.filter(
      (e) =>
        e.type === 'person' ||
        (e.type === 'software-system' && e.external) ||
        (e.type === 'container' && e.systemId === mainSystem.id)
    );

    const containerRelationships = relationships.filter(
      (r) =>
        containerElements.some((e) => e.id === r.sourceId) &&
        containerElements.some((e) => e.id === r.targetId)
    );

    return {
      id: `container-${mainSystem.id}`,
      title: `Container: ${mainSystem.name}`,
      level: 'container',
      scope: mainSystem.id,
      elements: containerElements,
      relationships: containerRelationships,
      description: `Container diagram for ${mainSystem.name}`,
      generatedAt: new Date(),
    };
  }

  /**
   * Generate component diagram
   */
  private generateComponentDiagram(
    container: C4Element,
    elements: C4Element[],
    relationships: C4Relationship[]
  ): C4Diagram {
    // Include components of this container and related elements
    const componentElements = elements.filter(
      (e) =>
        (e.type === 'component' && e.containerId === container.id) ||
        (e.type === 'container' && e.id !== container.id)
    );

    const componentRelationships = relationships.filter(
      (r) =>
        componentElements.some((e) => e.id === r.sourceId) ||
        componentElements.some((e) => e.id === r.targetId)
    );

    return {
      id: `component-${container.id}`,
      title: `Component: ${container.name}`,
      level: 'component',
      scope: container.id,
      elements: componentElements,
      relationships: componentRelationships,
      description: `Component diagram for ${container.name}`,
      generatedAt: new Date(),
    };
  }

  /**
   * Create an element
   */
  private createElement(
    type: C4ElementType,
    name: string,
    description: string,
    options?: Partial<C4Element>
  ): C4Element {
    return {
      id: `el-${++this.elementCounter}`,
      type,
      name,
      description,
      ...options,
    };
  }

  /**
   * Create a relationship
   */
  private createRelationship(
    sourceId: string,
    targetId: string,
    type: C4RelationshipType,
    description: string,
    technology?: string
  ): C4Relationship {
    return {
      id: `rel-${++this.relationshipCounter}`,
      sourceId,
      targetId,
      type,
      description,
      technology,
    };
  }

  /**
   * Find element by name
   */
  private findElement(elements: C4Element[], name: string): C4Element | undefined {
    return elements.find((e) => e.name === name || e.id === name);
  }

  /**
   * Export to Structurizr DSL
   */
  private toStructurizr(diagram: C4Diagram): string {
    const lines: string[] = [];
    lines.push(`workspace "${diagram.title}" {`);
    lines.push('  model {');

    // Elements
    for (const element of diagram.elements) {
      const ext = element.external ? ' "External"' : '';
      switch (element.type) {
        case 'person':
          lines.push(`    ${this.sanitizeId(element.name)} = person "${element.name}" "${element.description}"${ext}`);
          break;
        case 'software-system':
          lines.push(`    ${this.sanitizeId(element.name)} = softwareSystem "${element.name}" "${element.description}"${ext}`);
          break;
        case 'container':
          lines.push(`    ${this.sanitizeId(element.name)} = container "${element.name}" "${element.description}" "${element.technology ?? ''}"`);
          break;
        case 'component':
          lines.push(`    ${this.sanitizeId(element.name)} = component "${element.name}" "${element.description}" "${element.technology ?? ''}"`);
          break;
      }
    }

    // Relationships
    for (const rel of diagram.relationships) {
      const source = diagram.elements.find((e) => e.id === rel.sourceId);
      const target = diagram.elements.find((e) => e.id === rel.targetId);
      if (source && target) {
        const tech = rel.technology ? ` "${rel.technology}"` : '';
        lines.push(`    ${this.sanitizeId(source.name)} -> ${this.sanitizeId(target.name)} "${rel.description}"${tech}`);
      }
    }

    lines.push('  }');
    lines.push('  views {');
    lines.push(`    ${diagram.level} ${this.sanitizeId(diagram.title)} {`);
    lines.push('      include *');
    lines.push('      autoLayout');
    lines.push('    }');
    lines.push('  }');
    lines.push('}');

    return lines.join('\n');
  }

  /**
   * Export to PlantUML
   */
  private toPlantUML(diagram: C4Diagram): string {
    const lines: string[] = [];
    lines.push('@startuml');
    lines.push(`!include https://raw.githubusercontent.com/plantuml-stdlib/C4-PlantUML/master/C4_${this.capitalizeFirst(diagram.level)}.puml`);
    lines.push('');
    lines.push(`title ${diagram.title}`);
    lines.push('');

    // Elements
    for (const element of diagram.elements) {
      const ext = element.external ? '_Ext' : '';
      switch (element.type) {
        case 'person':
          lines.push(`Person${ext}(${this.sanitizeId(element.name)}, "${element.name}", "${element.description}")`);
          break;
        case 'software-system':
          lines.push(`System${ext}(${this.sanitizeId(element.name)}, "${element.name}", "${element.description}")`);
          break;
        case 'container':
          const containerType = this.getPlantUMLContainerType(element);
          lines.push(`${containerType}(${this.sanitizeId(element.name)}, "${element.name}", "${element.technology ?? ''}", "${element.description}")`);
          break;
        case 'component':
          lines.push(`Component(${this.sanitizeId(element.name)}, "${element.name}", "${element.technology ?? ''}", "${element.description}")`);
          break;
      }
    }

    lines.push('');

    // Relationships
    for (const rel of diagram.relationships) {
      const source = diagram.elements.find((e) => e.id === rel.sourceId);
      const target = diagram.elements.find((e) => e.id === rel.targetId);
      if (source && target) {
        const tech = rel.technology ? `, "${rel.technology}"` : '';
        lines.push(`Rel(${this.sanitizeId(source.name)}, ${this.sanitizeId(target.name)}, "${rel.description}"${tech})`);
      }
    }

    lines.push('');
    lines.push('@enduml');

    return lines.join('\n');
  }

  /**
   * Export to Mermaid
   */
  private toMermaid(diagram: C4Diagram): string {
    const lines: string[] = [];
    lines.push(`%% ${diagram.title}`);
    lines.push('flowchart TB');
    lines.push('');

    // Group elements by type
    const persons = diagram.elements.filter((e) => e.type === 'person');
    const systems = diagram.elements.filter((e) => e.type === 'software-system' && !e.external);
    const external = diagram.elements.filter((e) => e.type === 'software-system' && e.external);
    const containers = diagram.elements.filter((e) => e.type === 'container');
    const components = diagram.elements.filter((e) => e.type === 'component');

    // Subgraph for persons
    if (persons.length > 0) {
      lines.push('  subgraph Users');
      for (const p of persons) {
        lines.push(`    ${this.sanitizeId(p.name)}["👤 ${p.name}<br/>${p.description}"]`);
      }
      lines.push('  end');
      lines.push('');
    }

    // Main system / containers
    if (containers.length > 0) {
      const mainSystem = systems[0];
      lines.push(`  subgraph ${this.sanitizeId(mainSystem?.name ?? 'System')}["${mainSystem?.name ?? 'System'}"]`);
      for (const c of containers) {
        const icon = this.getMermaidIcon(c);
        lines.push(`    ${this.sanitizeId(c.name)}["${icon} ${c.name}<br/>${c.technology ?? ''}<br/>${c.description}"]`);
      }
      lines.push('  end');
      lines.push('');
    } else if (systems.length > 0) {
      for (const s of systems) {
        lines.push(`  ${this.sanitizeId(s.name)}["🖥️ ${s.name}<br/>${s.description}"]`);
      }
      lines.push('');
    }

    // Components
    if (components.length > 0) {
      // Group by container
      const byContainer = new Map<string, C4Element[]>();
      for (const c of components) {
        const key = c.containerId ?? 'unknown';
        if (!byContainer.has(key)) byContainer.set(key, []);
        byContainer.get(key)!.push(c);
      }

      for (const [containerId, comps] of byContainer) {
        const container = diagram.elements.find((e) => e.id === containerId);
        lines.push(`  subgraph ${containerId}["${container?.name ?? containerId}"]`);
        for (const c of comps) {
          lines.push(`    ${this.sanitizeId(c.name)}["📦 ${c.name}<br/>${c.description}"]`);
        }
        lines.push('  end');
      }
      lines.push('');
    }

    // External systems
    if (external.length > 0) {
      lines.push('  subgraph External["External Systems"]');
      for (const e of external) {
        lines.push(`    ${this.sanitizeId(e.name)}["🌐 ${e.name}<br/>${e.description}"]`);
      }
      lines.push('  end');
      lines.push('');
    }

    // Relationships
    for (const rel of diagram.relationships) {
      const source = diagram.elements.find((e) => e.id === rel.sourceId);
      const target = diagram.elements.find((e) => e.id === rel.targetId);
      if (source && target) {
        const label = rel.technology ? `${rel.description}<br/>${rel.technology}` : rel.description;
        lines.push(`  ${this.sanitizeId(source.name)} -->|"${label}"| ${this.sanitizeId(target.name)}`);
      }
    }

    // Styling
    lines.push('');
    lines.push('  classDef person fill:#08427B,color:#fff');
    lines.push('  classDef system fill:#1168BD,color:#fff');
    lines.push('  classDef container fill:#438DD5,color:#fff');
    lines.push('  classDef external fill:#999999,color:#fff');

    return lines.join('\n');
  }

  /**
   * Get PlantUML container type
   */
  private getPlantUMLContainerType(element: C4Element): string {
    const tags = element.tags ?? [];
    if (tags.includes('database')) return 'ContainerDb';
    if (tags.includes('queue')) return 'ContainerQueue';
    return 'Container';
  }

  /**
   * Get Mermaid icon for element
   */
  private getMermaidIcon(element: C4Element): string {
    const tags = element.tags ?? [];
    if (tags.includes('database')) return '🗄️';
    if (tags.includes('queue')) return '📨';
    if (tags.includes('web-app')) return '🌐';
    if (tags.includes('api')) return '⚡';
    if (tags.includes('storage')) return '💾';
    return '📦';
  }

  /**
   * Sanitize ID for diagram formats
   */
  private sanitizeId(name: string): string {
    return name.replace(/[^a-zA-Z0-9]/g, '_').toLowerCase();
  }

  /**
   * Capitalize first letter
   */
  private capitalizeFirst(str: string): string {
    return str.charAt(0).toUpperCase() + str.slice(1);
  }
}

/**
 * Create C4 model generator instance
 */
export function createC4ModelGenerator(config?: Partial<C4GeneratorConfig>): C4ModelGenerator {
  return new C4ModelGenerator(config);
}
