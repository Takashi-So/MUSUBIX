/**
 * Visual Explanation Generator
 * 
 * Generates visual diagrams and explanations for complex concepts
 * 
 * @packageDocumentation
 * @module explanation/visual
 * 
 * @see REQ-EXP-003 - Visual Explanation Generation
 * @see Article VI - Explainable AI
 */

/**
 * Diagram type
 */
export type DiagramType =
  | 'flowchart'
  | 'sequence'
  | 'class'
  | 'entity-relationship'
  | 'state'
  | 'component'
  | 'deployment'
  | 'mindmap'
  | 'gantt'
  | 'pie';

/**
 * Output format
 */
export type OutputFormat = 'mermaid' | 'plantuml' | 'svg' | 'ascii' | 'json';

/**
 * Visual element
 */
export interface VisualElement {
  /** Element ID */
  id: string;
  /** Type */
  type: 'node' | 'edge' | 'group' | 'annotation';
  /** Label */
  label: string;
  /** Description */
  description?: string;
  /** Style */
  style?: ElementStyle;
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Element style
 */
export interface ElementStyle {
  /** Fill color */
  fill?: string;
  /** Stroke color */
  stroke?: string;
  /** Shape */
  shape?: 'rectangle' | 'ellipse' | 'diamond' | 'hexagon' | 'cylinder' | 'cloud';
  /** Line style */
  lineStyle?: 'solid' | 'dashed' | 'dotted';
  /** Font size */
  fontSize?: number;
}

/**
 * Node element
 */
export interface NodeElement extends VisualElement {
  type: 'node';
  /** Position */
  position?: { x: number; y: number };
  /** Size */
  size?: { width: number; height: number };
}

/**
 * Edge element
 */
export interface EdgeElement extends VisualElement {
  type: 'edge';
  /** Source node ID */
  source: string;
  /** Target node ID */
  target: string;
  /** Arrow type */
  arrow?: 'none' | 'single' | 'double' | 'open' | 'filled';
}

/**
 * Group element
 */
export interface GroupElement extends VisualElement {
  type: 'group';
  /** Child element IDs */
  children: string[];
}

/**
 * Diagram structure
 */
export interface Diagram {
  /** Diagram ID */
  id: string;
  /** Title */
  title: string;
  /** Type */
  type: DiagramType;
  /** Description */
  description?: string;
  /** Elements */
  elements: VisualElement[];
  /** Layout direction */
  direction?: 'TB' | 'BT' | 'LR' | 'RL';
  /** Theme */
  theme?: DiagramTheme;
}

/**
 * Diagram theme
 */
export interface DiagramTheme {
  /** Primary color */
  primary: string;
  /** Secondary color */
  secondary: string;
  /** Background color */
  background: string;
  /** Text color */
  text: string;
  /** Accent colors */
  accents: string[];
}

/**
 * Default themes
 */
export const DIAGRAM_THEMES: Record<string, DiagramTheme> = {
  default: {
    primary: '#2196F3',
    secondary: '#4CAF50',
    background: '#FFFFFF',
    text: '#333333',
    accents: ['#FF9800', '#9C27B0', '#00BCD4'],
  },
  dark: {
    primary: '#90CAF9',
    secondary: '#A5D6A7',
    background: '#1E1E1E',
    text: '#FFFFFF',
    accents: ['#FFB74D', '#CE93D8', '#80DEEA'],
  },
  minimal: {
    primary: '#666666',
    secondary: '#999999',
    background: '#FFFFFF',
    text: '#333333',
    accents: ['#888888', '#AAAAAA', '#CCCCCC'],
  },
};

/**
 * Explanation context
 */
export interface ExplanationContext {
  /** Subject being explained */
  subject: string;
  /** Target audience */
  audience: 'developer' | 'manager' | 'stakeholder' | 'general';
  /** Complexity level */
  complexity: 'simple' | 'intermediate' | 'detailed';
  /** Additional context */
  additionalContext?: string;
}

/**
 * Visual explanation result
 */
export interface VisualExplanation {
  /** Generated diagram */
  diagram: Diagram;
  /** Narrative explanation */
  narrative: string;
  /** Key insights */
  insights: string[];
  /** Rendered output */
  rendered: Record<OutputFormat, string>;
  /** Related concepts */
  relatedConcepts?: string[];
}

/**
 * Generator configuration
 */
export interface VisualGeneratorConfig {
  /** Default diagram type */
  defaultType: DiagramType;
  /** Default output format */
  defaultFormat: OutputFormat;
  /** Default theme */
  defaultTheme: string;
  /** Include narrative */
  includeNarrative: boolean;
  /** Include insights */
  includeInsights: boolean;
  /** Max elements per diagram */
  maxElements: number;
}

/**
 * Default configuration
 */
export const DEFAULT_VISUAL_CONFIG: VisualGeneratorConfig = {
  defaultType: 'flowchart',
  defaultFormat: 'mermaid',
  defaultTheme: 'default',
  includeNarrative: true,
  includeInsights: true,
  maxElements: 50,
};

/**
 * Visual Explanation Generator
 */
export class VisualExplanationGenerator {
  private config: VisualGeneratorConfig;
  private elementCounter = 0;

  constructor(config?: Partial<VisualGeneratorConfig>) {
    this.config = { ...DEFAULT_VISUAL_CONFIG, ...config };
  }

  /**
   * Generate visual explanation
   */
  generate(
    context: ExplanationContext,
    diagramType?: DiagramType
  ): VisualExplanation {
    const type = diagramType ?? this.config.defaultType;
    
    // Create diagram structure
    const diagram = this.createDiagram(context, type);

    // Generate narrative
    const narrative = this.config.includeNarrative
      ? this.generateNarrative(context, diagram)
      : '';

    // Extract insights
    const insights = this.config.includeInsights
      ? this.extractInsights(context, diagram)
      : [];

    // Render in multiple formats
    const rendered = this.renderAllFormats(diagram);

    return {
      diagram,
      narrative,
      insights,
      rendered,
      relatedConcepts: this.findRelatedConcepts(context),
    };
  }

  /**
   * Create diagram from context
   */
  private createDiagram(context: ExplanationContext, type: DiagramType): Diagram {
    const theme = DIAGRAM_THEMES[this.config.defaultTheme];

    const diagram: Diagram = {
      id: this.generateId('diagram'),
      title: `${context.subject} Overview`,
      type,
      description: context.additionalContext,
      elements: [],
      direction: 'TB',
      theme,
    };

    // Generate elements based on diagram type
    switch (type) {
      case 'flowchart':
        diagram.elements = this.generateFlowchartElements(context);
        break;
      case 'sequence':
        diagram.elements = this.generateSequenceElements(context);
        break;
      case 'class':
        diagram.elements = this.generateClassElements(context);
        break;
      case 'mindmap':
        diagram.elements = this.generateMindmapElements(context);
        break;
      case 'state':
        diagram.elements = this.generateStateElements(context);
        break;
      case 'component':
        diagram.elements = this.generateComponentElements(context);
        break;
      default:
        diagram.elements = this.generateGenericElements(context);
    }

    return diagram;
  }

  /**
   * Generate flowchart elements
   */
  private generateFlowchartElements(context: ExplanationContext): VisualElement[] {
    const elements: VisualElement[] = [];

    // Start node
    const start = this.createNode('Start', 'Begin process', { shape: 'ellipse' });
    elements.push(start);

    // Process steps based on complexity
    const steps = this.deriveProcessSteps(context);
    let prevId = start.id;

    for (const step of steps) {
      const node = this.createNode(step.name, step.description, { shape: 'rectangle' });
      elements.push(node);

      const edge = this.createEdge(prevId, node.id, step.transition);
      elements.push(edge);

      prevId = node.id;
    }

    // End node
    const end = this.createNode('End', 'Process complete', { shape: 'ellipse' });
    elements.push(end);
    elements.push(this.createEdge(prevId, end.id, ''));

    return elements;
  }

  /**
   * Generate sequence diagram elements
   */
  private generateSequenceElements(context: ExplanationContext): VisualElement[] {
    const elements: VisualElement[] = [];

    // Participants
    const participants = this.deriveParticipants(context);
    for (const p of participants) {
      elements.push(this.createNode(p.name, p.role, { shape: 'rectangle' }));
    }

    // Interactions
    const interactions = this.deriveInteractions(context);
    for (const interaction of interactions) {
      elements.push(this.createEdge(
        interaction.from,
        interaction.to,
        interaction.message,
        { arrow: 'single' }
      ));
    }

    return elements;
  }

  /**
   * Generate class diagram elements
   */
  private generateClassElements(context: ExplanationContext): VisualElement[] {
    const elements: VisualElement[] = [];

    // Classes
    const classes = this.deriveClasses(context);
    for (const cls of classes) {
      const node = this.createNode(cls.name, cls.description, { shape: 'rectangle' });
      node.metadata = {
        attributes: cls.attributes,
        methods: cls.methods,
      };
      elements.push(node);
    }

    // Relationships
    const relationships = this.deriveRelationships(context);
    for (const rel of relationships) {
      elements.push(this.createEdge(
        rel.from,
        rel.to,
        rel.type,
        { arrow: rel.type === 'inheritance' ? 'open' : 'filled' }
      ));
    }

    return elements;
  }

  /**
   * Generate mindmap elements
   */
  private generateMindmapElements(context: ExplanationContext): VisualElement[] {
    const elements: VisualElement[] = [];

    // Central concept
    const center = this.createNode(context.subject, 'Main concept', { shape: 'ellipse' });
    elements.push(center);

    // Branches
    const branches = this.deriveBranches(context);
    for (const branch of branches) {
      const node = this.createNode(branch.topic, branch.description, { shape: 'rectangle' });
      elements.push(node);
      elements.push(this.createEdge(center.id, node.id, ''));

      // Sub-branches
      for (const sub of branch.subtopics) {
        const subNode = this.createNode(sub, '', { shape: 'rectangle' });
        elements.push(subNode);
        elements.push(this.createEdge(node.id, subNode.id, ''));
      }
    }

    return elements;
  }

  /**
   * Generate state diagram elements
   */
  private generateStateElements(context: ExplanationContext): VisualElement[] {
    const elements: VisualElement[] = [];

    // Initial state
    const initial = this.createNode('[*]', 'Initial state', { shape: 'ellipse' });
    elements.push(initial);

    // States
    const states = this.deriveStates(context);
    for (const state of states) {
      const node = this.createNode(state.name, state.description, { shape: 'rectangle' });
      elements.push(node);
    }

    // Transitions
    const transitions = this.deriveTransitions(context);
    for (const t of transitions) {
      elements.push(this.createEdge(t.from, t.to, t.trigger));
    }

    // Final state
    const final = this.createNode('[*]', 'Final state', { shape: 'ellipse' });
    final.id = this.generateId('final');
    elements.push(final);

    return elements;
  }

  /**
   * Generate component diagram elements
   */
  private generateComponentElements(context: ExplanationContext): VisualElement[] {
    const elements: VisualElement[] = [];

    // Components
    const components = this.deriveComponents(context);
    for (const comp of components) {
      const node = this.createNode(comp.name, comp.description, { shape: 'rectangle' });
      node.metadata = { interfaces: comp.interfaces };
      elements.push(node);
    }

    // Dependencies
    const deps = this.deriveDependencies(context);
    for (const dep of deps) {
      elements.push(this.createEdge(dep.from, dep.to, dep.type, { lineStyle: 'dashed' }));
    }

    return elements;
  }

  /**
   * Generate generic elements
   */
  private generateGenericElements(context: ExplanationContext): VisualElement[] {
    const elements: VisualElement[] = [];

    // Main subject
    const main = this.createNode(context.subject, '', { shape: 'rectangle' });
    elements.push(main);

    // Related concepts
    const concepts = this.findRelatedConcepts(context);
    for (const concept of concepts) {
      const node = this.createNode(concept, '', { shape: 'rectangle' });
      elements.push(node);
      elements.push(this.createEdge(main.id, node.id, 'relates to'));
    }

    return elements;
  }

  /**
   * Create node element
   */
  private createNode(label: string, description: string, style: Partial<ElementStyle>): NodeElement {
    return {
      id: this.generateId('node'),
      type: 'node',
      label,
      description,
      style: { ...style },
    };
  }

  /**
   * Create edge element
   */
  private createEdge(
    source: string,
    target: string,
    label: string,
    style?: Partial<ElementStyle & { arrow: EdgeElement['arrow'] }>
  ): EdgeElement {
    return {
      id: this.generateId('edge'),
      type: 'edge',
      source,
      target,
      label,
      arrow: style?.arrow ?? 'single',
      style: style ? { ...style } : undefined,
    };
  }

  /**
   * Derive process steps from context
   */
  private deriveProcessSteps(context: ExplanationContext): Array<{
    name: string;
    description: string;
    transition: string;
  }> {
    // Generate based on complexity
    const baseSteps = [
      { name: 'Input', description: 'Receive input data', transition: '' },
      { name: 'Process', description: 'Process the data', transition: '' },
      { name: 'Validate', description: 'Validate results', transition: '' },
      { name: 'Output', description: 'Generate output', transition: '' },
    ];

    if (context.complexity === 'detailed') {
      return [
        { name: 'Initialize', description: 'Setup environment', transition: '' },
        ...baseSteps,
        { name: 'Log', description: 'Record operation', transition: '' },
        { name: 'Cleanup', description: 'Release resources', transition: '' },
      ];
    }

    if (context.complexity === 'simple') {
      return [
        { name: 'Process', description: `Process ${context.subject}`, transition: '' },
      ];
    }

    return baseSteps;
  }

  /**
   * Derive participants for sequence diagram
   */
  private deriveParticipants(_context: ExplanationContext): Array<{
    name: string;
    role: string;
  }> {
    return [
      { name: 'User', role: 'Initiator' },
      { name: 'System', role: 'Processor' },
      { name: 'Database', role: 'Storage' },
    ];
  }

  /**
   * Derive interactions for sequence diagram
   */
  private deriveInteractions(_context: ExplanationContext): Array<{
    from: string;
    to: string;
    message: string;
  }> {
    return [
      { from: 'user', to: 'system', message: 'Request' },
      { from: 'system', to: 'database', message: 'Query' },
      { from: 'database', to: 'system', message: 'Result' },
      { from: 'system', to: 'user', message: 'Response' },
    ];
  }

  /**
   * Derive classes for class diagram
   */
  private deriveClasses(context: ExplanationContext): Array<{
    name: string;
    description: string;
    attributes: string[];
    methods: string[];
  }> {
    return [
      {
        name: context.subject,
        description: 'Main class',
        attributes: ['id: string', 'data: any'],
        methods: ['process()', 'validate()'],
      },
    ];
  }

  /**
   * Derive relationships for class diagram
   */
  private deriveRelationships(_context: ExplanationContext): Array<{
    from: string;
    to: string;
    type: string;
  }> {
    return [];
  }

  /**
   * Derive branches for mindmap
   */
  private deriveBranches(_context: ExplanationContext): Array<{
    topic: string;
    description: string;
    subtopics: string[];
  }> {
    return [
      { topic: 'Features', description: 'Key features', subtopics: ['Feature A', 'Feature B'] },
      { topic: 'Benefits', description: 'Key benefits', subtopics: ['Benefit A', 'Benefit B'] },
      { topic: 'Use Cases', description: 'Applications', subtopics: ['Case A', 'Case B'] },
    ];
  }

  /**
   * Derive states for state diagram
   */
  private deriveStates(_context: ExplanationContext): Array<{
    name: string;
    description: string;
  }> {
    return [
      { name: 'Idle', description: 'Waiting for input' },
      { name: 'Processing', description: 'Processing data' },
      { name: 'Complete', description: 'Operation finished' },
    ];
  }

  /**
   * Derive transitions for state diagram
   */
  private deriveTransitions(_context: ExplanationContext): Array<{
    from: string;
    to: string;
    trigger: string;
  }> {
    return [
      { from: '[*]', to: 'idle', trigger: 'start' },
      { from: 'idle', to: 'processing', trigger: 'input received' },
      { from: 'processing', to: 'complete', trigger: 'done' },
      { from: 'complete', to: '[*]', trigger: 'finish' },
    ];
  }

  /**
   * Derive components for component diagram
   */
  private deriveComponents(_context: ExplanationContext): Array<{
    name: string;
    description: string;
    interfaces: string[];
  }> {
    return [
      { name: 'API', description: 'External interface', interfaces: ['REST', 'GraphQL'] },
      { name: 'Service', description: 'Business logic', interfaces: ['IService'] },
      { name: 'Repository', description: 'Data access', interfaces: ['IRepository'] },
    ];
  }

  /**
   * Derive dependencies for component diagram
   */
  private deriveDependencies(_context: ExplanationContext): Array<{
    from: string;
    to: string;
    type: string;
  }> {
    return [
      { from: 'api', to: 'service', type: 'uses' },
      { from: 'service', to: 'repository', type: 'uses' },
    ];
  }

  /**
   * Generate narrative explanation
   */
  private generateNarrative(context: ExplanationContext, diagram: Diagram): string {
    const lines: string[] = [];

    lines.push(`## ${context.subject}`);
    lines.push('');

    // Introduction based on audience
    switch (context.audience) {
      case 'developer':
        lines.push(`This technical overview explains the ${context.subject} architecture and implementation details.`);
        break;
      case 'manager':
        lines.push(`This summary provides a high-level view of ${context.subject} and its business value.`);
        break;
      case 'stakeholder':
        lines.push(`This document outlines how ${context.subject} addresses your requirements.`);
        break;
      default:
        lines.push(`This explanation covers the key aspects of ${context.subject}.`);
    }

    lines.push('');

    // Describe diagram
    lines.push(`### Visual Overview`);
    lines.push('');
    lines.push(`The ${diagram.type} diagram above illustrates the key components and their relationships.`);
    lines.push('');

    // Key elements
    const nodes = diagram.elements.filter((e) => e.type === 'node');
    if (nodes.length > 0) {
      lines.push('### Key Elements');
      lines.push('');
      for (const node of nodes.slice(0, 5)) {
        lines.push(`- **${node.label}**: ${node.description || 'Part of the system'}`);
      }
    }

    return lines.join('\n');
  }

  /**
   * Extract insights from explanation
   */
  private extractInsights(context: ExplanationContext, diagram: Diagram): string[] {
    const insights: string[] = [];

    // Analyze diagram structure
    const nodes = diagram.elements.filter((e) => e.type === 'node').length;
    const edges = diagram.elements.filter((e) => e.type === 'edge').length;

    if (nodes > 5) {
      insights.push(`The system has ${nodes} major components, indicating moderate complexity`);
    }

    if (edges > nodes) {
      insights.push('High interconnectivity suggests tight coupling between components');
    }

    // Context-based insights
    switch (context.complexity) {
      case 'detailed':
        insights.push('Detailed view reveals implementation nuances');
        break;
      case 'simple':
        insights.push('Simplified view focuses on core concepts');
        break;
    }

    // Audience-specific insights
    switch (context.audience) {
      case 'developer':
        insights.push('Technical implementation follows established patterns');
        break;
      case 'manager':
        insights.push('Architecture supports scalability and maintainability');
        break;
    }

    return insights;
  }

  /**
   * Find related concepts
   */
  private findRelatedConcepts(context: ExplanationContext): string[] {
    const subject = context.subject.toLowerCase();
    const related: string[] = [];

    // Common related concepts
    const conceptMap: Record<string, string[]> = {
      api: ['REST', 'GraphQL', 'Authentication', 'Rate Limiting'],
      database: ['SQL', 'NoSQL', 'Indexing', 'Transactions'],
      authentication: ['OAuth', 'JWT', 'Sessions', 'MFA'],
      architecture: ['Microservices', 'Monolith', 'Event-Driven', 'Layered'],
      testing: ['Unit Tests', 'Integration Tests', 'E2E Tests', 'TDD'],
      deployment: ['CI/CD', 'Docker', 'Kubernetes', 'Cloud'],
    };

    for (const [key, concepts] of Object.entries(conceptMap)) {
      if (subject.includes(key)) {
        related.push(...concepts);
      }
    }

    return related.slice(0, 5);
  }

  /**
   * Render diagram in all formats
   */
  private renderAllFormats(diagram: Diagram): Record<OutputFormat, string> {
    return {
      mermaid: this.renderMermaid(diagram),
      plantuml: this.renderPlantUML(diagram),
      svg: this.renderSVG(diagram),
      ascii: this.renderASCII(diagram),
      json: JSON.stringify(diagram, null, 2),
    };
  }

  /**
   * Render as Mermaid
   */
  renderMermaid(diagram: Diagram): string {
    const lines: string[] = [];

    // Diagram type declaration
    switch (diagram.type) {
      case 'flowchart':
        lines.push(`flowchart ${diagram.direction ?? 'TB'}`);
        break;
      case 'sequence':
        lines.push('sequenceDiagram');
        break;
      case 'class':
        lines.push('classDiagram');
        break;
      case 'state':
        lines.push('stateDiagram-v2');
        break;
      case 'mindmap':
        lines.push('mindmap');
        lines.push(`  root((${diagram.title}))`);
        break;
      default:
        lines.push(`flowchart ${diagram.direction ?? 'TB'}`);
    }

    // Render elements
    for (const element of diagram.elements) {
      if (element.type === 'node') {
        const node = element as NodeElement;
        const shape = this.mermaidShape(node.style?.shape);
        lines.push(`  ${node.id}${shape[0]}${node.label}${shape[1]}`);
      } else if (element.type === 'edge') {
        const edge = element as EdgeElement;
        const arrow = this.mermaidArrow(edge.arrow, edge.style?.lineStyle);
        const label = edge.label ? `|${edge.label}|` : '';
        lines.push(`  ${edge.source} ${arrow}${label} ${edge.target}`);
      }
    }

    return lines.join('\n');
  }

  /**
   * Get Mermaid shape syntax
   */
  private mermaidShape(shape?: ElementStyle['shape']): [string, string] {
    switch (shape) {
      case 'ellipse': return ['((', '))'];
      case 'diamond': return ['{', '}'];
      case 'hexagon': return ['{{', '}}'];
      case 'cylinder': return ['[(', ')]'];
      case 'cloud': return [')', ')'];
      default: return ['[', ']'];
    }
  }

  /**
   * Get Mermaid arrow syntax
   */
  private mermaidArrow(arrow?: EdgeElement['arrow'], lineStyle?: ElementStyle['lineStyle']): string {
    const line = lineStyle === 'dashed' ? '-.-' : lineStyle === 'dotted' ? '...' : '--';
    
    switch (arrow) {
      case 'none': return `${line}`;
      case 'double': return `<${line}>`;
      case 'open': return `${line}>`;
      default: return `${line}>`;
    }
  }

  /**
   * Render as PlantUML
   */
  renderPlantUML(diagram: Diagram): string {
    const lines: string[] = ['@startuml'];
    lines.push(`title ${diagram.title}`);
    lines.push('');

    // Render based on type
    for (const element of diagram.elements) {
      if (element.type === 'node') {
        const node = element as NodeElement;
        lines.push(`rectangle "${node.label}" as ${node.id}`);
      } else if (element.type === 'edge') {
        const edge = element as EdgeElement;
        const arrow = edge.arrow === 'double' ? '<-->' : '-->';
        const label = edge.label ? ` : ${edge.label}` : '';
        lines.push(`${edge.source} ${arrow} ${edge.target}${label}`);
      }
    }

    lines.push('');
    lines.push('@enduml');
    return lines.join('\n');
  }

  /**
   * Render as SVG (simplified)
   */
  renderSVG(diagram: Diagram): string {
    const nodes = diagram.elements.filter((e) => e.type === 'node') as NodeElement[];
    const width = 800;
    const height = Math.max(400, nodes.length * 100);

    let svg = `<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}">`;
    svg += `<style>
      .node { fill: ${diagram.theme?.primary ?? '#2196F3'}; stroke: #333; stroke-width: 2; }
      .label { font-family: Arial; font-size: 14px; fill: white; text-anchor: middle; }
    </style>`;

    // Render nodes
    nodes.forEach((node, i) => {
      const x = width / 2 - 50;
      const y = 50 + i * 100;
      svg += `<rect class="node" x="${x}" y="${y}" width="100" height="40" rx="5"/>`;
      svg += `<text class="label" x="${x + 50}" y="${y + 25}">${node.label}</text>`;
    });

    svg += '</svg>';
    return svg;
  }

  /**
   * Render as ASCII art
   */
  renderASCII(diagram: Diagram): string {
    const lines: string[] = [];
    const nodes = diagram.elements.filter((e) => e.type === 'node') as NodeElement[];

    lines.push(`┌${'─'.repeat(40)}┐`);
    lines.push(`│ ${diagram.title.padEnd(38)} │`);
    lines.push(`├${'─'.repeat(40)}┤`);

    for (let i = 0; i < nodes.length; i++) {
      const node = nodes[i];
      const boxWidth = Math.min(36, Math.max(10, node.label.length + 4));
      const padding = Math.floor((boxWidth - node.label.length) / 2);
      
      lines.push(`│  ┌${'─'.repeat(boxWidth)}┐${' '.repeat(36 - boxWidth)}│`);
      lines.push(`│  │${' '.repeat(padding)}${node.label}${' '.repeat(boxWidth - padding - node.label.length)}│${' '.repeat(36 - boxWidth)}│`);
      lines.push(`│  └${'─'.repeat(boxWidth)}┘${' '.repeat(36 - boxWidth)}│`);

      if (i < nodes.length - 1) {
        lines.push(`│${' '.repeat(19)}│${' '.repeat(20)}│`);
        lines.push(`│${' '.repeat(19)}▼${' '.repeat(20)}│`);
      }
    }

    lines.push(`└${'─'.repeat(40)}┘`);

    return lines.join('\n');
  }

  /**
   * Generate unique ID
   */
  private generateId(prefix: string): string {
    return `${prefix}_${++this.elementCounter}`;
  }
}

/**
 * Create visual explanation generator instance
 */
export function createVisualExplanationGenerator(
  config?: Partial<VisualGeneratorConfig>
): VisualExplanationGenerator {
  return new VisualExplanationGenerator(config);
}
