/**
 * @fileoverview MQL Parser - Parse MQL queries into AST
 * @module @nahisaho/musubix-security/mql/parser
 * @trace TSK-019, REQ-SEC-MQL-002
 */

import { MQLLexer, TokenType, type Token, type LexerError } from './lexer.js';
import type {
  MQLAst,
  FromClause,
  SelectClause,
  SelectField,
  WhereClause,
  OrderByClause,
  OrderByField,
  LimitClause,
  MQLSource,
  MQLExpression,
  MQLCondition,
  ParseResult,
  ParseError,
  FieldReference,
  Literal,
  FunctionCall,
  BinaryExpression,
  UnaryExpression,
  PropertyAccess,
  ComparisonCondition,
  LogicalCondition,
  InCondition,
  ExistsCondition,
  PredicateCondition,
  PatternCondition,
} from '../types/mql.js';

/**
 * MQL Parser
 */
export class MQLParser {
  private tokens: Token[] = [];
  private current = 0;
  private errors: ParseError[] = [];

  /**
   * Parse MQL query
   */
  parse(source: string): ParseResult {
    // Tokenize
    const lexer = new MQLLexer(source);
    const { tokens, errors: lexerErrors } = lexer.tokenize();

    this.tokens = tokens;
    this.current = 0;
    this.errors = [];

    // Convert lexer errors
    for (const error of lexerErrors) {
      this.errors.push({
        message: error.message,
        line: error.line,
        column: error.column,
        type: 'syntax',
      });
    }

    if (this.errors.length > 0) {
      return {
        errors: this.errors,
        isValid: false,
      };
    }

    try {
      const ast = this.parseQuery();
      return {
        ast,
        errors: this.errors,
        isValid: this.errors.length === 0,
      };
    } catch {
      return {
        errors: this.errors,
        isValid: false,
      };
    }
  }

  /**
   * Parse query
   * query := [SELECT select_clause] FROM from_clause [WHERE where_clause] [ORDER BY order_clause] [LIMIT limit_clause]
   */
  private parseQuery(): MQLAst {
    let select: SelectClause | undefined;
    let from: FromClause;
    let where: WhereClause | undefined;
    let orderBy: OrderByClause | undefined;
    let limit: LimitClause | undefined;

    // Optional SELECT clause
    if (this.match(TokenType.SELECT)) {
      select = this.parseSelectClause();
    }

    // Required FROM clause
    this.consume(TokenType.FROM, "Expected 'FROM' clause");
    from = this.parseFromClause();

    // Optional WHERE clause
    if (this.match(TokenType.WHERE)) {
      where = this.parseWhereClause();
    }

    // Optional ORDER BY clause
    if (this.match(TokenType.ORDER)) {
      this.consume(TokenType.BY, "Expected 'BY' after 'ORDER'");
      orderBy = this.parseOrderByClause();
    }

    // Optional LIMIT clause
    if (this.match(TokenType.LIMIT)) {
      limit = this.parseLimitClause();
    }

    return {
      type: 'query',
      from,
      select,
      where,
      orderBy,
      limit,
    };
  }

  /**
   * Parse SELECT clause
   */
  private parseSelectClause(): SelectClause {
    const distinct = this.match(TokenType.DISTINCT);
    const fields: SelectField[] = [];

    do {
      fields.push(this.parseSelectField());
    } while (this.match(TokenType.COMMA));

    return { fields, distinct };
  }

  /**
   * Parse select field
   */
  private parseSelectField(): SelectField {
    const expression = this.parseExpression();
    let alias: string | undefined;

    if (this.match(TokenType.AS)) {
      alias = this.consume(TokenType.IDENTIFIER, 'Expected alias name').value;
    }

    return { expression, alias };
  }

  /**
   * Parse FROM clause
   */
  private parseFromClause(): FromClause {
    const source = this.parseSource();
    let alias: string | undefined;

    if (this.match(TokenType.AS)) {
      alias = this.consume(TokenType.IDENTIFIER, 'Expected alias name').value;
    } else if (this.check(TokenType.IDENTIFIER) && !this.checkKeyword()) {
      alias = this.advance().value;
    }

    return { source, alias };
  }

  /**
   * Parse data source
   */
  private parseSource(): MQLSource {
    if (this.match(TokenType.FUNCTIONS)) {
      return { type: 'functions' };
    }

    if (this.match(TokenType.CLASSES)) {
      return { type: 'classes' };
    }

    if (this.match(TokenType.CALLS)) {
      return { type: 'calls' };
    }

    if (this.match(TokenType.VARIABLES)) {
      return { type: 'variables' };
    }

    if (this.match(TokenType.DATAFLOW)) {
      let source: MQLExpression | undefined;
      let sink: MQLExpression | undefined;

      if (this.match(TokenType.LPAREN)) {
        if (!this.check(TokenType.COMMA) && !this.check(TokenType.RPAREN)) {
          source = this.parseExpression();
        }
        if (this.match(TokenType.COMMA)) {
          sink = this.parseExpression();
        }
        this.consume(TokenType.RPAREN, "Expected ')' after dataflow parameters");
      }

      return { type: 'dataflow', source, sink };
    }

    if (this.match(TokenType.CONTROLFLOW)) {
      let from: MQLExpression | undefined;
      let to: MQLExpression | undefined;

      if (this.match(TokenType.LPAREN)) {
        if (!this.check(TokenType.COMMA) && !this.check(TokenType.RPAREN)) {
          from = this.parseExpression();
        }
        if (this.match(TokenType.COMMA)) {
          to = this.parseExpression();
        }
        this.consume(TokenType.RPAREN, "Expected ')' after controlflow parameters");
      }

      return { type: 'controlflow', from, to };
    }

    if (this.match(TokenType.AST)) {
      let nodeType: string | undefined;

      if (this.match(TokenType.LPAREN)) {
        if (!this.check(TokenType.RPAREN)) {
          nodeType = this.consume(TokenType.STRING, 'Expected node type string').value;
        }
        this.consume(TokenType.RPAREN, "Expected ')' after AST parameters");
      }

      return { type: 'ast', nodeType };
    }

    if (this.match(TokenType.SYMBOLS)) {
      return { type: 'symbols' };
    }

    throw this.error(this.peek(), 'Expected data source');
  }

  /**
   * Parse WHERE clause
   */
  private parseWhereClause(): WhereClause {
    const condition = this.parseCondition();
    return { condition };
  }

  /**
   * Parse condition (OR level)
   */
  private parseCondition(): MQLCondition {
    let left = this.parseAndCondition();

    while (this.match(TokenType.OR)) {
      const right = this.parseAndCondition();
      left = {
        type: 'logical',
        operator: 'or',
        operands: [left, right],
      };
    }

    return left;
  }

  /**
   * Parse AND condition
   */
  private parseAndCondition(): MQLCondition {
    let left = this.parseNotCondition();

    while (this.match(TokenType.AND)) {
      const right = this.parseNotCondition();
      left = {
        type: 'logical',
        operator: 'and',
        operands: [left, right],
      };
    }

    return left;
  }

  /**
   * Parse NOT condition
   */
  private parseNotCondition(): MQLCondition {
    if (this.match(TokenType.NOT)) {
      const operand = this.parseNotCondition();
      return {
        type: 'logical',
        operator: 'not',
        operands: [operand],
      };
    }

    return this.parsePrimaryCondition();
  }

  /**
   * Parse primary condition
   */
  private parsePrimaryCondition(): MQLCondition {
    // EXISTS condition
    if (this.match(TokenType.EXISTS)) {
      return this.parseExistsCondition();
    }

    // Parenthesized condition
    if (this.match(TokenType.LPAREN)) {
      const condition = this.parseCondition();
      this.consume(TokenType.RPAREN, "Expected ')' after condition");
      return condition;
    }

    // Expression-based condition
    const left = this.parseExpression();

    // IN condition
    if (this.match(TokenType.IN)) {
      return this.parseInCondition(left);
    }

    if (this.match(TokenType.NOT)) {
      if (this.match(TokenType.IN)) {
        return this.parseInCondition(left, true);
      }
      throw this.error(this.peek(), "Expected 'IN' after 'NOT'");
    }

    // LIKE/MATCHES condition
    if (this.match(TokenType.LIKE)) {
      const pattern = this.consume(TokenType.STRING, 'Expected pattern string').value;
      return {
        type: 'pattern',
        operator: 'like',
        expression: left,
        pattern,
      };
    }

    if (this.match(TokenType.MATCHES)) {
      const pattern = this.consume(TokenType.REGEX, 'Expected regex pattern').value;
      return {
        type: 'pattern',
        operator: 'matches',
        expression: left,
        pattern: new RegExp(pattern),
      };
    }

    // Comparison condition
    if (this.checkComparison()) {
      const operator = this.parseComparisonOperator();
      const right = this.parseExpression();
      return {
        type: 'comparison',
        operator,
        left,
        right,
      };
    }

    // Predicate call (function returning boolean)
    if (left.type === 'function') {
      return {
        type: 'predicate',
        name: (left as FunctionCall).name,
        arguments: (left as FunctionCall).arguments,
      };
    }

    throw this.error(this.peek(), 'Expected condition');
  }

  /**
   * Parse EXISTS condition
   */
  private parseExistsCondition(): ExistsCondition {
    this.consume(TokenType.LPAREN, "Expected '(' after 'EXISTS'");
    
    const variable = this.consume(TokenType.IDENTIFIER, 'Expected variable name').value;
    this.consume(TokenType.IN, "Expected 'IN' in EXISTS clause");
    const source = this.parseSource();

    let condition: MQLCondition | undefined;
    if (this.match(TokenType.WHERE)) {
      condition = this.parseCondition();
    }

    this.consume(TokenType.RPAREN, "Expected ')' after EXISTS clause");

    return {
      type: 'exists',
      variable,
      source,
      condition,
    };
  }

  /**
   * Parse IN condition
   */
  private parseInCondition(expression: MQLExpression, negated = false): InCondition {
    this.consume(TokenType.LPAREN, "Expected '(' after 'IN'");

    const values: MQLExpression[] = [];
    if (!this.check(TokenType.RPAREN)) {
      do {
        values.push(this.parseExpression());
      } while (this.match(TokenType.COMMA));
    }

    this.consume(TokenType.RPAREN, "Expected ')' after IN values");

    return {
      type: 'in',
      expression,
      values,
      negated,
    };
  }

  /**
   * Parse ORDER BY clause
   */
  private parseOrderByClause(): OrderByClause {
    const fields: OrderByField[] = [];

    do {
      const expression = this.parseExpression();
      let direction: 'asc' | 'desc' = 'asc';

      if (this.match(TokenType.ASC)) {
        direction = 'asc';
      } else if (this.match(TokenType.DESC)) {
        direction = 'desc';
      }

      fields.push({ expression, direction });
    } while (this.match(TokenType.COMMA));

    return { fields };
  }

  /**
   * Parse LIMIT clause
   */
  private parseLimitClause(): LimitClause {
    const count = parseInt(
      this.consume(TokenType.NUMBER, 'Expected limit count').value,
      10,
    );

    let offset: number | undefined;
    if (this.match(TokenType.OFFSET)) {
      offset = parseInt(
        this.consume(TokenType.NUMBER, 'Expected offset value').value,
        10,
      );
    }

    return { count, offset };
  }

  /**
   * Parse expression
   */
  private parseExpression(): MQLExpression {
    return this.parseAdditive();
  }

  /**
   * Parse additive expression
   */
  private parseAdditive(): MQLExpression {
    let left = this.parseMultiplicative();

    while (this.check(TokenType.PLUS) || this.check(TokenType.MINUS)) {
      const operator = this.advance().type === TokenType.PLUS ? '+' : '-';
      const right = this.parseMultiplicative();
      left = {
        type: 'binary',
        operator: operator as '+' | '-',
        left,
        right,
      };
    }

    return left;
  }

  /**
   * Parse multiplicative expression
   */
  private parseMultiplicative(): MQLExpression {
    let left = this.parseUnary();

    while (this.check(TokenType.STAR) || this.check(TokenType.SLASH)) {
      const operator = this.advance().type === TokenType.STAR ? '*' : '/';
      const right = this.parseUnary();
      left = {
        type: 'binary',
        operator: operator as '*' | '/',
        left,
        right,
      };
    }

    return left;
  }

  /**
   * Parse unary expression
   */
  private parseUnary(): MQLExpression {
    if (this.match(TokenType.MINUS)) {
      const operand = this.parseUnary();
      return {
        type: 'unary',
        operator: '-',
        operand,
      };
    }

    return this.parsePostfix();
  }

  /**
   * Parse postfix expression (property access, array access, function call)
   */
  private parsePostfix(): MQLExpression {
    let expr = this.parsePrimary();

    while (true) {
      if (this.match(TokenType.DOT)) {
        const property = this.consume(TokenType.IDENTIFIER, 'Expected property name').value;
        expr = {
          type: 'property',
          object: expr,
          property,
        };
      } else if (this.match(TokenType.LBRACKET)) {
        const index = this.parseExpression();
        this.consume(TokenType.RBRACKET, "Expected ']' after index");
        expr = {
          type: 'array',
          array: expr,
          index,
        };
      } else if (this.check(TokenType.LPAREN) && expr.type === 'field') {
        // Convert field reference to function call
        this.advance();
        const args: MQLExpression[] = [];
        if (!this.check(TokenType.RPAREN)) {
          do {
            args.push(this.parseExpression());
          } while (this.match(TokenType.COMMA));
        }
        this.consume(TokenType.RPAREN, "Expected ')' after function arguments");
        expr = {
          type: 'function',
          name: (expr as FieldReference).name,
          arguments: args,
        };
      } else {
        break;
      }
    }

    return expr;
  }

  /**
   * Parse primary expression
   */
  private parsePrimary(): MQLExpression {
    // Wildcard
    if (this.match(TokenType.STAR)) {
      return { type: 'wildcard' };
    }

    // Parenthesized expression
    if (this.match(TokenType.LPAREN)) {
      const expr = this.parseExpression();
      this.consume(TokenType.RPAREN, "Expected ')' after expression");
      return expr;
    }

    // Literals
    if (this.match(TokenType.STRING)) {
      return {
        type: 'literal',
        value: this.previous().value,
        dataType: 'string',
      };
    }

    if (this.match(TokenType.NUMBER)) {
      const value = this.previous().value;
      return {
        type: 'literal',
        value: value.includes('.') ? parseFloat(value) : parseInt(value, 10),
        dataType: 'number',
      };
    }

    if (this.match(TokenType.REGEX)) {
      return {
        type: 'literal',
        value: this.previous().value,
        dataType: 'regex',
      };
    }

    if (this.match(TokenType.TRUE)) {
      return { type: 'literal', value: true, dataType: 'boolean' };
    }

    if (this.match(TokenType.FALSE)) {
      return { type: 'literal', value: false, dataType: 'boolean' };
    }

    if (this.match(TokenType.NULL)) {
      return { type: 'literal', value: null, dataType: 'null' };
    }

    // Identifier (field reference)
    if (this.match(TokenType.IDENTIFIER)) {
      const name = this.previous().value;
      return { type: 'field', name };
    }

    throw this.error(this.peek(), 'Expected expression');
  }

  /**
   * Check if next token is a comparison operator
   */
  private checkComparison(): boolean {
    return (
      this.check(TokenType.EQ) ||
      this.check(TokenType.NE) ||
      this.check(TokenType.LT) ||
      this.check(TokenType.LE) ||
      this.check(TokenType.GT) ||
      this.check(TokenType.GE)
    );
  }

  /**
   * Parse comparison operator
   */
  private parseComparisonOperator(): '=' | '!=' | '<' | '<=' | '>' | '>=' {
    if (this.match(TokenType.EQ)) return '=';
    if (this.match(TokenType.NE)) return '!=';
    if (this.match(TokenType.LT)) return '<';
    if (this.match(TokenType.LE)) return '<=';
    if (this.match(TokenType.GT)) return '>';
    if (this.match(TokenType.GE)) return '>=';
    throw this.error(this.peek(), 'Expected comparison operator');
  }

  /**
   * Check if current token is a keyword (not usable as alias)
   */
  private checkKeyword(): boolean {
    const type = this.peek().type;
    return (
      type === TokenType.SELECT ||
      type === TokenType.FROM ||
      type === TokenType.WHERE ||
      type === TokenType.ORDER ||
      type === TokenType.BY ||
      type === TokenType.LIMIT ||
      type === TokenType.AND ||
      type === TokenType.OR ||
      type === TokenType.NOT
    );
  }

  // Token navigation helpers

  private match(...types: TokenType[]): boolean {
    for (const type of types) {
      if (this.check(type)) {
        this.advance();
        return true;
      }
    }
    return false;
  }

  private check(type: TokenType): boolean {
    if (this.isAtEnd()) return false;
    return this.peek().type === type;
  }

  private advance(): Token {
    if (!this.isAtEnd()) this.current++;
    return this.previous();
  }

  private peek(): Token {
    return this.tokens[this.current];
  }

  private previous(): Token {
    return this.tokens[this.current - 1];
  }

  private isAtEnd(): boolean {
    return this.peek().type === TokenType.EOF;
  }

  private consume(type: TokenType, message: string): Token {
    if (this.check(type)) return this.advance();
    throw this.error(this.peek(), message);
  }

  private error(token: Token, message: string): Error {
    this.errors.push({
      message,
      line: token.line,
      column: token.column,
      type: 'syntax',
    });
    return new Error(message);
  }
}

/**
 * Parse MQL query
 */
export function parse(source: string): ParseResult {
  const parser = new MQLParser();
  return parser.parse(source);
}
