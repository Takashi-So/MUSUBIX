/**
 * @fileoverview MQL Lexer - Tokenize MQL queries
 * @module @nahisaho/musubix-security/mql/lexer
 * @trace TSK-018, REQ-SEC-MQL-001
 */

/**
 * Token types
 */
export enum TokenType {
  // Keywords
  SELECT = 'SELECT',
  FROM = 'FROM',
  WHERE = 'WHERE',
  AND = 'AND',
  OR = 'OR',
  NOT = 'NOT',
  IN = 'IN',
  LIKE = 'LIKE',
  MATCHES = 'MATCHES',
  EXISTS = 'EXISTS',
  AS = 'AS',
  ORDER = 'ORDER',
  BY = 'BY',
  ASC = 'ASC',
  DESC = 'DESC',
  LIMIT = 'LIMIT',
  OFFSET = 'OFFSET',
  DISTINCT = 'DISTINCT',
  TRUE = 'TRUE',
  FALSE = 'FALSE',
  NULL = 'NULL',

  // Data sources
  FUNCTIONS = 'FUNCTIONS',
  CLASSES = 'CLASSES',
  CALLS = 'CALLS',
  VARIABLES = 'VARIABLES',
  DATAFLOW = 'DATAFLOW',
  CONTROLFLOW = 'CONTROLFLOW',
  AST = 'AST',
  SYMBOLS = 'SYMBOLS',

  // Identifiers and literals
  IDENTIFIER = 'IDENTIFIER',
  STRING = 'STRING',
  NUMBER = 'NUMBER',
  REGEX = 'REGEX',

  // Operators
  EQ = 'EQ',           // =
  NE = 'NE',           // !=
  LT = 'LT',           // <
  LE = 'LE',           // <=
  GT = 'GT',           // >
  GE = 'GE',           // >=
  PLUS = 'PLUS',       // +
  MINUS = 'MINUS',     // -
  STAR = 'STAR',       // *
  SLASH = 'SLASH',     // /

  // Punctuation
  LPAREN = 'LPAREN',   // (
  RPAREN = 'RPAREN',   // )
  LBRACKET = 'LBRACKET', // [
  RBRACKET = 'RBRACKET', // ]
  COMMA = 'COMMA',     // ,
  DOT = 'DOT',         // .
  COLON = 'COLON',     // :

  // Special
  EOF = 'EOF',
  ERROR = 'ERROR',
}

/**
 * Token
 */
export interface Token {
  /** Token type */
  type: TokenType;
  /** Token value */
  value: string;
  /** Line number (1-based) */
  line: number;
  /** Column number (1-based) */
  column: number;
  /** Start position in source */
  start: number;
  /** End position in source */
  end: number;
}

/**
 * Lexer error
 */
export interface LexerError {
  /** Error message */
  message: string;
  /** Line number */
  line: number;
  /** Column number */
  column: number;
  /** Position in source */
  position: number;
}

/**
 * Keywords mapping
 */
const KEYWORDS: Record<string, TokenType> = {
  select: TokenType.SELECT,
  from: TokenType.FROM,
  where: TokenType.WHERE,
  and: TokenType.AND,
  or: TokenType.OR,
  not: TokenType.NOT,
  in: TokenType.IN,
  like: TokenType.LIKE,
  matches: TokenType.MATCHES,
  exists: TokenType.EXISTS,
  as: TokenType.AS,
  order: TokenType.ORDER,
  by: TokenType.BY,
  asc: TokenType.ASC,
  desc: TokenType.DESC,
  limit: TokenType.LIMIT,
  offset: TokenType.OFFSET,
  distinct: TokenType.DISTINCT,
  true: TokenType.TRUE,
  false: TokenType.FALSE,
  null: TokenType.NULL,
  functions: TokenType.FUNCTIONS,
  classes: TokenType.CLASSES,
  calls: TokenType.CALLS,
  variables: TokenType.VARIABLES,
  dataflow: TokenType.DATAFLOW,
  controlflow: TokenType.CONTROLFLOW,
  ast: TokenType.AST,
  symbols: TokenType.SYMBOLS,
};

/**
 * MQL Lexer
 */
export class MQLLexer {
  private source: string;
  private position = 0;
  private line = 1;
  private column = 1;
  private errors: LexerError[] = [];

  /**
   * Create a new lexer
   */
  constructor(source: string) {
    this.source = source;
  }

  /**
   * Tokenize the source
   */
  tokenize(): { tokens: Token[]; errors: LexerError[] } {
    const tokens: Token[] = [];
    this.position = 0;
    this.line = 1;
    this.column = 1;
    this.errors = [];

    while (!this.isAtEnd()) {
      this.skipWhitespace();
      if (this.isAtEnd()) break;

      const token = this.scanToken();
      if (token) {
        tokens.push(token);
      }
    }

    // Add EOF token
    tokens.push({
      type: TokenType.EOF,
      value: '',
      line: this.line,
      column: this.column,
      start: this.position,
      end: this.position,
    });

    return { tokens, errors: this.errors };
  }

  /**
   * Scan next token
   */
  private scanToken(): Token | null {
    const start = this.position;
    const startLine = this.line;
    const startColumn = this.column;
    const char = this.advance();

    switch (char) {
      // Single-character tokens
      case '(':
        return this.makeToken(TokenType.LPAREN, char, start, startLine, startColumn);
      case ')':
        return this.makeToken(TokenType.RPAREN, char, start, startLine, startColumn);
      case '[':
        return this.makeToken(TokenType.LBRACKET, char, start, startLine, startColumn);
      case ']':
        return this.makeToken(TokenType.RBRACKET, char, start, startLine, startColumn);
      case ',':
        return this.makeToken(TokenType.COMMA, char, start, startLine, startColumn);
      case '.':
        return this.makeToken(TokenType.DOT, char, start, startLine, startColumn);
      case ':':
        return this.makeToken(TokenType.COLON, char, start, startLine, startColumn);
      case '+':
        return this.makeToken(TokenType.PLUS, char, start, startLine, startColumn);
      case '-':
        return this.makeToken(TokenType.MINUS, char, start, startLine, startColumn);
      case '*':
        return this.makeToken(TokenType.STAR, char, start, startLine, startColumn);
      case '/':
        // Check for comment
        if (this.peek() === '/') {
          this.skipLineComment();
          return null;
        } else if (this.peek() === '*') {
          this.skipBlockComment();
          return null;
        }
        return this.makeToken(TokenType.SLASH, char, start, startLine, startColumn);

      // Two-character tokens
      case '=':
        return this.makeToken(TokenType.EQ, char, start, startLine, startColumn);
      case '!':
        if (this.match('=')) {
          return this.makeToken(TokenType.NE, '!=', start, startLine, startColumn);
        }
        this.addError(`Unexpected character: ${char}`);
        return null;
      case '<':
        if (this.match('=')) {
          return this.makeToken(TokenType.LE, '<=', start, startLine, startColumn);
        }
        return this.makeToken(TokenType.LT, char, start, startLine, startColumn);
      case '>':
        if (this.match('=')) {
          return this.makeToken(TokenType.GE, '>=', start, startLine, startColumn);
        }
        return this.makeToken(TokenType.GT, char, start, startLine, startColumn);

      // Strings
      case '"':
      case "'":
        return this.scanString(char, start, startLine, startColumn);

      // Regex
      case '`':
        return this.scanRegex(start, startLine, startColumn);

      default:
        // Numbers
        if (this.isDigit(char)) {
          return this.scanNumber(start, startLine, startColumn);
        }

        // Identifiers and keywords
        if (this.isAlpha(char)) {
          return this.scanIdentifier(start, startLine, startColumn);
        }

        this.addError(`Unexpected character: ${char}`);
        return null;
    }
  }

  /**
   * Scan string literal
   */
  private scanString(
    quote: string,
    start: number,
    startLine: number,
    startColumn: number,
  ): Token {
    let value = '';

    while (!this.isAtEnd() && this.peek() !== quote) {
      if (this.peek() === '\\') {
        this.advance();
        if (!this.isAtEnd()) {
          const escaped = this.advance();
          switch (escaped) {
            case 'n':
              value += '\n';
              break;
            case 't':
              value += '\t';
              break;
            case 'r':
              value += '\r';
              break;
            case '\\':
              value += '\\';
              break;
            case '"':
              value += '"';
              break;
            case "'":
              value += "'";
              break;
            default:
              value += escaped;
          }
        }
      } else if (this.peek() === '\n') {
        this.addError('Unterminated string');
        break;
      } else {
        value += this.advance();
      }
    }

    if (this.isAtEnd()) {
      this.addError('Unterminated string');
    } else {
      this.advance(); // Closing quote
    }

    return this.makeToken(TokenType.STRING, value, start, startLine, startColumn);
  }

  /**
   * Scan regex literal
   */
  private scanRegex(start: number, startLine: number, startColumn: number): Token {
    let value = '';

    while (!this.isAtEnd() && this.peek() !== '`') {
      if (this.peek() === '\\') {
        value += this.advance();
        if (!this.isAtEnd()) {
          value += this.advance();
        }
      } else {
        value += this.advance();
      }
    }

    if (this.isAtEnd()) {
      this.addError('Unterminated regex');
    } else {
      this.advance(); // Closing backtick
    }

    return this.makeToken(TokenType.REGEX, value, start, startLine, startColumn);
  }

  /**
   * Scan number literal
   */
  private scanNumber(start: number, startLine: number, startColumn: number): Token {
    // Back up to include first digit
    this.position--;
    this.column--;

    let value = '';

    while (!this.isAtEnd() && this.isDigit(this.peek())) {
      value += this.advance();
    }

    // Check for decimal
    if (this.peek() === '.' && this.isDigit(this.peekNext())) {
      value += this.advance(); // .
      while (!this.isAtEnd() && this.isDigit(this.peek())) {
        value += this.advance();
      }
    }

    // Check for exponent
    if (this.peek() === 'e' || this.peek() === 'E') {
      value += this.advance();
      if (this.peek() === '+' || this.peek() === '-') {
        value += this.advance();
      }
      while (!this.isAtEnd() && this.isDigit(this.peek())) {
        value += this.advance();
      }
    }

    return this.makeToken(TokenType.NUMBER, value, start, startLine, startColumn);
  }

  /**
   * Scan identifier or keyword
   */
  private scanIdentifier(start: number, startLine: number, startColumn: number): Token {
    // Back up to include first character
    this.position--;
    this.column--;

    let value = '';

    while (!this.isAtEnd() && this.isAlphaNumeric(this.peek())) {
      value += this.advance();
    }

    // Check for keyword
    const keyword = KEYWORDS[value.toLowerCase()];
    const type = keyword ?? TokenType.IDENTIFIER;

    return this.makeToken(type, value, start, startLine, startColumn);
  }

  /**
   * Skip whitespace
   */
  private skipWhitespace(): void {
    while (!this.isAtEnd()) {
      const char = this.peek();
      switch (char) {
        case ' ':
        case '\t':
        case '\r':
          this.advance();
          break;
        case '\n':
          this.advance();
          this.line++;
          this.column = 1;
          break;
        default:
          return;
      }
    }
  }

  /**
   * Skip line comment
   */
  private skipLineComment(): void {
    while (!this.isAtEnd() && this.peek() !== '\n') {
      this.advance();
    }
  }

  /**
   * Skip block comment
   */
  private skipBlockComment(): void {
    this.advance(); // *
    while (!this.isAtEnd()) {
      if (this.peek() === '*' && this.peekNext() === '/') {
        this.advance(); // *
        this.advance(); // /
        return;
      }
      if (this.peek() === '\n') {
        this.line++;
        this.column = 0;
      }
      this.advance();
    }
    this.addError('Unterminated block comment');
  }

  /**
   * Make a token
   */
  private makeToken(
    type: TokenType,
    value: string,
    start: number,
    line: number,
    column: number,
  ): Token {
    return {
      type,
      value,
      line,
      column,
      start,
      end: this.position,
    };
  }

  /**
   * Advance and return current character
   */
  private advance(): string {
    const char = this.source[this.position];
    this.position++;
    this.column++;
    return char;
  }

  /**
   * Peek current character
   */
  private peek(): string {
    if (this.isAtEnd()) return '\0';
    return this.source[this.position];
  }

  /**
   * Peek next character
   */
  private peekNext(): string {
    if (this.position + 1 >= this.source.length) return '\0';
    return this.source[this.position + 1];
  }

  /**
   * Match and consume character
   */
  private match(expected: string): boolean {
    if (this.isAtEnd()) return false;
    if (this.source[this.position] !== expected) return false;
    this.position++;
    this.column++;
    return true;
  }

  /**
   * Check if at end
   */
  private isAtEnd(): boolean {
    return this.position >= this.source.length;
  }

  /**
   * Check if character is digit
   */
  private isDigit(char: string): boolean {
    return char >= '0' && char <= '9';
  }

  /**
   * Check if character is alpha
   */
  private isAlpha(char: string): boolean {
    return (char >= 'a' && char <= 'z') || (char >= 'A' && char <= 'Z') || char === '_';
  }

  /**
   * Check if character is alphanumeric
   */
  private isAlphaNumeric(char: string): boolean {
    return this.isAlpha(char) || this.isDigit(char);
  }

  /**
   * Add error
   */
  private addError(message: string): void {
    this.errors.push({
      message,
      line: this.line,
      column: this.column,
      position: this.position,
    });
  }
}

/**
 * Tokenize MQL query
 */
export function tokenize(source: string): { tokens: Token[]; errors: LexerError[] } {
  const lexer = new MQLLexer(source);
  return lexer.tokenize();
}
