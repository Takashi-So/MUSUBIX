/**
 * Book Entity and ISBN Value Object
 * @requirements REQ-BOOK-001, REQ-BOOK-004
 * @design DES-LIBRARY-001 §3.1
 * @task TSK-LIB-001
 */

/**
 * BookId - 書籍ID値オブジェクト
 */
export class BookId {
  private static counter = 0;

  constructor(public readonly value: string) {}

  static generate(): BookId {
    BookId.counter++;
    const timestamp = Date.now();
    const seq = String(BookId.counter).padStart(3, '0');
    return new BookId(`BOOK-${timestamp}-${seq}`);
  }

  equals(other: BookId): boolean {
    return this.value === other.value;
  }

  toString(): string {
    return this.value;
  }
}

/**
 * ISBN - ISBN-13値オブジェクト
 * @requirements REQ-BOOK-001 (ISBN-13形式)
 */
export class ISBN {
  public readonly value: string;

  constructor(isbn: string) {
    const normalized = this.normalize(isbn);
    
    if (!this.isValidFormat(normalized)) {
      throw new Error('Invalid ISBN format');
    }
    
    if (!this.isValidChecksum(normalized)) {
      throw new Error('Invalid ISBN checksum');
    }
    
    this.value = normalized;
  }

  private normalize(isbn: string): string {
    return isbn.replace(/[-\s]/g, '');
  }

  private isValidFormat(isbn: string): boolean {
    return /^\d{13}$/.test(isbn);
  }

  private isValidChecksum(isbn: string): boolean {
    const digits = isbn.split('').map(Number);
    let sum = 0;
    for (let i = 0; i < 12; i++) {
      sum += digits[i] * (i % 2 === 0 ? 1 : 3);
    }
    const checkDigit = (10 - (sum % 10)) % 10;
    return checkDigit === digits[12];
  }

  equals(other: ISBN): boolean {
    return this.value === other.value;
  }

  toString(): string {
    // Format as 978-X-XX-XXXXXX-X
    const v = this.value;
    return `${v.slice(0, 3)}-${v.slice(3, 4)}-${v.slice(4, 6)}-${v.slice(6, 12)}-${v.slice(12)}`;
  }
}

/**
 * CreateBookParams - 書籍作成パラメータ
 */
export interface CreateBookParams {
  isbn: ISBN;
  title: string;
  author: string;
  publisher: string;
  publishYear: number;
  category: string;
  shelfLocation: string;
}

/**
 * UpdateBookParams - 書籍更新パラメータ
 */
export interface UpdateBookParams {
  title?: string;
  author?: string;
  publisher?: string;
  category?: string;
  shelfLocation?: string;
}

/**
 * Book - 書籍エンティティ（集約ルート）
 * @requirements REQ-BOOK-001, REQ-BOOK-002, REQ-BOOK-003
 * @design DES-LIBRARY-001 §3.1 Book Entity (Aggregate Root)
 */
export class Book {
  private constructor(
    public readonly id: BookId,
    public readonly isbn: ISBN,
    private _title: string,
    private _author: string,
    private _publisher: string,
    private _publishYear: number,
    private _category: string,
    private _shelfLocation: string,
    public readonly createdAt: Date,
    private _updatedAt: Date
  ) {}

  static create(params: CreateBookParams): Book {
    // Validation: REQ-BOOK-001 (タイトル最大500文字)
    if (params.title.length > 500) {
      throw new Error('Title must not exceed 500 characters');
    }

    // Validation: 出版年4桁
    const currentYear = new Date().getFullYear();
    if (params.publishYear < 1000 || params.publishYear > currentYear + 1) {
      throw new Error('Invalid publish year');
    }

    const now = new Date();
    return new Book(
      BookId.generate(),
      params.isbn,
      params.title,
      params.author,
      params.publisher,
      params.publishYear,
      params.category,
      params.shelfLocation,
      now,
      now
    );
  }

  // Getters
  get title(): string {
    return this._title;
  }

  get author(): string {
    return this._author;
  }

  get publisher(): string {
    return this._publisher;
  }

  get publishYear(): number {
    return this._publishYear;
  }

  get category(): string {
    return this._category;
  }

  get shelfLocation(): string {
    return this._shelfLocation;
  }

  get updatedAt(): Date {
    return this._updatedAt;
  }

  /**
   * 書籍情報を更新
   * @requirements REQ-BOOK-002 (バリデーション後更新)
   */
  update(params: UpdateBookParams): void {
    if (params.title !== undefined) {
      if (params.title.length > 500) {
        throw new Error('Title must not exceed 500 characters');
      }
      this._title = params.title;
    }
    if (params.author !== undefined) {
      this._author = params.author;
    }
    if (params.publisher !== undefined) {
      this._publisher = params.publisher;
    }
    if (params.category !== undefined) {
      this._category = params.category;
    }
    if (params.shelfLocation !== undefined) {
      this._shelfLocation = params.shelfLocation;
    }
    this._updatedAt = new Date();
  }

  /**
   * 復元用ファクトリメソッド（リポジトリから）
   */
  static reconstruct(
    id: BookId,
    isbn: ISBN,
    title: string,
    author: string,
    publisher: string,
    publishYear: number,
    category: string,
    shelfLocation: string,
    createdAt: Date,
    updatedAt: Date
  ): Book {
    return new Book(
      id,
      isbn,
      title,
      author,
      publisher,
      publishYear,
      category,
      shelfLocation,
      createdAt,
      updatedAt
    );
  }
}
