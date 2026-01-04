/**
 * Result Type - Rust-inspired error handling
 * Traces to: MUSUBIX Best Practices
 */
export class ValidationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'ValidationError';
  }
}

export class DomainError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'DomainError';
  }
}

export type Result<T, E extends Error> = Ok<T, E> | Err<T, E>;

class Ok<T, E extends Error> {
  readonly value: T;

  constructor(value: T) {
    this.value = value;
  }

  isOk(): this is Ok<T, E> {
    return true;
  }

  isErr(): this is Err<T, E> {
    return false;
  }

  unwrap(): T {
    return this.value;
  }

  unwrapErr(): E {
    throw new Error('Called unwrapErr on Ok');
  }

  map<U>(fn: (value: T) => U): Result<U, E> {
    return ok(fn(this.value));
  }
}

class Err<T, E extends Error> {
  readonly error: E;

  constructor(error: E) {
    this.error = error;
  }

  isOk(): this is Ok<T, E> {
    return false;
  }

  isErr(): this is Err<T, E> {
    return true;
  }

  unwrap(): T {
    throw this.error;
  }

  unwrapErr(): E {
    return this.error;
  }

  map<U>(_fn: (value: T) => U): Result<U, E> {
    return err(this.error);
  }
}

export function ok<T, E extends Error>(value: T): Result<T, E> {
  return new Ok(value);
}

export function err<T, E extends Error>(error: E): Result<T, E> {
  return new Err(error);
}
