/**
 * Priority Queue
 * @module @nahisaho/musubix-neural-search
 * @description Max-heap priority queue for search
 */

import type { IPriorityQueue, PriorityItem } from '../types.js';

/**
 * Max-heap priority queue implementation
 */
export class PriorityQueue<T> implements IPriorityQueue<T> {
  private heap: PriorityItem<T>[];

  constructor() {
    this.heap = [];
  }

  /**
   * Add item with priority
   */
  push(item: T, priority: number): void {
    this.heap.push({ item, priority });
    this.bubbleUp(this.heap.length - 1);
  }

  /**
   * Remove and return highest priority item
   */
  pop(): T | undefined {
    if (this.heap.length === 0) {
      return undefined;
    }

    const top = this.heap[0];
    const last = this.heap.pop();

    if (this.heap.length > 0 && last) {
      this.heap[0] = last;
      this.bubbleDown(0);
    }

    return top.item;
  }

  /**
   * Peek at highest priority item
   */
  peek(): T | undefined {
    return this.heap[0]?.item;
  }

  /**
   * Get queue size
   */
  size(): number {
    return this.heap.length;
  }

  /**
   * Check if empty
   */
  isEmpty(): boolean {
    return this.heap.length === 0;
  }

  /**
   * Clear the queue
   */
  clear(): void {
    this.heap = [];
  }

  /**
   * Get all items sorted by priority
   */
  toArray(): T[] {
    return [...this.heap]
      .sort((a, b) => b.priority - a.priority)
      .map((item) => item.item);
  }

  /**
   * Bubble up the element at index
   */
  private bubbleUp(index: number): void {
    while (index > 0) {
      const parentIdx = Math.floor((index - 1) / 2);
      if (this.heap[parentIdx].priority >= this.heap[index].priority) {
        break;
      }
      this.swap(parentIdx, index);
      index = parentIdx;
    }
  }

  /**
   * Bubble down the element at index
   */
  private bubbleDown(index: number): void {
    const length = this.heap.length;

    while (true) {
      const leftIdx = 2 * index + 1;
      const rightIdx = 2 * index + 2;
      let largestIdx = index;

      if (
        leftIdx < length &&
        this.heap[leftIdx].priority > this.heap[largestIdx].priority
      ) {
        largestIdx = leftIdx;
      }

      if (
        rightIdx < length &&
        this.heap[rightIdx].priority > this.heap[largestIdx].priority
      ) {
        largestIdx = rightIdx;
      }

      if (largestIdx === index) {
        break;
      }

      this.swap(index, largestIdx);
      index = largestIdx;
    }
  }

  /**
   * Swap two elements
   */
  private swap(i: number, j: number): void {
    const temp = this.heap[i];
    this.heap[i] = this.heap[j];
    this.heap[j] = temp;
  }
}
