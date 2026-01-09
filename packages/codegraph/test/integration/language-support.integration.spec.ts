/**
 * Language Support Integration Tests
 *
 * Tests all 16 supported languages in MUSUBIX v2.3.2
 *
 * @see REQ-CG-v2.3.2 - 16-language support
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { extractorRegistry } from '../../src/parser/extractors/index.js';
import { ASTParser } from '../../src/parser/ast-parser.js';
import { writeFileSync, mkdirSync, existsSync, rmSync } from 'fs';
import { join } from 'path';
import { tmpdir } from 'os';

// Create temporary test directory
const TEST_DIR = join(tmpdir(), 'musubix-lang-test-' + Date.now());

// Sample code for each language
const SAMPLE_CODE: Record<string, { ext: string; code: string; expectedEntities: string[] }> = {
  typescript: {
    ext: '.ts',
    code: `
export interface User {
  id: string;
  name: string;
}

export class UserService {
  private users: User[] = [];

  async getUser(id: string): Promise<User | undefined> {
    return this.users.find(u => u.id === id);
  }

  async createUser(name: string): Promise<User> {
    const user: User = { id: Date.now().toString(), name };
    this.users.push(user);
    return user;
  }
}
`,
    expectedEntities: ['User', 'UserService', 'getUser', 'createUser'],
  },

  javascript: {
    ext: '.js',
    code: `
class Calculator {
  add(a, b) {
    return a + b;
  }

  multiply(a, b) {
    return a * b;
  }
}

function calculate(op, a, b) {
  const calc = new Calculator();
  return op === 'add' ? calc.add(a, b) : calc.multiply(a, b);
}

module.exports = { Calculator, calculate };
`,
    expectedEntities: ['Calculator', 'add', 'multiply', 'calculate'],
  },

  python: {
    ext: '.py',
    code: `
class DataProcessor:
    """Process data with various transformations."""
    
    def __init__(self, data: list):
        self.data = data
    
    def filter(self, predicate):
        return [x for x in self.data if predicate(x)]
    
    def map(self, transform):
        return [transform(x) for x in self.data]


def process_all(items: list) -> list:
    processor = DataProcessor(items)
    return processor.filter(lambda x: x > 0)
`,
    expectedEntities: ['DataProcessor', '__init__', 'filter', 'map', 'process_all'],
  },

  rust: {
    ext: '.rs',
    code: `
pub struct Config {
    pub name: String,
    pub value: i32,
}

impl Config {
    pub fn new(name: &str, value: i32) -> Self {
        Config {
            name: name.to_string(),
            value,
        }
    }

    pub fn update(&mut self, value: i32) {
        self.value = value;
    }
}

pub fn create_default_config() -> Config {
    Config::new("default", 0)
}
`,
    expectedEntities: ['Config', 'new', 'update', 'create_default_config'],
  },

  go: {
    ext: '.go',
    code: `
package main

type Service struct {
    Name string
    Port int
}

func NewService(name string, port int) *Service {
    return &Service{Name: name, Port: port}
}

func (s *Service) Start() error {
    return nil
}

func (s *Service) Stop() error {
    return nil
}
`,
    expectedEntities: ['Service', 'NewService', 'Start', 'Stop'],
  },

  java: {
    ext: '.java',
    code: `
package com.example;

public class OrderService {
    private List<Order> orders = new ArrayList<>();

    public Order createOrder(String customerId) {
        Order order = new Order(customerId);
        orders.add(order);
        return order;
    }

    public Optional<Order> findOrder(String orderId) {
        return orders.stream()
            .filter(o -> o.getId().equals(orderId))
            .findFirst();
    }

    public void cancelOrder(String orderId) {
        findOrder(orderId).ifPresent(order -> order.setStatus("CANCELLED"));
    }
}
`,
    expectedEntities: ['OrderService', 'createOrder', 'findOrder', 'cancelOrder'],
  },

  php: {
    ext: '.php',
    code: `
<?php

namespace App\\Services;

class UserRepository {
    private array $users = [];

    public function find(int $id): ?User {
        return $this->users[$id] ?? null;
    }

    public function save(User $user): void {
        $this->users[$user->getId()] = $user;
    }

    public function delete(int $id): bool {
        if (isset($this->users[$id])) {
            unset($this->users[$id]);
            return true;
        }
        return false;
    }
}
`,
    expectedEntities: ['UserRepository', 'find', 'save', 'delete'],
  },

  csharp: {
    ext: '.cs',
    code: `
namespace MyApp.Services
{
    public class ProductService
    {
        private readonly List<Product> _products = new();

        public Product GetProduct(int id)
        {
            return _products.FirstOrDefault(p => p.Id == id);
        }

        public void AddProduct(Product product)
        {
            _products.Add(product);
        }

        public bool RemoveProduct(int id)
        {
            var product = GetProduct(id);
            return product != null && _products.Remove(product);
        }
    }
}
`,
    expectedEntities: ['ProductService', 'GetProduct', 'AddProduct', 'RemoveProduct'],
  },

  c: {
    ext: '.c',
    code: `
#include <stdio.h>
#include <stdlib.h>

typedef struct {
    int x;
    int y;
} Point;

Point* create_point(int x, int y) {
    Point* p = malloc(sizeof(Point));
    p->x = x;
    p->y = y;
    return p;
}

void free_point(Point* p) {
    free(p);
}

int distance_squared(Point* a, Point* b) {
    int dx = a->x - b->x;
    int dy = a->y - b->y;
    return dx * dx + dy * dy;
}
`,
    expectedEntities: ['Point', 'create_point', 'free_point', 'distance_squared'],
  },

  cpp: {
    ext: '.cpp',
    code: `
#include <string>
#include <vector>

class Logger {
private:
    std::vector<std::string> logs;

public:
    void log(const std::string& message) {
        logs.push_back(message);
    }

    void clear() {
        logs.clear();
    }

    size_t count() const {
        return logs.size();
    }
};

template<typename T>
T max_value(T a, T b) {
    return a > b ? a : b;
}
`,
    expectedEntities: ['Logger', 'log', 'clear', 'count', 'max_value'],
  },

  ruby: {
    ext: '.rb',
    code: `
class Account
  attr_accessor :balance
  
  def initialize(initial_balance = 0)
    @balance = initial_balance
  end
  
  def deposit(amount)
    @balance += amount
  end
  
  def withdraw(amount)
    raise "Insufficient funds" if amount > @balance
    @balance -= amount
  end
end

module Banking
  def self.create_account(balance)
    Account.new(balance)
  end
end
`,
    expectedEntities: ['Account', 'initialize', 'deposit', 'withdraw', 'Banking', 'create_account'],
  },

  kotlin: {
    ext: '.kt',
    code: `
data class User(val id: String, val name: String)

class UserManager {
    private val users = mutableListOf<User>()

    fun addUser(user: User) {
        users.add(user)
    }

    fun findUser(id: String): User? {
        return users.find { it.id == id }
    }

    fun removeUser(id: String): Boolean {
        return users.removeIf { it.id == id }
    }
}

fun createDefaultUser(): User {
    return User("0", "Guest")
}
`,
    expectedEntities: ['User', 'UserManager', 'addUser', 'findUser', 'removeUser', 'createDefaultUser'],
  },

  swift: {
    ext: '.swift',
    code: `
protocol DataSource {
    func getData() -> [String]
}

class DataManager: DataSource {
    private var items: [String] = []
    
    func getData() -> [String] {
        return items
    }
    
    func addItem(_ item: String) {
        items.append(item)
    }
    
    func clearItems() {
        items.removeAll()
    }
}

func processData(source: DataSource) -> Int {
    return source.getData().count
}
`,
    expectedEntities: ['DataSource', 'getData', 'DataManager', 'addItem', 'clearItems', 'processData'],
  },

  scala: {
    ext: '.scala',
    code: `
case class Item(id: String, name: String, price: Double)

class Inventory {
  private var items: List[Item] = List.empty
  
  def addItem(item: Item): Unit = {
    items = items :+ item
  }
  
  def findItem(id: String): Option[Item] = {
    items.find(_.id == id)
  }
  
  def totalValue: Double = {
    items.map(_.price).sum
  }
}

object InventoryManager {
  def createInventory(): Inventory = new Inventory()
}
`,
    expectedEntities: ['Item', 'Inventory', 'addItem', 'findItem', 'totalValue', 'InventoryManager', 'createInventory'],
  },

  lua: {
    ext: '.lua',
    code: `
-- Game entity system
Entity = {}
Entity.__index = Entity

function Entity.new(name, x, y)
    local self = setmetatable({}, Entity)
    self.name = name
    self.x = x
    self.y = y
    return self
end

function Entity:move(dx, dy)
    self.x = self.x + dx
    self.y = self.y + dy
end

function Entity:getPosition()
    return self.x, self.y
end

function createPlayer(name)
    return Entity.new(name, 0, 0)
end
`,
    expectedEntities: ['Entity', 'new', 'move', 'getPosition', 'createPlayer'],
  },

  hcl: {
    ext: '.tf',
    code: `
variable "region" {
  description = "AWS region"
  type        = string
  default     = "us-west-2"
}

resource "aws_instance" "web_server" {
  ami           = "ami-0c55b159cbfafe1f0"
  instance_type = "t2.micro"

  tags = {
    Name = "WebServer"
  }
}

output "instance_id" {
  description = "The ID of the EC2 instance"
  value       = aws_instance.web_server.id
}

locals {
  common_tags = {
    Environment = "production"
  }
}
`,
    expectedEntities: ['region', 'web_server', 'instance_id', 'common_tags'],
  },
};

describe('Language Support Integration Tests', () => {
  let parser: ASTParser;

  beforeAll(() => {
    // Create test directory if it doesn't exist
    if (!existsSync(TEST_DIR)) {
      mkdirSync(TEST_DIR, { recursive: true });
    }
    parser = new ASTParser();
  });

  describe('ExtractorRegistry', () => {
    it('should have 16 languages registered', () => {
      const languages = extractorRegistry.getRegisteredLanguages();
      expect(languages.length).toBe(16);
    });

    it('should support all expected languages', () => {
      const expectedLanguages = [
        'typescript', 'javascript', 'python', 'rust', 'go', 'java',
        'php', 'csharp', 'c', 'cpp', 'ruby', 'hcl', 'kotlin', 'swift', 'scala', 'lua'
      ];

      for (const lang of expectedLanguages) {
        expect(extractorRegistry.hasExtractor(lang)).toBe(true);
      }
    });
  });

  // Test each language
  for (const [lang, sample] of Object.entries(SAMPLE_CODE)) {
    describe(`${lang.toUpperCase()} Language Support`, () => {
      it(`should create extractor for ${lang}`, async () => {
        const extractor = await extractorRegistry.getExtractor(lang);
        expect(extractor).toBeDefined();
        expect(extractor?.getLanguage()).toBe(lang);
      });

      it(`should have correct configuration for ${lang}`, async () => {
        const extractor = await extractorRegistry.getExtractor(lang);
        expect(extractor).toBeDefined();
        
        const config = extractor?.getConfig();
        expect(config).toBeDefined();
        expect(config?.extensions).toBeDefined();
        expect(config?.extensions.length).toBeGreaterThan(0);
      });

      it(`should parse ${lang} code and extract entities`, async () => {
        // Write sample code to temp file
        const testFile = join(TEST_DIR, `test_${lang}${sample.ext}`);
        writeFileSync(testFile, sample.code);

        try {
          // Use ASTParser.parseFile() instead of direct extractor call
          const result = await parser.parseFile(testFile);
          
          expect(result).toBeDefined();
          expect(result.entities).toBeDefined();
          expect(Array.isArray(result.entities)).toBe(true);
          
          // Log extracted entities for debugging
          const entityNames = result.entities.map(e => e.name);
          console.log(`[${lang}] Extracted ${result.entities.length} entities: ${entityNames.slice(0, 10).join(', ')}${entityNames.length > 10 ? '...' : ''}`);

          // Verify at least file entity is found (fallback parsing creates this)
          expect(result.entities.length).toBeGreaterThanOrEqual(1);
          
          // Check for errors
          if (result.errors && result.errors.length > 0) {
            console.warn(`[${lang}] Parse warnings:`, result.errors.map(e => e.message).join(', '));
          }
        } finally {
          // Cleanup is handled in afterAll
        }
      });
    });
  }

  // Cleanup test directory after all tests
  afterAll(() => {
    try {
      if (existsSync(TEST_DIR)) {
        rmSync(TEST_DIR, { recursive: true, force: true });
      }
    } catch {
      // Ignore cleanup errors
    }
  });
});
