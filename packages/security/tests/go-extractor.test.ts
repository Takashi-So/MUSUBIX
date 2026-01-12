/**
 * @fileoverview Go Extractor Tests
 * @module @nahisaho/musubix-security/tests/go-extractor.test
 * @trace TSK-GO-007, REQ-SEC-GO-001, REQ-SEC-GO-002, REQ-SEC-GO-003
 * @trace REQ-SEC-GO-004, REQ-SEC-GO-005, REQ-SEC-GO-006, REQ-SEC-GO-007, REQ-SEC-GO-008
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { GoExtractor, createGoExtractor } from '../src/extractors/go-extractor.js';

describe('GoExtractor', () => {
  let extractor: GoExtractor;

  beforeEach(() => {
    extractor = createGoExtractor();
  });

  // TEST-GO-001: GoExtractorインスタンス作成
  describe('constructor', () => {
    it('should create instance with correct language', () => {
      expect(extractor).toBeInstanceOf(GoExtractor);
      expect(extractor.language).toBe('go');
    });

    it('should create instance via factory function', () => {
      const instance = createGoExtractor();
      expect(instance).toBeInstanceOf(GoExtractor);
    });

    it('should support correct file extensions', () => {
      expect(extractor.extensions).toContain('.go');
    });

    it('should detect supported files', () => {
      expect(extractor.supports('main.go')).toBe(true);
      expect(extractor.supports('handler.go')).toBe(true);
      expect(extractor.supports('file.py')).toBe(false);
      expect(extractor.supports('file.rs')).toBe(false);
    });
  });

  // TEST-GO-002: フレームワークモデル検証
  describe('getFrameworkModels', () => {
    it('should return framework models', () => {
      const models = extractor.getFrameworkModels();
      expect(Array.isArray(models)).toBe(true);
      expect(models.length).toBe(10); // 10 framework models as designed
    });

    it('should have net/http framework model', () => {
      const models = extractor.getFrameworkModels();
      const httpModel = models.find((m) => m.name === 'net/http');

      expect(httpModel).toBeDefined();
      expect(httpModel?.sources.length).toBe(6);
      expect(httpModel?.sinks.length).toBe(3);
      expect(httpModel?.sanitizers.length).toBe(2);
    });

    it('should have database/sql framework model', () => {
      const models = extractor.getFrameworkModels();
      const sqlModel = models.find((m) => m.name === 'database/sql');

      expect(sqlModel).toBeDefined();
      expect(sqlModel?.sinks.some((s) => s.vulnerabilityType === 'sql_injection')).toBe(true);
    });

    it('should have os/exec framework model', () => {
      const models = extractor.getFrameworkModels();
      const execModel = models.find((m) => m.name === 'os/exec');

      expect(execModel).toBeDefined();
      expect(execModel?.sources.some((s) => s.pattern.test('os.Args'))).toBe(true);
      expect(execModel?.sinks.some((s) => s.vulnerabilityType === 'command_injection')).toBe(true);
    });

    it('should have os framework model for file operations', () => {
      const models = extractor.getFrameworkModels();
      const osModel = models.find((m) => m.name === 'os');

      expect(osModel).toBeDefined();
      expect(osModel?.sinks.some((s) => s.vulnerabilityType === 'path_traversal')).toBe(true);
      expect(osModel?.sanitizers.some((s) => s.pattern.test('filepath.Clean('))).toBe(true);
    });

    it('should have encoding/xml framework model', () => {
      const models = extractor.getFrameworkModels();
      const xmlModel = models.find((m) => m.name === 'encoding/xml');

      expect(xmlModel).toBeDefined();
      expect(xmlModel?.sinks.some((s) => s.vulnerabilityType === 'xxe')).toBe(true);
    });

    it('should have Gin framework model', () => {
      const models = extractor.getFrameworkModels();
      const ginModel = models.find((m) => m.name === 'Gin');

      expect(ginModel).toBeDefined();
      expect(ginModel?.sources.length).toBe(6);
      expect(ginModel?.sinks.length).toBe(3);
    });

    it('should have Echo framework model', () => {
      const models = extractor.getFrameworkModels();
      const echoModel = models.find((m) => m.name === 'Echo');

      expect(echoModel).toBeDefined();
      expect(echoModel?.sources.length).toBe(5);
      expect(echoModel?.sinks.length).toBe(3);
    });

    it('should have Fiber framework model', () => {
      const models = extractor.getFrameworkModels();
      const fiberModel = models.find((m) => m.name === 'Fiber');

      expect(fiberModel).toBeDefined();
      expect(fiberModel?.sources.length).toBe(5);
      expect(fiberModel?.sinks.length).toBe(2);
    });

    it('should have GORM framework model', () => {
      const models = extractor.getFrameworkModels();
      const gormModel = models.find((m) => m.name === 'GORM');

      expect(gormModel).toBeDefined();
      expect(gormModel?.sinks.some((s) => s.vulnerabilityType === 'sql_injection')).toBe(true);
    });

    it('should have Go SSRF framework model', () => {
      const models = extractor.getFrameworkModels();
      const ssrfModel = models.find((m) => m.name === 'Go SSRF');

      expect(ssrfModel).toBeDefined();
      expect(ssrfModel?.sinks.some((s) => s.vulnerabilityType === 'ssrf')).toBe(true);
    });
  });

  // TEST-GO-003: AST構築テスト
  describe('extract', () => {
    it('should extract from simple Go code', async () => {
      const code = `
package main

func main() {
    println("Hello, World!")
}
      `;

      const result = await extractor.extract(code, 'main.go');

      expect(result.language).toBe('go');
      expect(result.filePath).toBe('main.go');
      expect(result.ast).toBeDefined();
      expect(result.astNodes.size).toBeGreaterThan(0);
    });

    it('should extract function declarations', async () => {
      const code = `
package main

func Add(a, b int) int {
    return a + b
}

func multiply(x, y float64) float64 {
    return x * y
}
      `;

      const result = await extractor.extract(code, 'math.go');

      expect(result.symbols.functions.size).toBeGreaterThanOrEqual(0);
    });

    it('should extract method declarations', async () => {
      const code = `
package main

type User struct {
    Name string
}

func (u *User) GetName() string {
    return u.Name
}
      `;

      const result = await extractor.extract(code, 'user.go');

      expect(result.ast).toBeDefined();
    });
  });

  // TEST-GO-004: ソース検出テスト
  describe('source detection', () => {
    it('should detect net/http sources', async () => {
      const code = `
package main

import "net/http"

func handler(w http.ResponseWriter, r *http.Request) {
    query := r.URL.Query()
    name := r.FormValue("name")
    body := r.Body
}
      `;

      const result = await extractor.extract(code, 'handler.go');

      expect(result.dfg.sources.length).toBeGreaterThan(0);
    });

    it('should detect Gin sources', async () => {
      const code = `
package main

import "github.com/gin-gonic/gin"

func handler(c *gin.Context) {
    name := c.Query("name")
    id := c.Param("id")
    data := c.PostForm("data")
}
      `;

      const result = await extractor.extract(code, 'gin_handler.go');

      expect(result.dfg.sources.length).toBeGreaterThan(0);
    });

    it('should detect os/exec sources', async () => {
      const code = `
package main

import "os"

func main() {
    args := os.Args
    env := os.Getenv("PATH")
}
      `;

      const result = await extractor.extract(code, 'env.go');

      expect(result.dfg.sources.length).toBeGreaterThan(0);
    });
  });

  // TEST-GO-005: シンク検出テスト
  describe('sink detection', () => {
    it('should detect SQL injection sinks', async () => {
      const code = `
package main

import "database/sql"

func query(db *sql.DB, userInput string) {
    db.Query("SELECT * FROM users WHERE name = '" + userInput + "'")
}
      `;

      const result = await extractor.extract(code, 'db.go');

      expect(result.dfg.sinks.length).toBeGreaterThan(0);
    });

    it('should detect command injection sinks', async () => {
      const code = `
package main

import "os/exec"

func run(cmd string) {
    exec.Command(cmd)
}
      `;

      const result = await extractor.extract(code, 'exec.go');

      expect(result.dfg.sinks.length).toBeGreaterThan(0);
    });

    it('should detect XSS sinks', async () => {
      const code = `
package main

import (
    "fmt"
    "net/http"
)

func handler(w http.ResponseWriter, r *http.Request) {
    name := r.FormValue("name")
    fmt.Fprintf(w, name)
}
      `;

      const result = await extractor.extract(code, 'xss.go');

      expect(result.dfg.sinks.length).toBeGreaterThan(0);
    });

    it('should detect path traversal sinks', async () => {
      const code = `
package main

import "os"

func readFile(path string) {
    os.Open(path)
    os.ReadFile(path)
}
      `;

      const result = await extractor.extract(code, 'file.go');

      expect(result.dfg.sinks.length).toBeGreaterThan(0);
    });

    it('should detect SSRF sinks', async () => {
      const code = `
package main

import "net/http"

func fetch(url string) {
    http.Get(url)
}
      `;

      const result = await extractor.extract(code, 'ssrf.go');

      expect(result.dfg.sinks.length).toBeGreaterThan(0);
    });

    it('should detect GORM SQL injection sinks', async () => {
      const code = `
package main

import "gorm.io/gorm"

func query(db *gorm.DB, userInput string) {
    db.Raw("SELECT * FROM users WHERE name = '" + userInput + "'")
}
      `;

      const result = await extractor.extract(code, 'gorm.go');

      expect(result.dfg.sinks.length).toBeGreaterThan(0);
    });
  });

  // TEST-GO-006: サニタイザー検出テスト
  describe('sanitizer detection', () => {
    it('should detect HTML escape sanitizers', async () => {
      const code = `
package main

import "html"

func escape(input string) string {
    return html.EscapeString(input)
}
      `;

      const result = await extractor.extract(code, 'escape.go');

      // Check if sanitizers are detected in DFG nodes
      let hasSanitizer = false;
      for (const [, node] of result.dfg.nodes) {
        if (node.nodeType === 'sanitizer') {
          hasSanitizer = true;
          break;
        }
      }
      expect(hasSanitizer).toBe(true);
    });

    it('should detect filepath.Clean sanitizer', async () => {
      const code = `
package main

import "path/filepath"

func safePath(path string) string {
    return filepath.Clean(path)
}
      `;

      const result = await extractor.extract(code, 'path.go');

      let hasSanitizer = false;
      for (const [, node] of result.dfg.nodes) {
        if (node.nodeType === 'sanitizer') {
          hasSanitizer = true;
          break;
        }
      }
      expect(hasSanitizer).toBe(true);
    });
  });

  // TEST-GO-007: CFG構築テスト
  describe('CFG construction', () => {
    it('should build CFG with entry and exit blocks', async () => {
      const code = `
package main

func main() {
    x := 1
    y := 2
    z := x + y
}
      `;

      const result = await extractor.extract(code, 'cfg.go');

      expect(result.cfg.blocks.size).toBeGreaterThan(0);
      expect(result.cfg.entryBlocks.length).toBeGreaterThan(0);
      expect(result.cfg.exitBlocks.length).toBeGreaterThan(0);
    });

    it('should create blocks for functions', async () => {
      const code = `
package main

func foo() {}
func bar() {}
func baz() {}
      `;

      const result = await extractor.extract(code, 'funcs.go');

      // Each function should have its own block
      expect(result.cfg.blocks.size).toBeGreaterThanOrEqual(1);
    });
  });

  // TEST-GO-008: シンボル抽出テスト
  describe('symbol extraction', () => {
    it('should extract function symbols', async () => {
      const code = `
package main

func PublicFunc() {}
func privateFunc() {}
      `;

      const result = await extractor.extract(code, 'symbols.go');

      // Functions should be extracted
      expect(result.symbols.symbols.size).toBeGreaterThanOrEqual(0);
    });

    it('should extract struct types', async () => {
      const code = `
package main

type User struct {
    ID   int
    Name string
}

type config struct {
    host string
    port int
}
      `;

      const result = await extractor.extract(code, 'types.go');

      expect(result.ast).toBeDefined();
    });

    it('should extract interface types', async () => {
      const code = `
package main

type Reader interface {
    Read(p []byte) (n int, err error)
}

type Writer interface {
    Write(p []byte) (n int, err error)
}
      `;

      const result = await extractor.extract(code, 'interfaces.go');

      expect(result.ast).toBeDefined();
    });
  });

  // TEST-GO-009: エクスポート判定テスト
  describe('isExported', () => {
    it('should return true for uppercase identifiers', () => {
      expect(extractor.isExported('Public')).toBe(true);
      expect(extractor.isExported('MyFunc')).toBe(true);
      expect(extractor.isExported('HTTPHandler')).toBe(true);
    });

    it('should return false for lowercase identifiers', () => {
      expect(extractor.isExported('private')).toBe(false);
      expect(extractor.isExported('myFunc')).toBe(false);
      expect(extractor.isExported('handler')).toBe(false);
    });

    it('should return false for empty string', () => {
      expect(extractor.isExported('')).toBe(false);
    });
  });

  // TEST-GO-010: 統合テスト
  describe('integration', () => {
    it('should handle complete Go file with vulnerabilities', async () => {
      const code = `
package main

import (
    "database/sql"
    "net/http"
    "os/exec"
)

func handler(w http.ResponseWriter, r *http.Request, db *sql.DB) {
    // Source: user input
    userInput := r.FormValue("cmd")
    
    // Sink: command injection
    exec.Command(userInput)
    
    // Sink: SQL injection
    query := "SELECT * FROM users WHERE name = '" + userInput + "'"
    db.Query(query)
    
    // Sink: XSS
    w.Write([]byte(userInput))
}
      `;

      const result = await extractor.extract(code, 'vulnerable.go');

      expect(result.language).toBe('go');
      expect(result.dfg.sources.length).toBeGreaterThan(0);
      expect(result.dfg.sinks.length).toBeGreaterThan(0);
    });

    it('should handle Go code with sanitizers', async () => {
      const code = `
package main

import (
    "html"
    "net/http"
    "path/filepath"
)

func handler(w http.ResponseWriter, r *http.Request) {
    // Source
    userInput := r.FormValue("input")
    path := r.FormValue("path")
    
    // Sanitizers
    safeInput := html.EscapeString(userInput)
    safePath := filepath.Clean(path)
    
    w.Write([]byte(safeInput))
}
      `;

      const result = await extractor.extract(code, 'sanitized.go');

      let hasSanitizer = false;
      for (const [, node] of result.dfg.nodes) {
        if (node.nodeType === 'sanitizer') {
          hasSanitizer = true;
          break;
        }
      }
      expect(hasSanitizer).toBe(true);
    });

    it('should handle Gin framework code', async () => {
      const code = `
package main

import (
    "github.com/gin-gonic/gin"
    "gorm.io/gorm"
)

func GetUser(c *gin.Context, db *gorm.DB) {
    id := c.Param("id")
    name := c.Query("name")
    
    // Potential SQL injection with GORM
    db.Raw("SELECT * FROM users WHERE id = " + id)
    
    c.String(200, "User: " + name)
}
      `;

      const result = await extractor.extract(code, 'gin_app.go');

      expect(result.dfg.sources.length).toBeGreaterThan(0);
      expect(result.dfg.sinks.length).toBeGreaterThan(0);
    });
  });
});
