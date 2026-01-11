/**
 * @fileoverview Tests for Python vulnerability scanner
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  PythonScanner,
  createPythonScanner,
  resetPythonVulnCounter,
} from '../src/analysis/python-scanner.js';

describe('PythonScanner', () => {
  let scanner: PythonScanner;

  beforeEach(() => {
    scanner = createPythonScanner();
    resetPythonVulnCounter();
  });

  describe('SQL Injection (CWE-89)', () => {
    it('should detect f-string SQL injection', () => {
      const code = `
cursor.execute(f"SELECT * FROM users WHERE id = {user_id}")
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-89'))).toBe(true);
    });

    it('should detect format() SQL injection', () => {
      const code = `
cursor.execute("SELECT * FROM users WHERE id = {}".format(user_id))
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-89'))).toBe(true);
    });
  });

  describe('Command Injection (CWE-78)', () => {
    it('should detect os.system with f-string', () => {
      const code = `
os.system(f"ping {host}")
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-78'))).toBe(true);
    });

    it('should detect subprocess with shell=True', () => {
      const code = `
subprocess.run(cmd, shell=True)
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-78'))).toBe(true);
    });

    it('should detect os.popen', () => {
      const code = `
result = os.popen(command)
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-78'))).toBe(true);
    });
  });

  describe('Code Injection (CWE-94)', () => {
    it('should detect eval()', () => {
      const code = `
result = eval(user_input)
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-94'))).toBe(true);
    });

    it('should detect exec()', () => {
      const code = `
exec(code_string)
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-94'))).toBe(true);
    });
  });

  describe('Path Traversal (CWE-22)', () => {
    it('should detect open() with f-string', () => {
      const code = `
with open(f"/uploads/{filename}") as f:
    data = f.read()
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-22'))).toBe(true);
    });
  });

  describe('Insecure Deserialization (CWE-502)', () => {
    it('should detect pickle.load()', () => {
      const code = `
data = pickle.load(untrusted_file)
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-502'))).toBe(true);
    });

    it('should detect pickle.loads()', () => {
      const code = `
data = pickle.loads(untrusted_data)
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-502'))).toBe(true);
    });

    it('should detect yaml.load() without safe_load', () => {
      const code = `
data = yaml.load(user_data)
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-502'))).toBe(true);
    });
  });

  describe('XXE (CWE-611)', () => {
    it('should detect ElementTree.parse', () => {
      const code = `
tree = xml.etree.ElementTree.parse(xml_file)
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-611'))).toBe(true);
    });

    it('should detect lxml.etree.parse', () => {
      const code = `
doc = lxml.etree.parse(xml_input)
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-611'))).toBe(true);
    });
  });

  describe('SSRF (CWE-918)', () => {
    it('should detect requests.get with f-string URL', () => {
      const code = `
response = requests.get(f"http://api.example.com/{user_endpoint}")
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-918'))).toBe(true);
    });

    it('should detect urllib with dynamic URL', () => {
      const code = `
data = urllib.request.urlopen(f"http://{host}/data")
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-918'))).toBe(true);
    });
  });

  describe('LDAP Injection (CWE-90)', () => {
    it('should detect ldap.search with dynamic filter', () => {
      const code = `
results = ldap.search_s(base_dn, ldap.SCOPE_SUBTREE, f"(uid={username})")
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-90'))).toBe(true);
    });
  });

  describe('Hardcoded Secrets (CWE-798)', () => {
    it('should detect hardcoded password', () => {
      const code = `
password = "superSecretPassword123"
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-798'))).toBe(true);
    });

    it('should detect hardcoded API key', () => {
      const code = `
api_key = "sk_live_abcdef123456789"
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-798'))).toBe(true);
    });
  });

  describe('Weak Cryptography (CWE-327)', () => {
    it('should detect MD5 usage', () => {
      const code = `
hash = hashlib.md5(data)
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-327'))).toBe(true);
    });

    it('should detect SHA1 usage', () => {
      const code = `
hash = hashlib.sha1(data)
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-327'))).toBe(true);
    });
  });

  describe('Debug Mode (CWE-489)', () => {
    it('should detect Flask debug=True', () => {
      const code = `
app.run(debug=True)
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-489'))).toBe(true);
    });
  });

  describe('ReDoS (CWE-1333)', () => {
    it('should detect vulnerable regex pattern', () => {
      const code = `
re.match(r"(a+)+b", user_input)
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-1333'))).toBe(true);
    });
  });

  describe('Template Injection (CWE-1336)', () => {
    it('should detect render_template_string with f-string', () => {
      const code = `
return render_template_string(f"<h1>{user_name}</h1>")
      `;
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.cwes.includes('CWE-1336') || v.cwes.includes('CWE-94'))).toBe(true);
    });
  });

  describe('getRuleCount', () => {
    it('should return correct rule count', () => {
      expect(scanner.getRuleCount()).toBeGreaterThanOrEqual(14);
    });
  });

  describe('custom patterns', () => {
    it('should allow adding custom pattern', () => {
      scanner.addPattern({
        ruleId: 'PY-CUSTOM-001',
        pattern: /dangerous_function\s*\(/gi,
        type: 'misconfig',
        severity: 'high',
        cwes: ['CWE-999'],
        owasp: ['A99:2021'],
        description: 'Custom dangerous function',
        recommendation: 'Avoid using dangerous_function',
        confidence: 0.9,
      });

      const code = 'dangerous_function(data)';
      const vulns = scanner.scanContent(code, 'test.py');
      expect(vulns.some(v => v.ruleId === 'PY-CUSTOM-001')).toBe(true);
    });
  });
});
