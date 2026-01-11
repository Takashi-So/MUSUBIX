/**
 * @fileoverview Tests for PHP vulnerability scanner
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  PhpScanner,
  createPhpScanner,
  resetPhpVulnCounter,
} from '../src/analysis/php-scanner.js';

describe('PhpScanner', () => {
  let scanner: PhpScanner;

  beforeEach(() => {
    scanner = createPhpScanner();
    resetPhpVulnCounter();
  });

  describe('SQL Injection (CWE-89)', () => {
    it('should detect mysql_query with $_GET', () => {
      const code = `
<?php
mysql_query("SELECT * FROM users WHERE id = " . $_GET['id']);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-89'))).toBe(true);
    });

    it('should detect mysqli_query with user input', () => {
      const code = `
<?php
mysqli_query($conn, "SELECT * FROM users WHERE id = " . $_POST['id']);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-89'))).toBe(true);
    });

    it('should detect PDO query with concatenation', () => {
      const code = `
<?php
$pdo->query("SELECT * FROM users WHERE name = '" . $name . "'");
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-89'))).toBe(true);
    });
  });

  describe('XSS (CWE-79)', () => {
    it('should detect echo with $_GET', () => {
      const code = `
<?php
echo $_GET['message'];
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-79'))).toBe(true);
    });

    it('should detect print with $_POST', () => {
      const code = `
<?php
print $_POST['name'];
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-79'))).toBe(true);
    });

    it('should detect short echo tag with user input', () => {
      const code = `
<h1><?= $_REQUEST['title'] ?></h1>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-79'))).toBe(true);
    });
  });

  describe('Command Injection (CWE-78)', () => {
    it('should detect exec with user input', () => {
      const code = `
<?php
exec("ping " . $_GET['host']);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-78'))).toBe(true);
    });

    it('should detect system with user input', () => {
      const code = `
<?php
system("ls " . $_POST['dir']);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-78'))).toBe(true);
    });

    it('should detect backtick operator', () => {
      const code = '<?php $output = `cat $_GET["file"]`; ?>';
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-78'))).toBe(true);
    });
  });

  describe('Code Injection (CWE-94)', () => {
    it('should detect eval with user input', () => {
      const code = `
<?php
eval($_POST['code']);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-94'))).toBe(true);
    });

    it('should detect eval usage', () => {
      const code = `
<?php
eval($dynamic_code);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-94'))).toBe(true);
    });

    it('should detect create_function', () => {
      const code = `
<?php
$func = create_function('$a', 'return $a;');
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-94'))).toBe(true);
    });

    it('should detect preg_replace with /e modifier', () => {
      const code = `
<?php
preg_replace("/test/e", $replacement, $subject);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-94'))).toBe(true);
    });
  });

  describe('File Inclusion (CWE-98)', () => {
    it('should detect include with user input', () => {
      const code = `
<?php
include($_GET['page']);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-98'))).toBe(true);
    });

    it('should detect require_once with user input', () => {
      const code = `
<?php
require_once($_POST['module']);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-98'))).toBe(true);
    });
  });

  describe('Path Traversal (CWE-22)', () => {
    it('should detect file_get_contents with user input', () => {
      const code = `
<?php
$content = file_get_contents($_GET['file']);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-22'))).toBe(true);
    });

    it('should detect unlink with user input', () => {
      const code = `
<?php
unlink("/uploads/" . $_POST['filename']);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-22'))).toBe(true);
    });
  });

  describe('Insecure Deserialization (CWE-502)', () => {
    it('should detect unserialize with user input', () => {
      const code = `
<?php
$data = unserialize($_COOKIE['session']);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-502'))).toBe(true);
    });

    it('should detect unserialize usage', () => {
      const code = `
<?php
$obj = unserialize($serialized_data);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-502'))).toBe(true);
    });
  });

  describe('SSRF (CWE-918)', () => {
    it('should detect file_get_contents with user URL', () => {
      const code = `
<?php
$data = file_get_contents("http://api.example.com/" . $_GET['endpoint']);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-918'))).toBe(true);
    });

    it('should detect curl with user URL', () => {
      const code = `
<?php
curl_setopt($ch, CURLOPT_URL, $_POST['url']);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-918'))).toBe(true);
    });
  });

  describe('XXE (CWE-611)', () => {
    it('should detect simplexml_load_string with user input', () => {
      const code = `
<?php
$xml = simplexml_load_string($_POST['xml']);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-611'))).toBe(true);
    });
  });

  describe('LDAP Injection (CWE-90)', () => {
    it('should detect ldap_search with user input', () => {
      const code = `
<?php
ldap_search($ds, $dn, "(uid=" . $_GET['username'] . ")");
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-90'))).toBe(true);
    });
  });

  describe('Hardcoded Secrets (CWE-798)', () => {
    it('should detect hardcoded password', () => {
      const code = `
<?php
$password = "superSecretPassword123";
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-798'))).toBe(true);
    });
  });

  describe('Weak Cryptography (CWE-327)', () => {
    it('should detect MD5 for password', () => {
      const code = `
<?php
$hash = md5($password);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-327'))).toBe(true);
    });

    it('should detect SHA1 for password', () => {
      const code = `
<?php
$hash = sha1($pass);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-327'))).toBe(true);
    });
  });

  describe('Session Fixation (CWE-384)', () => {
    it('should detect session_id with user input', () => {
      const code = `
<?php
session_id($_GET['sid']);
session_start();
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-384'))).toBe(true);
    });
  });

  describe('Open Redirect (CWE-601)', () => {
    it('should detect header redirect with user input', () => {
      const code = `
<?php
header("Location: " . $_GET['redirect']);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-601'))).toBe(true);
    });
  });

  describe('Information Disclosure (CWE-209)', () => {
    it('should detect var_dump', () => {
      const code = `
<?php
var_dump($user);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-209'))).toBe(true);
    });

    it('should detect print_r', () => {
      const code = `
<?php
print_r($_SESSION);
?>
      `;
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.cwes.includes('CWE-209'))).toBe(true);
    });
  });

  describe('getRuleCount', () => {
    it('should return correct rule count', () => {
      expect(scanner.getRuleCount()).toBeGreaterThanOrEqual(16);
    });
  });

  describe('custom patterns', () => {
    it('should allow adding custom pattern', () => {
      scanner.addPattern({
        ruleId: 'PHP-CUSTOM-001',
        pattern: /legacy_dangerous_function\s*\(/gi,
        type: 'misconfig',
        severity: 'high',
        cwes: ['CWE-999'],
        owasp: ['A99:2021'],
        description: 'Custom dangerous function',
        recommendation: 'Avoid using legacy_dangerous_function',
        confidence: 0.9,
      });

      const code = '<?php legacy_dangerous_function($data); ?>';
      const vulns = scanner.scanContent(code, 'test.php');
      expect(vulns.some(v => v.ruleId === 'PHP-CUSTOM-001')).toBe(true);
    });
  });
});
