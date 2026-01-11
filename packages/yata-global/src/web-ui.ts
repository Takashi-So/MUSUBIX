/**
 * YATA Global Web UI
 *
 * HTML templates for KGPR management interface
 *
 * @packageDocumentation
 */

const STYLES = `
* {
  box-sizing: border-box;
  margin: 0;
  padding: 0;
}

body {
  font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Oxygen, Ubuntu, sans-serif;
  background: #f5f7fa;
  color: #333;
  line-height: 1.6;
}

.navbar {
  background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
  color: white;
  padding: 1rem 2rem;
  display: flex;
  justify-content: space-between;
  align-items: center;
  box-shadow: 0 2px 10px rgba(0,0,0,0.1);
}

.nav-brand {
  font-size: 1.5rem;
  font-weight: bold;
}

.nav-brand span {
  color: #ffd700;
}

.nav-links {
  display: flex;
  gap: 2rem;
}

.nav-links a {
  color: white;
  text-decoration: none;
  padding: 0.5rem 1rem;
  border-radius: 4px;
  transition: background 0.3s;
}

.nav-links a:hover {
  background: rgba(255,255,255,0.2);
}

.container {
  max-width: 1200px;
  margin: 0 auto;
  padding: 2rem;
}

h1, h2, h3 {
  color: #333;
  margin-bottom: 1rem;
}

.card {
  background: white;
  border-radius: 8px;
  box-shadow: 0 2px 10px rgba(0,0,0,0.1);
  padding: 1.5rem;
  margin-bottom: 1rem;
}

.stats-grid {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
  gap: 1rem;
  margin-bottom: 2rem;
}

.stat-card {
  background: white;
  border-radius: 8px;
  padding: 1.5rem;
  text-align: center;
  box-shadow: 0 2px 10px rgba(0,0,0,0.1);
}

.stat-value {
  font-size: 2.5rem;
  font-weight: bold;
  background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
  -webkit-background-clip: text;
  -webkit-text-fill-color: transparent;
  background-clip: text;
}

.stat-label {
  color: #666;
  font-size: 0.9rem;
  margin-top: 0.5rem;
}

.btn {
  display: inline-block;
  padding: 0.75rem 1.5rem;
  border: none;
  border-radius: 4px;
  cursor: pointer;
  text-decoration: none;
  font-size: 1rem;
  transition: all 0.3s;
}

.btn-primary {
  background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
  color: white;
}

.btn-primary:hover {
  transform: translateY(-2px);
  box-shadow: 0 4px 15px rgba(102,126,234,0.4);
}

.btn-success {
  background: #28a745;
  color: white;
}

.btn-success:hover {
  background: #218838;
}

.btn-danger {
  background: #dc3545;
  color: white;
}

.btn-danger:hover {
  background: #c82333;
}

.btn-secondary {
  background: #6c757d;
  color: white;
}

.btn-secondary:hover {
  background: #5a6268;
}

.status-badge {
  display: inline-block;
  padding: 0.25rem 0.75rem;
  border-radius: 20px;
  font-size: 0.85rem;
  font-weight: 500;
}

.status-draft { background: #e9ecef; color: #495057; }
.status-submitted { background: #cce5ff; color: #004085; }
.status-in_review { background: #fff3cd; color: #856404; }
.status-approved { background: #d4edda; color: #155724; }
.status-merged { background: #d1ecf1; color: #0c5460; }
.status-rejected { background: #f8d7da; color: #721c24; }

.table {
  width: 100%;
  border-collapse: collapse;
  margin-top: 1rem;
}

.table th,
.table td {
  padding: 1rem;
  text-align: left;
  border-bottom: 1px solid #e9ecef;
}

.table th {
  background: #f8f9fa;
  font-weight: 600;
  color: #495057;
}

.table tr:hover {
  background: #f8f9fa;
}

.form-group {
  margin-bottom: 1.5rem;
}

.form-group label {
  display: block;
  margin-bottom: 0.5rem;
  font-weight: 500;
  color: #495057;
}

.form-group input,
.form-group textarea,
.form-group select {
  width: 100%;
  padding: 0.75rem;
  border: 1px solid #ced4da;
  border-radius: 4px;
  font-size: 1rem;
}

.form-group input:focus,
.form-group textarea:focus,
.form-group select:focus {
  outline: none;
  border-color: #667eea;
  box-shadow: 0 0 0 3px rgba(102,126,234,0.1);
}

.form-group textarea {
  min-height: 100px;
  resize: vertical;
}

.entity-list,
.relationship-list {
  margin-top: 1rem;
}

.entity-item,
.relationship-item {
  display: flex;
  gap: 0.5rem;
  margin-bottom: 0.5rem;
  padding: 0.75rem;
  background: #f8f9fa;
  border-radius: 4px;
}

.entity-item input,
.relationship-item input,
.relationship-item select {
  flex: 1;
  padding: 0.5rem;
  border: 1px solid #ced4da;
  border-radius: 4px;
}

.btn-remove {
  background: #dc3545;
  color: white;
  border: none;
  padding: 0.5rem 0.75rem;
  border-radius: 4px;
  cursor: pointer;
}

.btn-add {
  background: #28a745;
  color: white;
  border: none;
  padding: 0.5rem 1rem;
  border-radius: 4px;
  cursor: pointer;
  margin-top: 0.5rem;
}

.detail-header {
  display: flex;
  justify-content: space-between;
  align-items: flex-start;
  margin-bottom: 2rem;
}

.detail-title {
  font-size: 1.75rem;
  margin-bottom: 0.5rem;
}

.detail-meta {
  color: #666;
  font-size: 0.9rem;
}

.detail-actions {
  display: flex;
  gap: 0.5rem;
}

.section {
  margin-bottom: 2rem;
}

.section-title {
  font-size: 1.25rem;
  color: #495057;
  padding-bottom: 0.5rem;
  border-bottom: 2px solid #667eea;
  margin-bottom: 1rem;
}

.entity-grid,
.relationship-grid {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(250px, 1fr));
  gap: 1rem;
}

.entity-card,
.relationship-card {
  background: #f8f9fa;
  border-radius: 8px;
  padding: 1rem;
  border-left: 4px solid #667eea;
}

.entity-card h4,
.relationship-card h4 {
  margin-bottom: 0.5rem;
  color: #333;
}

.entity-card p,
.relationship-card p {
  font-size: 0.9rem;
  color: #666;
}

.review-section {
  margin-top: 2rem;
  padding: 1.5rem;
  background: #fff3cd;
  border-radius: 8px;
  border: 1px solid #ffc107;
}

.review-section h3 {
  color: #856404;
  margin-bottom: 1rem;
}

.filter-bar {
  display: flex;
  gap: 1rem;
  margin-bottom: 1.5rem;
  flex-wrap: wrap;
}

.filter-bar select,
.filter-bar input {
  padding: 0.5rem 1rem;
  border: 1px solid #ced4da;
  border-radius: 4px;
}

.empty-state {
  text-align: center;
  padding: 3rem;
  color: #666;
}

.empty-state svg {
  width: 64px;
  height: 64px;
  margin-bottom: 1rem;
  opacity: 0.5;
}

.toast {
  position: fixed;
  bottom: 2rem;
  right: 2rem;
  padding: 1rem 2rem;
  background: #333;
  color: white;
  border-radius: 8px;
  box-shadow: 0 4px 20px rgba(0,0,0,0.2);
  transform: translateY(100px);
  opacity: 0;
  transition: all 0.3s;
}

.toast.show {
  transform: translateY(0);
  opacity: 1;
}

.toast.success { background: #28a745; }
.toast.error { background: #dc3545; }

.projects-grid {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(300px, 1fr));
  gap: 1.5rem;
}

.project-card {
  background: white;
  border-radius: 8px;
  padding: 1.5rem;
  box-shadow: 0 2px 10px rgba(0,0,0,0.1);
  transition: transform 0.3s, box-shadow 0.3s;
  text-decoration: none;
  color: inherit;
  display: block;
}

.project-card:hover {
  transform: translateY(-4px);
  box-shadow: 0 8px 25px rgba(0,0,0,0.15);
}

.project-card h3 {
  color: #667eea;
  margin-bottom: 0.5rem;
}

.project-card p {
  color: #666;
  font-size: 0.9rem;
}

.project-stats {
  display: flex;
  gap: 1rem;
  margin-top: 1rem;
  padding-top: 1rem;
  border-top: 1px solid #e9ecef;
}

.project-stat {
  font-size: 0.85rem;
  color: #666;
}

.project-stat strong {
  color: #333;
}

.loading {
  display: flex;
  justify-content: center;
  align-items: center;
  padding: 2rem;
}

.spinner {
  width: 40px;
  height: 40px;
  border: 4px solid #f3f3f3;
  border-top: 4px solid #667eea;
  border-radius: 50%;
  animation: spin 1s linear infinite;
}

@keyframes spin {
  0% { transform: rotate(0deg); }
  100% { transform: rotate(360deg); }
}
`;

const NAV_HTML = `
<nav class="navbar">
  <div class="nav-brand">YATA <span>Global</span></div>
  <div class="nav-links">
    <a href="/">Dashboard</a>
    <a href="/ui/kgprs">KGPRs</a>
    <a href="/ui/projects">Projects</a>
  </div>
</nav>
`;

/**
 * Main dashboard HTML
 */
export function getDashboardHTML(): string {
  return `<!DOCTYPE html>
<html lang="ja">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>YATA Global - Dashboard</title>
  <style>${STYLES}</style>
</head>
<body>
  ${NAV_HTML}
  <div class="container">
    <h1>Dashboard</h1>
    
    <div class="stats-grid" id="stats">
      <div class="stat-card">
        <div class="stat-value" id="stat-total">-</div>
        <div class="stat-label">Total KGPRs</div>
      </div>
      <div class="stat-card">
        <div class="stat-value" id="stat-pending">-</div>
        <div class="stat-label">Pending Review</div>
      </div>
      <div class="stat-card">
        <div class="stat-value" id="stat-merged">-</div>
        <div class="stat-label">Merged</div>
      </div>
      <div class="stat-card">
        <div class="stat-value" id="stat-projects">-</div>
        <div class="stat-label">Projects</div>
      </div>
    </div>

    <div class="card">
      <h2>Quick Actions</h2>
      <div style="display: flex; gap: 1rem; margin-top: 1rem;">
        <a href="/ui/kgprs/new" class="btn btn-primary">Create New KGPR</a>
        <a href="/ui/kgprs" class="btn btn-secondary">View All KGPRs</a>
        <a href="/ui/projects" class="btn btn-secondary">Browse Projects</a>
      </div>
    </div>

    <div class="card">
      <h2>Recent KGPRs</h2>
      <div id="recent-kgprs">
        <div class="loading"><div class="spinner"></div></div>
      </div>
    </div>
  </div>

  <div class="toast" id="toast"></div>

  <script>
    async function loadDashboard() {
      try {
        // Load KGPRs
        const kgprsRes = await fetch('/api/v1/kgprs');
        const kgprsData = await kgprsRes.json();
        const kgprs = kgprsData.kgprs || [];
        
        // Update stats
        document.getElementById('stat-total').textContent = kgprs.length;
        document.getElementById('stat-pending').textContent = 
          kgprs.filter(k => k.status === 'submitted' || k.status === 'in_review').length;
        document.getElementById('stat-merged').textContent = 
          kgprs.filter(k => k.status === 'merged').length;
        
        // Load projects count
        const projectsRes = await fetch('/api/v1/projects');
        const projectsData = await projectsRes.json();
        document.getElementById('stat-projects').textContent = (projectsData.projects || []).length;
        
        // Render recent KGPRs
        const recentKgprs = kgprs.slice(0, 5);
        const recentHtml = recentKgprs.length === 0 
          ? '<div class="empty-state"><p>No KGPRs yet. Create your first one!</p></div>'
          : '<table class="table"><thead><tr><th>ID</th><th>Title</th><th>Status</th><th>Updated</th></tr></thead><tbody>' +
            recentKgprs.map(k => 
              '<tr onclick="location.href=\\'/ui/kgprs/' + k.id + '\\'\" style="cursor:pointer">' +
              '<td>' + k.id.slice(0,8) + '...</td>' +
              '<td>' + (k.title || 'Untitled') + '</td>' +
              '<td><span class="status-badge status-' + k.status + '">' + k.status + '</span></td>' +
              '<td>' + new Date(k.updatedAt).toLocaleDateString('ja-JP') + '</td>' +
              '</tr>'
            ).join('') +
            '</tbody></table>';
        document.getElementById('recent-kgprs').innerHTML = recentHtml;
      } catch (err) {
        console.error('Failed to load dashboard:', err);
        document.getElementById('recent-kgprs').innerHTML = 
          '<div class="empty-state"><p>Failed to load data</p></div>';
      }
    }
    
    loadDashboard();
  </script>
</body>
</html>`;
}

/**
 * KGPR list page HTML
 */
export function getKGPRListHTML(): string {
  return `<!DOCTYPE html>
<html lang="ja">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>YATA Global - KGPRs</title>
  <style>${STYLES}</style>
</head>
<body>
  ${NAV_HTML}
  <div class="container">
    <div style="display: flex; justify-content: space-between; align-items: center; margin-bottom: 1.5rem;">
      <h1>Knowledge Graph Pull Requests</h1>
      <a href="/ui/kgprs/new" class="btn btn-primary">+ New KGPR</a>
    </div>
    
    <div class="filter-bar">
      <select id="status-filter" onchange="filterKGPRs()">
        <option value="">All Status</option>
        <option value="draft">Draft</option>
        <option value="submitted">Submitted</option>
        <option value="in_review">In Review</option>
        <option value="approved">Approved</option>
        <option value="merged">Merged</option>
        <option value="rejected">Rejected</option>
      </select>
      <input type="text" id="search" placeholder="Search..." oninput="filterKGPRs()">
    </div>

    <div class="card">
      <div id="kgpr-list">
        <div class="loading"><div class="spinner"></div></div>
      </div>
    </div>
  </div>

  <div class="toast" id="toast"></div>

  <script>
    let allKgprs = [];
    
    async function loadKGPRs() {
      try {
        const res = await fetch('/api/v1/kgprs');
        const data = await res.json();
        allKgprs = data.kgprs || [];
        renderKGPRs(allKgprs);
      } catch (err) {
        console.error('Failed to load KGPRs:', err);
        document.getElementById('kgpr-list').innerHTML = 
          '<div class="empty-state"><p>Failed to load KGPRs</p></div>';
      }
    }
    
    function filterKGPRs() {
      const status = document.getElementById('status-filter').value;
      const search = document.getElementById('search').value.toLowerCase();
      
      let filtered = allKgprs;
      if (status) {
        filtered = filtered.filter(k => k.status === status);
      }
      if (search) {
        filtered = filtered.filter(k => 
          (k.title || '').toLowerCase().includes(search) ||
          (k.description || '').toLowerCase().includes(search) ||
          k.id.toLowerCase().includes(search)
        );
      }
      renderKGPRs(filtered);
    }
    
    function renderKGPRs(kgprs) {
      if (kgprs.length === 0) {
        document.getElementById('kgpr-list').innerHTML = 
          '<div class="empty-state"><p>No KGPRs found</p></div>';
        return;
      }
      
      const html = '<table class="table"><thead><tr>' +
        '<th>ID</th><th>Title</th><th>Project</th><th>Status</th>' +
        '<th>Entities</th><th>Relations</th><th>Updated</th></tr></thead><tbody>' +
        kgprs.map(k => 
          '<tr onclick="location.href=\\'/ui/kgprs/' + k.id + '\\'\" style="cursor:pointer">' +
          '<td>' + k.id.slice(0,8) + '...</td>' +
          '<td><strong>' + (k.title || 'Untitled') + '</strong></td>' +
          '<td>' + (k.projectId || '-') + '</td>' +
          '<td><span class="status-badge status-' + k.status + '">' + k.status + '</span></td>' +
          '<td>' + ((k.content && k.content.entities) ? k.content.entities.length : 0) + '</td>' +
          '<td>' + ((k.content && k.content.relationships) ? k.content.relationships.length : 0) + '</td>' +
          '<td>' + new Date(k.updatedAt).toLocaleDateString('ja-JP') + '</td>' +
          '</tr>'
        ).join('') +
        '</tbody></table>';
      document.getElementById('kgpr-list').innerHTML = html;
    }
    
    loadKGPRs();
  </script>
</body>
</html>`;
}

/**
 * KGPR detail page HTML
 */
export function getKGPRDetailHTML(id: string): string {
  return `<!DOCTYPE html>
<html lang="ja">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>YATA Global - KGPR Detail</title>
  <style>${STYLES}</style>
</head>
<body>
  ${NAV_HTML}
  <div class="container">
    <div id="kgpr-detail">
      <div class="loading"><div class="spinner"></div></div>
    </div>
  </div>

  <div class="toast" id="toast"></div>

  <script>
    const kgprId = '${id}';
    let currentKgpr = null;
    
    async function loadKGPR() {
      try {
        const res = await fetch('/api/v1/kgprs/' + kgprId);
        if (!res.ok) throw new Error('KGPR not found');
        currentKgpr = await res.json();
        renderKGPR(currentKgpr);
      } catch (err) {
        console.error('Failed to load KGPR:', err);
        document.getElementById('kgpr-detail').innerHTML = 
          '<div class="empty-state"><p>KGPR not found</p><a href="/ui/kgprs" class="btn btn-primary">Back to List</a></div>';
      }
    }
    
    function renderKGPR(k) {
      const entities = (k.content && k.content.entities) || [];
      const relationships = (k.content && k.content.relationships) || [];
      
      const html = '<div class="detail-header">' +
        '<div>' +
          '<h1 class="detail-title">' + (k.title || 'Untitled KGPR') + '</h1>' +
          '<div class="detail-meta">' +
            '<span class="status-badge status-' + k.status + '">' + k.status + '</span> | ' +
            'ID: ' + k.id + ' | ' +
            'Project: ' + (k.projectId || '-') + ' | ' +
            'Updated: ' + new Date(k.updatedAt).toLocaleString('ja-JP') +
          '</div>' +
        '</div>' +
        '<div class="detail-actions">' +
          getActionButtons(k.status) +
        '</div>' +
      '</div>' +
      
      '<div class="card">' +
        '<h3>Description</h3>' +
        '<p>' + (k.description || 'No description') + '</p>' +
      '</div>' +
      
      '<div class="section">' +
        '<h2 class="section-title">Entities (' + entities.length + ')</h2>' +
        (entities.length === 0 
          ? '<div class="empty-state"><p>No entities</p></div>'
          : '<div class="entity-grid">' + entities.map(e => 
              '<div class="entity-card">' +
                '<h4>' + (e.name || e.id) + '</h4>' +
                '<p>Type: ' + (e.type || '-') + '</p>' +
                (e.properties ? '<p>Props: ' + Object.keys(e.properties).length + '</p>' : '') +
              '</div>'
            ).join('') + '</div>'
        ) +
      '</div>' +
      
      '<div class="section">' +
        '<h2 class="section-title">Relationships (' + relationships.length + ')</h2>' +
        (relationships.length === 0 
          ? '<div class="empty-state"><p>No relationships</p></div>'
          : '<div class="relationship-grid">' + relationships.map(r => 
              '<div class="relationship-card">' +
                '<h4>' + (r.type || 'unknown') + '</h4>' +
                '<p>' + (r.source || r.sourceId) + ' → ' + (r.target || r.targetId) + '</p>' +
              '</div>'
            ).join('') + '</div>'
        ) +
      '</div>' +
      
      (k.status === 'submitted' || k.status === 'in_review' 
        ? '<div class="review-section">' +
            '<h3>Review Actions</h3>' +
            '<div style="display: flex; gap: 1rem; margin-top: 1rem;">' +
              '<button onclick="reviewKGPR(\\'approved\\')" class="btn btn-success">Approve</button>' +
              '<button onclick="reviewKGPR(\\'changes_requested\\')" class="btn btn-secondary">Request Changes</button>' +
              '<button onclick="reviewKGPR(\\'rejected\\')" class="btn btn-danger">Reject</button>' +
            '</div>' +
          '</div>'
        : ''
      ) +
      
      '<div style="margin-top: 2rem;">' +
        '<a href="/ui/kgprs" class="btn btn-secondary">← Back to List</a>' +
      '</div>';
      
      document.getElementById('kgpr-detail').innerHTML = html;
    }
    
    function getActionButtons(status) {
      let buttons = '';
      if (status === 'draft') {
        buttons = '<button onclick="submitKGPR()" class="btn btn-primary">Submit for Review</button>';
      } else if (status === 'approved') {
        buttons = '<button onclick="mergeKGPR()" class="btn btn-success">Merge</button>';
      }
      return buttons;
    }
    
    async function submitKGPR() {
      try {
        const res = await fetch('/api/v1/kgprs/' + kgprId + '/submit', { method: 'POST' });
        if (!res.ok) throw new Error('Submit failed');
        showToast('KGPR submitted for review', 'success');
        loadKGPR();
      } catch (err) {
        showToast('Failed to submit KGPR', 'error');
      }
    }
    
    async function reviewKGPR(decision) {
      try {
        const res = await fetch('/api/v1/kgprs/' + kgprId + '/review', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ decision: decision, comment: '' })
        });
        if (!res.ok) throw new Error('Review failed');
        showToast('Review submitted: ' + decision, 'success');
        loadKGPR();
      } catch (err) {
        showToast('Failed to submit review', 'error');
      }
    }
    
    async function mergeKGPR() {
      try {
        const res = await fetch('/api/v1/kgprs/' + kgprId + '/merge', { method: 'POST' });
        if (!res.ok) throw new Error('Merge failed');
        showToast('KGPR merged successfully!', 'success');
        loadKGPR();
      } catch (err) {
        showToast('Failed to merge KGPR', 'error');
      }
    }
    
    function showToast(message, type) {
      const toast = document.getElementById('toast');
      toast.textContent = message;
      toast.className = 'toast show ' + type;
      setTimeout(() => toast.className = 'toast', 3000);
    }
    
    loadKGPR();
  </script>
</body>
</html>`;
}

/**
 * KGPR create page HTML
 */
export function getKGPRCreateHTML(): string {
  return `<!DOCTYPE html>
<html lang="ja">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>YATA Global - Create KGPR</title>
  <style>${STYLES}</style>
</head>
<body>
  ${NAV_HTML}
  <div class="container">
    <h1>Create New KGPR</h1>
    
    <form id="kgpr-form" class="card">
      <div class="form-group">
        <label for="title">Title *</label>
        <input type="text" id="title" name="title" required placeholder="Enter KGPR title">
      </div>
      
      <div class="form-group">
        <label for="description">Description</label>
        <textarea id="description" name="description" placeholder="Describe the changes in this KGPR"></textarea>
      </div>
      
      <div class="form-group">
        <label for="projectId">Project ID</label>
        <input type="text" id="projectId" name="projectId" placeholder="e.g., sample-project">
      </div>
      
      <div class="form-group">
        <label for="namespace">Namespace</label>
        <input type="text" id="namespace" name="namespace" placeholder="e.g., default" value="default">
      </div>
      
      <div class="section">
        <h3 class="section-title">Entities</h3>
        <div id="entities-list" class="entity-list"></div>
        <button type="button" class="btn-add" onclick="addEntity()">+ Add Entity</button>
      </div>
      
      <div class="section">
        <h3 class="section-title">Relationships</h3>
        <div id="relationships-list" class="relationship-list"></div>
        <button type="button" class="btn-add" onclick="addRelationship()">+ Add Relationship</button>
      </div>
      
      <div style="display: flex; gap: 1rem; margin-top: 2rem;">
        <button type="submit" class="btn btn-primary">Create KGPR</button>
        <a href="/ui/kgprs" class="btn btn-secondary">Cancel</a>
      </div>
    </form>
  </div>

  <div class="toast" id="toast"></div>

  <script>
    let entityCount = 0;
    let relationshipCount = 0;
    
    function addEntity() {
      const container = document.getElementById('entities-list');
      const div = document.createElement('div');
      div.className = 'entity-item';
      div.id = 'entity-' + entityCount;
      div.innerHTML = 
        '<input type="text" placeholder="Entity ID" name="entity-id-' + entityCount + '">' +
        '<input type="text" placeholder="Name" name="entity-name-' + entityCount + '">' +
        '<input type="text" placeholder="Type" name="entity-type-' + entityCount + '">' +
        '<button type="button" class="btn-remove" onclick="removeEntity(' + entityCount + ')">×</button>';
      container.appendChild(div);
      entityCount++;
    }
    
    function removeEntity(id) {
      const el = document.getElementById('entity-' + id);
      if (el) el.remove();
    }
    
    function addRelationship() {
      const container = document.getElementById('relationships-list');
      const div = document.createElement('div');
      div.className = 'relationship-item';
      div.id = 'rel-' + relationshipCount;
      div.innerHTML = 
        '<input type="text" placeholder="Source ID" name="rel-source-' + relationshipCount + '">' +
        '<input type="text" placeholder="Type (e.g., depends-on)" name="rel-type-' + relationshipCount + '">' +
        '<input type="text" placeholder="Target ID" name="rel-target-' + relationshipCount + '">' +
        '<button type="button" class="btn-remove" onclick="removeRelationship(' + relationshipCount + ')">×</button>';
      container.appendChild(div);
      relationshipCount++;
    }
    
    function removeRelationship(id) {
      const el = document.getElementById('rel-' + id);
      if (el) el.remove();
    }
    
    document.getElementById('kgpr-form').onsubmit = async function(e) {
      e.preventDefault();
      
      const formData = new FormData(this);
      
      // Collect entities
      const entities = [];
      for (let i = 0; i < entityCount; i++) {
        const id = formData.get('entity-id-' + i);
        if (id) {
          entities.push({
            id: id,
            name: formData.get('entity-name-' + i) || id,
            type: formData.get('entity-type-' + i) || 'unknown'
          });
        }
      }
      
      // Collect relationships
      const relationships = [];
      for (let i = 0; i < relationshipCount; i++) {
        const source = formData.get('rel-source-' + i);
        const target = formData.get('rel-target-' + i);
        if (source && target) {
          relationships.push({
            sourceId: source,
            type: formData.get('rel-type-' + i) || 'related-to',
            targetId: target
          });
        }
      }
      
      const kgprData = {
        title: formData.get('title'),
        description: formData.get('description') || '',
        projectId: formData.get('projectId') || undefined,
        namespace: formData.get('namespace') || 'default',
        content: {
          entities: entities,
          relationships: relationships
        }
      };
      
      try {
        const res = await fetch('/api/v1/kgprs', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify(kgprData)
        });
        
        if (!res.ok) {
          const err = await res.json();
          throw new Error(err.error || 'Create failed');
        }
        
        const result = await res.json();
        showToast('KGPR created successfully!', 'success');
        setTimeout(() => location.href = '/ui/kgprs/' + result.id, 1000);
      } catch (err) {
        showToast('Failed: ' + err.message, 'error');
      }
    };
    
    function showToast(message, type) {
      const toast = document.getElementById('toast');
      toast.textContent = message;
      toast.className = 'toast show ' + type;
      setTimeout(() => toast.className = 'toast', 3000);
    }
    
    // Add one entity and relationship by default
    addEntity();
    addRelationship();
  </script>
</body>
</html>`;
}

/**
 * Projects list page HTML
 */
export function getProjectsListHTML(): string {
  return `<!DOCTYPE html>
<html lang="ja">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>YATA Global - Projects</title>
  <style>${STYLES}</style>
</head>
<body>
  ${NAV_HTML}
  <div class="container">
    <h1>Projects</h1>
    
    <div id="projects-list">
      <div class="loading"><div class="spinner"></div></div>
    </div>
  </div>

  <script>
    async function loadProjects() {
      try {
        const res = await fetch('/api/v1/projects');
        const data = await res.json();
        const projects = data.projects || [];
        
        if (projects.length === 0) {
          document.getElementById('projects-list').innerHTML = 
            '<div class="empty-state"><p>No projects found</p></div>';
          return;
        }
        
        const html = '<div class="projects-grid">' +
          projects.map(p => 
            '<a href="/ui/projects/' + p.id + '" class="project-card">' +
              '<h3>' + p.name + '</h3>' +
              '<p>' + (p.description || 'No description') + '</p>' +
              '<div class="project-stats">' +
                '<span class="project-stat"><strong>' + (p.entityCount || 0) + '</strong> entities</span>' +
                '<span class="project-stat"><strong>' + (p.relationshipCount || 0) + '</strong> relationships</span>' +
              '</div>' +
            '</a>'
          ).join('') +
        '</div>';
        
        document.getElementById('projects-list').innerHTML = html;
      } catch (err) {
        console.error('Failed to load projects:', err);
        document.getElementById('projects-list').innerHTML = 
          '<div class="empty-state"><p>Failed to load projects</p></div>';
      }
    }
    
    loadProjects();
  </script>
</body>
</html>`;
}

/**
 * Project detail page HTML
 */
export function getProjectDetailHTML(id: string): string {
  return `<!DOCTYPE html>
<html lang="ja">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>YATA Global - Project Detail</title>
  <style>${STYLES}</style>
</head>
<body>
  ${NAV_HTML}
  <div class="container">
    <div id="project-detail">
      <div class="loading"><div class="spinner"></div></div>
    </div>
  </div>

  <script>
    const projectId = '${id}';
    
    async function loadProject() {
      try {
        const res = await fetch('/api/v1/projects/' + projectId);
        if (!res.ok) throw new Error('Project not found');
        const project = await res.json();
        renderProject(project);
      } catch (err) {
        console.error('Failed to load project:', err);
        document.getElementById('project-detail').innerHTML = 
          '<div class="empty-state"><p>Project not found</p><a href="/ui/projects" class="btn btn-primary">Back to Projects</a></div>';
      }
    }
    
    function renderProject(p) {
      const entities = p.entities || [];
      const relationships = p.relationships || [];
      
      const html = '<div class="detail-header">' +
        '<div>' +
          '<h1 class="detail-title">' + p.name + '</h1>' +
          '<div class="detail-meta">ID: ' + p.id + '</div>' +
        '</div>' +
      '</div>' +
      
      '<div class="card">' +
        '<h3>Description</h3>' +
        '<p>' + (p.description || 'No description') + '</p>' +
      '</div>' +
      
      '<div class="stats-grid">' +
        '<div class="stat-card">' +
          '<div class="stat-value">' + entities.length + '</div>' +
          '<div class="stat-label">Entities</div>' +
        '</div>' +
        '<div class="stat-card">' +
          '<div class="stat-value">' + relationships.length + '</div>' +
          '<div class="stat-label">Relationships</div>' +
        '</div>' +
      '</div>' +
      
      '<div class="section">' +
        '<h2 class="section-title">Entities</h2>' +
        (entities.length === 0 
          ? '<div class="empty-state"><p>No entities</p></div>'
          : '<div class="entity-grid">' + entities.map(e => 
              '<div class="entity-card">' +
                '<h4>' + (e.name || e.id) + '</h4>' +
                '<p>Type: ' + (e.type || '-') + '</p>' +
                '<p style="font-size: 0.8rem; color: #999;">ID: ' + e.id + '</p>' +
              '</div>'
            ).join('') + '</div>'
        ) +
      '</div>' +
      
      '<div class="section">' +
        '<h2 class="section-title">Relationships</h2>' +
        (relationships.length === 0 
          ? '<div class="empty-state"><p>No relationships</p></div>'
          : '<table class="table"><thead><tr><th>Source</th><th>Type</th><th>Target</th></tr></thead><tbody>' +
              relationships.map(r => 
                '<tr>' +
                  '<td>' + (r.source || r.sourceId) + '</td>' +
                  '<td><strong>' + (r.type || '-') + '</strong></td>' +
                  '<td>' + (r.target || r.targetId) + '</td>' +
                '</tr>'
              ).join('') +
            '</tbody></table>'
        ) +
      '</div>' +
      
      '<div style="margin-top: 2rem;">' +
        '<a href="/ui/projects" class="btn btn-secondary">← Back to Projects</a>' +
      '</div>';
      
      document.getElementById('project-detail').innerHTML = html;
    }
    
    loadProject();
  </script>
</body>
</html>`;
}
