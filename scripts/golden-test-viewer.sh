#!/bin/bash
# Golden Test Viewer - starts a web server with dynamic test discovery
# Usage: ./scripts/golden-test-viewer.sh [port]

set -e

PORT="${1:-8080}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

cd "$PROJECT_ROOT/tests"

python3 - "$PORT" << 'PYSERVER'
import http.server
import json
import sys
from pathlib import Path
from urllib.parse import unquote

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8080

HTML = '''<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Ziku Golden Test Viewer</title>
  <style>
    :root{--bg:#1e1e2e;--bg2:#313244;--bg3:#45475a;--text:#cdd6f4;--text2:#a6adc8;--accent:#89b4fa;--success:#a6e3a1;--error:#f38ba8;--border:#585b70}
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:system-ui,sans-serif;background:var(--bg);color:var(--text);line-height:1.6}
    header{background:var(--bg2);padding:1rem 2rem;border-bottom:1px solid var(--border);position:sticky;top:0;z-index:100}
    h1{font-size:1.3rem;margin-bottom:.75rem}
    .controls{display:flex;gap:.75rem;flex-wrap:wrap;align-items:center}
    input[type=text]{padding:.4rem .8rem;border:1px solid var(--border);border-radius:6px;background:var(--bg);color:var(--text);min-width:200px}
    input:focus{outline:none;border-color:var(--accent)}
    .btn{padding:.4rem .8rem;border:1px solid var(--border);border-radius:6px;background:var(--bg3);color:var(--text2);cursor:pointer}
    .btn:hover{border-color:var(--accent);color:var(--text)}
    .btn.active{background:var(--accent);color:var(--bg);border-color:var(--accent)}
    .stats{color:var(--text2);font-size:.85rem;margin-left:auto}
    main{padding:1.5rem 2rem;max-width:1400px;margin:0 auto}
    .category{margin-bottom:2rem}
    .category h2{font-size:1.1rem;color:var(--accent);border-bottom:2px solid var(--accent);padding-bottom:.3rem;margin-bottom:.75rem}
    .test-card{background:var(--bg2);border:1px solid var(--border);border-radius:6px;margin-bottom:.5rem;overflow:hidden}
    .test-card.success{border-left:3px solid var(--success)}
    .test-card.error{border-left:3px solid var(--error)}
    .test-card.hidden{display:none}
    .test-header{display:flex;justify-content:space-between;padding:.5rem .75rem;background:var(--bg3);cursor:pointer;font-family:monospace;font-size:.9rem}
    .badge{font-size:.7rem;padding:.1rem .4rem;border-radius:3px;margin-left:.5rem}
    .badge.success{background:var(--success);color:var(--bg)}
    .badge.error{background:var(--error);color:var(--bg)}
    .test-content{display:none;padding:.75rem}
    .test-card.expanded .test-content{display:block}
    .panels{display:grid;grid-template-columns:1fr 1fr;gap:.75rem}
    @media(max-width:800px){.panels{grid-template-columns:1fr}}
    .panel{background:var(--bg);border-radius:4px;overflow:hidden}
    .panel-header{padding:.3rem .5rem;background:var(--bg3);font-size:.7rem;color:var(--text2);text-transform:uppercase}
    .panel pre{padding:.75rem;margin:0;font-size:.85rem;white-space:pre-wrap;word-break:break-word;overflow-x:auto}
    .panel.input pre{color:#f9e2af}
    .panel.output pre{color:var(--success)}
    .error .panel.output pre{color:var(--error)}
    .loading{color:var(--text2);font-style:italic}
    .no-results{text-align:center;padding:2rem;color:var(--text2)}
  </style>
</head>
<body>
  <header>
    <h1>Ziku Golden Test Viewer</h1>
    <div class="controls">
      <input type="text" id="search" placeholder="Search tests...">
      <button class="btn active" data-filter="all">All</button>
      <button class="btn" data-filter="success">Success</button>
      <button class="btn" data-filter="error">Error</button>
      <button class="btn" id="expandAll">Expand All</button>
      <span class="stats" id="stats"></span>
    </div>
  </header>
  <main id="main"><p class="loading">Loading tests...</p></main>
  <script>
    const state={tests:[],filter:'all',search:'',expanded:new Set(),allExpanded:false};
    async function load(){const r=await fetch('/api/tests');state.tests=(await r.json()).tests;render();}
    async function loadContent(t){
      if(t.input!==undefined)return;
      try{const[i,o]=await Promise.all([fetch('/'+t.path+'.ziku'),fetch('/'+t.path+'.golden')]);
        t.input=await i.text();t.output=await o.text();}
      catch(e){t.input=t.output='(failed)';}
    }
    function esc(s){return s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');}
    function render(){
      const m=document.getElementById('main'),f=state.tests.filter(t=>(state.filter==='all'||t.type===state.filter)&&(state.search===''||t.name.toLowerCase().includes(state.search.toLowerCase())));
      const g={};f.forEach(t=>(g[t.category]=g[t.category]||[]).push(t));
      if(!f.length){m.innerHTML='<p class="no-results">No tests match.</p>';return;}
      m.innerHTML=Object.entries(g).map(([c,ts])=>`<section class="category"><h2>${c} (${ts.length})</h2>${ts.map(t=>{
        const k=t.category+'/'+t.name,x=state.allExpanded||state.expanded.has(k);
        return `<div class="test-card ${t.type} ${x?'expanded':''}" data-key="${k}">
          <div class="test-header" onclick="toggle('${k}')"><span>${t.name}<span class="badge ${t.type}">${t.type}</span></span><span>${x?'▲':'▼'}</span></div>
          <div class="test-content">${t.input!==undefined?`<div class="panels"><div class="panel input"><div class="panel-header">Input</div><pre>${esc(t.input)}</pre></div><div class="panel output"><div class="panel-header">Expected</div><pre>${esc(t.output)}</pre></div></div>`:'<p class="loading">Loading...</p>'}</div>
        </div>`;}).join('')}</section>`).join('');
      document.getElementById('stats').textContent=f.length+' of '+state.tests.length;
    }
    async function toggle(k){const t=state.tests.find(x=>x.category+'/'+x.name===k);if(state.expanded.has(k))state.expanded.delete(k);else{state.expanded.add(k);await loadContent(t);}render();}
    document.getElementById('search').addEventListener('input',e=>{state.search=e.target.value;render();});
    document.querySelectorAll('[data-filter]').forEach(b=>b.addEventListener('click',()=>{document.querySelectorAll('[data-filter]').forEach(x=>x.classList.remove('active'));b.classList.add('active');state.filter=b.dataset.filter;render();}));
    document.getElementById('expandAll').addEventListener('click',async()=>{state.allExpanded=!state.allExpanded;document.getElementById('expandAll').textContent=state.allExpanded?'Collapse All':'Expand All';if(state.allExpanded)await Promise.all(state.tests.map(loadContent));render();});
    load();
  </script>
</body>
</html>'''

def get_tests():
    tests = []
    golden = Path('golden')
    if not golden.exists():
        return tests
    for cat in sorted(golden.iterdir()):
        if not cat.is_dir() or cat.name == 'scheme':
            continue
        for typ in ['success', 'error']:
            type_dir = cat / typ
            if not type_dir.is_dir():
                continue
            for f in sorted(type_dir.glob('*.ziku')):
                tests.append({
                    'category': cat.name,
                    'type': typ,
                    'name': f.stem,
                    'path': f'golden/{cat.name}/{typ}/{f.stem}'
                })
    return tests

class Handler(http.server.SimpleHTTPRequestHandler):
    def do_GET(self):
        path = unquote(self.path)
        if path == '/' or path == '/index.html':
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.end_headers()
            self.wfile.write(HTML.encode())
        elif path == '/api/tests':
            self.send_response(200)
            self.send_header('Content-Type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps({'tests': get_tests()}).encode())
        else:
            super().do_GET()

    def log_message(self, fmt, *args):
        pass  # Suppress logging

print(f'Golden Test Viewer: http://localhost:{PORT}')
print('Press Ctrl+C to stop')
http.server.HTTPServer(('', PORT), Handler).serve_forever()
PYSERVER
