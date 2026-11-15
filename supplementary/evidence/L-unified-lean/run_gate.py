#!/usr/bin/env python3
"""Repository gate then actual defining-module/source provenance and statement comparison."""
from pathlib import Path
import importlib.util,json,os,subprocess,sys,re,time,hashlib
here=Path(__file__).resolve().parent;repo=here.parents[3]
os.environ['PATH']='/Users/[user]/.elan/bin:'+os.environ['PATH']
targets=json.loads((here/'targets.json').read_text())
cmd=[sys.executable,str(repo/'scripts/lean_check.py'),'--root',str(here),'--lib','Unified108']
for d in sorted(targets):cmd+=['--decl',d]
t=time.monotonic()
p=subprocess.run(cmd,cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(here/'log/gate.log').write_text(p.stdout)
(here/'log/gate-timing.json').write_text(json.dumps({'seconds':time.monotonic()-t,'exit_code':p.returncode,'declarations':len(targets)},indent=2)+'\n')
print(p.stdout)
if p.returncode:sys.exit(p.returncode)
# The checker scans the aggregator named by --lib. Disclose the known root
# placeholder across the actual active-source inventory, instead of letting
# that narrow scan suggest every source declaration is sorry-free.
report=here/'log/LEAN_CHECK.md'
with report.open('a') as f:
    f.write('\n## Full active-source scope\n\nThe library source scan above covers the Unified108 import aggregator. '
      'The active source inventory also contains the known conditional '
      'Mathathon.P108.Skip.Delta_eq placeholder in Mathathon/P108/LaiSkip.lean. '
      f'It and its sorry-dependent content-valuation consequences are excluded from the {len(targets)} selected declarations. '
      'The axiom audit above checks every selected declaration and its transitive proof dependencies. '
      'See source-manifest.json and README.md.\n')
p=subprocess.run(['lake','env','lean','Provenance.lean'],cwd=here,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(here/'log/provenance.log').write_text(p.stdout)
if p.returncode:print(p.stdout[-5000:]);sys.exit(p.returncode)
actual=dict(re.findall(r'@@SOURCE (\S+) (\S+)',p.stdout))
sources={r['module']:r for r in json.loads((here/'source-manifest.json').read_text())}
assert set(actual)==set(targets),(set(targets)-set(actual))
rows=[]
for d,m in sorted(actual.items()):
    src=sources[m]
    assert hashlib.sha256((here/src['destination']).read_bytes()).hexdigest()==src['sha256']
    rows.append({'declaration':d,'module':m,'source_probe':src['source_probe'],'source':src['source'],
      'sha256':src['sha256'],'destination':src['destination'],'original_claims':targets[d]})
(here/'declaration-source-map.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
(here/'DECLARATIONS.md').write_text('# Unified #108 declaration provenance (COMPUTED)\n\n| Declaration | Source probe | Source file | SHA256 |\n|---|---|---|---|\n'+''.join('| '+r['declaration']+' | '+r['source_probe']+' | '+r['source']+' | '+r['sha256']+' |\n' for r in rows))
# The gate has printed the current statements; compare every retained original baseline.
gate=(here/'log/LEAN_CHECK.md').read_text()
baseline=json.loads((here/'baseline-statements.json').read_text())
comparisons=[]
for d,old in baseline.items():
    m=re.search(r'### '+re.escape(chr(96)+d+chr(96))+r'\n'+chr(96)*3+r'lean\n(.*?)\n'+chr(96)*3,gate,re.S)
    assert m,d
    new=m.group(1).strip()
    for b in old:
        comparisons.append({'declaration':d,'original_report':b['report'],'byte_identical_statement':new==b['statement'],
             'whitespace_identical_statement':re.sub(r'\s+',' ',new)==re.sub(r'\s+',' ',b['statement'])})
(here/'statement-comparison.json').write_text(json.dumps(comparisons,indent=2,ensure_ascii=False)+'\n')
print('Defining module/source mapped:',len(rows))
print('Original statement comparisons:',len(comparisons),'exact:',sum(r['byte_identical_statement'] for r in comparisons))
if not all(r['byte_identical_statement'] for r in comparisons):sys.exit(2)
