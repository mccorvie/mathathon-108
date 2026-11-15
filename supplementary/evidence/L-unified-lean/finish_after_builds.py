#!/usr/bin/env python3
"""Wait for each existing cold build, then run each requested audit once. No retries."""
from pathlib import Path
import time,subprocess,sys,os,json,re,importlib.util
here=Path(__file__).resolve().parent;repo=here.parents[3]
os.environ['PATH']='/Users/[user]/.elan/bin:'+os.environ['PATH']
def await_build(path):
    while True:
        t=path.read_text() if path.exists() else ''
        if 'Build completed successfully' in t:return
        if re.search(r'^error:',t,re.M):raise RuntimeError('Compilation error in '+str(path))
        time.sleep(10)
def state(s):
    (here/'log/finish-state.json').write_text(json.dumps({'phase':s,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())})+'\n')
state('waiting for v4.33.1 cold build')
assert json.loads((here/'.lake/build433-status.json').read_text())['exit_code']==0
state('running v4.33.1 repository gate, provenance and original-statement comparison')
p=subprocess.run([sys.executable,str(here/'run_gate.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(here/'log/finish-gate.log').write_text(p.stdout)
if p.returncode:
    print(p.stdout[-5000:]);sys.exit(p.returncode)
state('waiting for compatible v4.35.0 build')
while not (here/'v435/log/compat-build-status.json').exists():time.sleep(10)
assert json.loads((here/'v435/log/compat-build-status.json').read_text())['exit_code']==0
p=subprocess.run(['lake','build','Unified108'],cwd=here/'v435',stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(here/'v435/log/final-cached-build.log').write_text(p.stdout)
assert p.returncode==0,p.stdout[-3000:]
state('auditing v4.35.0 standard axioms and comparing the two versions')
spec=importlib.util.spec_from_file_location('checker',repo/'scripts/lean_check.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
targets=sorted(json.loads((here/'targets.json').read_text()))
t=time.monotonic()
audit=c.audit(here/'v435',targets,'Unified108',3600)
(here/'v435/log/audit.json').write_text(json.dumps(audit,indent=2,ensure_ascii=False)+'\n')
gate=(here/'log/LEAN_CHECK.md').read_text()
rows=[]
for d in targets:
    m=re.search(r'### '+re.escape(chr(96)+d+chr(96))+r'\n'+chr(96)*3+r'lean\n(.*?)\n'+chr(96)*3,gate,re.S)
    assert m,d
    r=audit[d]
    rows.append({'declaration':d,'standard_axioms':not r['error'] and r['axioms'] is not None and set(r['axioms'])<=c.ALLOWED,
      'byte_identical_statement':r['statement']==m.group(1).strip()})
(here/'v435/log/comparison.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
out={'seconds':time.monotonic()-t,'declarations':len(rows),
     'standard_axiom_count':sum(r['standard_axioms'] for r in rows),
     'byte_identical_count':sum(r['byte_identical_statement'] for r in rows),
     'scope':'COMPUTED compatibility audit, not the hardwired v4.33.1 version gate'}
(here/'v435/log/audit-timing.json').write_text(json.dumps(out,indent=2)+'\n')
state('finished')
print(json.dumps(out))
sys.exit(0 if all(r['standard_axioms'] and r['byte_identical_statement'] for r in rows) else 2)
