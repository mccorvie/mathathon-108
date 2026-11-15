#!/usr/bin/env python3
"""E312 byte-exact source closure; Codex lane L. Original probes are read-only."""
from pathlib import Path
import json,shutil,re
here=Path(__file__).resolve().parent;repo=here.parents[3]
inv=json.loads((here/'inventory.json').read_text())
entries=['Mathathon','Zeta5S','LeanWitness','UArcsinePairs','IntegralWitness','AllM']
closure=set()
def visit(m):
    if m in closure:return
    assert m in inv,('missing',m)
    closure.add(m)
    for imp in inv[m][0]['imports']:
        if imp in inv:visit(imp)
        else:assert imp.startswith(('Mathlib','Lean','Std','Batteries')),('unmapped',m,imp)
for m in entries:visit(m)
manifest=[]
for m in sorted(closure):
    v=inv[m][0];src=repo/v['path'];dst=here/Path(*m.split('.')).with_suffix('.lean')
    dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
    assert src.read_bytes()==dst.read_bytes()
    manifest.append({'module':m,'destination':str(dst.relative_to(here)),'source_probe':v['probe'],
      'source':v['path'],'sha256':v['sha256'],'all_original_copies':inv[m]})
(here/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(here/'Unified108.lean').write_text('\n'.join('import '+m for m in entries)+'\n')
roots=sorted({m.split('.')[0] for m in closure}|{'Unified108'})
config='''name = "Unified108"
defaultTargets = ["Unified108"]
[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false
pp.unicode.fun = true
maxSynthPendingDepth = 3
[[require]]
name = "mathlib"
scope = "leanprover-community"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.33.1"
'''
for m in roots:config+='\n[[lean_lib]]\nname = "'+m+'"\n'
(here/'lakefile.toml').write_text(config)
for name in ['lean-toolchain','lake-manifest.json']:shutil.copyfile(repo/name,here/name)
(here/'.lake').mkdir(exist_ok=True)
if not (here/'.lake/packages').exists():(here/'.lake/packages').symlink_to(repo/'.lake/packages',target_is_directory=True)
refs=[]
for label,prefix in [('lean_skip','LeanSkip'),('U-translation-lean','UTranslation')]:
    for m,vs in inv.items():
        if m==prefix or m.startswith(prefix+'.'):
            for v in vs:
                if v['probe']!=label:continue
                dst=here/'reference'/label/(v['path'].split('/'+label+'/')[-1]+'.txt')
                dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(repo/v['path'],dst)
                refs.append({'module':m,'source':v['path'],'archive':str(dst.relative_to(here)),'sha256':v['sha256']})
(here/'reference-manifest.json').write_text(json.dumps(refs,indent=2)+'\n')
targets={}
for row in (repo/'log/CLAIMS.md').read_text().splitlines():
    if not row.startswith('| C108-'):continue
    claim=row.split('|')[1].strip()
    for token in re.findall(r'lean:([^\s·,;|]+)',row):
        token=token.strip(chr(96)).rstrip(').')
        d,_,p=token.partition('@')
        if re.fullmatch(r'[\w.\u0080-\uffff]+',d):
            targets.setdefault(d,[]).append({'claim':claim,'original_probe':p or 'root'})
for d in re.findall(r'^#print axioms (\S+)',(repo/'problems/108-zeta-odd-autopsy/evidence/L-zeta5-general-s/Zeta5S/Axioms.lean').read_text(),re.M):
    targets.setdefault(d,[]).append({'claim':'L complete audit','original_probe':'problems/108-zeta-odd-autopsy/evidence/L-zeta5-general-s'})
(here/'targets.json').write_text(json.dumps(targets,indent=2,ensure_ascii=False)+'\n')
src=['import Unified108','open Lean Elab Command']
for d in sorted(targets):
    src+=['run_elab do','  let n := "'+d+'".toName',
      '  let some m ← findModuleOf? n | throwError "missing declaration '+d+'"',
      '  logInfo m!"@@SOURCE '+d+' {m}"']
(here/'Provenance.lean').write_text('\n'.join(src)+'\n')
(here/'log').mkdir(exist_ok=True)
print('Copied active modules:',len(closure),'audit targets:',len(targets))
print('Library roots:',','.join(roots))
