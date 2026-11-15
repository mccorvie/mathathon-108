#!/usr/bin/env python3
"""B12 source preparation only; copies source, preserves declaration bodies.
Codex, lane B,2026-11-14. Read exact provenance in SOURCE_MANIFEST.json.
"""
from pathlib import Path
import hashlib
import json
import re
import shutil

here=Path(__file__).resolve().parent
repo=here.parents[3]
evidence=here.parent
upstream=Path('/tmp/lane-b-zeta5')
projects=[evidence/'B-analytic-gram',evidence/'B-analytic-determinant',evidence/'B-analytic-envelope',evidence/'B-sharp-split',evidence/'B-bridge']
roots=['Determinant','Gram','BAnalyticEnvelope','Zeta5S.SmallPrimeF','Apery.Energy','Apery.Measure','Apery.EnergyConst','Apery.Stirling']
queue=list(roots); sources={}; imports={}
while queue:
 module=queue.pop()
 if module in sources:continue
 rel=Path(module.replace('.','/')+'.lean')
 candidates=[]
 for project in projects:
  for prefix in [Path('.'),Path('vendor')]:
   candidate=project/prefix/rel
   if candidate.is_file():candidates.append((project,candidate))
 if module.startswith('Apery.'):
  candidates=[(upstream,upstream/rel)]
 assert candidates,module
 project,source=candidates[0]
 raw=source.read_bytes()
 for _,other in candidates[1:]:assert raw==other.read_bytes(),f'copy collision:{module}'
 deps=[]
 for row in re.findall(r'^import (.+)$',raw.decode(),re.M):
  deps.extend(dep for dep in row.split() if not dep.startswith('Mathlib'))
 sources[module]=(project,source,raw)
 imports[module]=deps
 queue.extend(deps)

# The required new Statement.lean name collides with B8's old pole-target
# module. Rename that copied module and the one import edge, without touching
# any mathematical declaration. All other source bytes are retained exactly.
mapping={'Statement':'PoleTargets'}
invalid={'Statement'}
changed=True
while changed:
 old=len(invalid)
 invalid.update(m for m,deps in imports.items() if any(d in invalid for d in deps))
 changed=len(invalid)!=old
manifest=[]; cachecount=0
for module,(project,source,raw) in sorted(sources.items()):
 destmodule=mapping.get(module,module)
 data=re.sub(r'^import Statement$', 'import PoleTargets',raw.decode(),flags=re.M).encode()
 rel=Path(destmodule.replace('.','/')+'.lean')
 target=here/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
 transform='import Statement -> import PoleTargets' if data!=raw else 'none'
 source_name=str(source.relative_to(repo)) if source.is_relative_to(repo) else str(source)
 manifest.append({'module':destmodule,'original_module':module,'source':source_name,'destination':str(rel),
  'source_sha256':hashlib.sha256(raw).hexdigest(),'copy_sha256':hashlib.sha256(data).hexdigest(),
  'transformation':transform,'renamed_module':destmodule!=module,'declaration_bodies_unchanged':True})
 # Cached products are copied only for unchanged modules outside the import
 # cone of the renamed pole-target module. This is a cache convenience, not
 # verification; Lake remains responsible for dependency freshness checks.
 if module not in invalid and data==raw:
  build=project/'.lake/build'
  for prefix in ['lib/lean','ir']:
   srcbase=build/prefix/Path(module.replace('.','/'))
   if srcbase.parent.is_dir():
    for product in srcbase.parent.glob(srcbase.name+'.*'):
     dst=here/'.lake/build'/prefix/product.relative_to(build/prefix)
     dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(product,dst);cachecount+=1

(here/'SOURCE_MANIFEST.json').write_text(json.dumps({'status':'COMPUTED source/provenance only',
 'source_modules':len(manifest),'cache_files_copied':cachecount,'files':manifest},indent=2)+'\n')
shutil.copyfile(projects[0]/'lake-manifest.json',here/'lake-manifest.json')
for name in ['LICENSE','NOTICE']:
 shutil.copyfile(projects[0]/name,here/(name if name=='LICENSE' else 'NOTICE.B11'))
(here/'.lake').mkdir(exist_ok=True)
packages=here/'.lake/packages';expected=upstream/'.lake/packages'
if packages.is_symlink():assert packages.resolve()==expected.resolve()
elif packages.exists():raise RuntimeError('refusing to replace package directory')
else:packages.symlink_to(expected,target_is_directory=True)
leanlibs=sorted({mapping.get(m,m).split('.')[0] for m in sources}|{'Statement','Scalar','Pointwise','IntegralBound','RealProof','Closure'})
config='''name = "BAnalyticRealBound"
defaultTargets = ["RealProof"]
[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false
maxSynthPendingDepth = 3
[[require]]
name = "mathlib"
scope = "leanprover-community"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.33.1"
'''
for name in leanlibs:config+='\n[[lean_lib]]\nname = "'+name+'"\n'
(here/'lakefile.toml').write_text(config)
(here/'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
print(f'COMPUTED: {len(sources)} source modules; {len(invalid)} invalidated by module rename; {cachecount} cache products copied')
