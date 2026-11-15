#!/usr/bin/env python3
"""COMPUTED exact prior closure copy. Codex lane B, 2026-11-14.
Sources only by default. --copy-cache is used only after the parent confirms
its serial prior-source build has completed. Cache copying is not certification.
"""
from pathlib import Path
import argparse,hashlib,json,shutil
args=argparse.ArgumentParser()
args.add_argument('--copy-cache',action='store_true')
opt=args.parse_args()
here=Path(__file__).resolve().parent
up=Path('/tmp/lane-b-zeta5')
sha=lambda data:hashlib.sha256(data).hexdigest()
info=json.loads((here/'ENERGY_CLOSURE.json').read_text())
rows=[];products=0
for row in info['files']:
 m=row['module'];rel=Path(m.replace('.','/')+'.lean')
 source=Path(row['source']);data=source.read_bytes()
 assert sha(data)==row['sha256'],str(source)
 dest=here/rel
 if row['already_in_conditional_probe']:
  assert dest.read_bytes()==data,m
 else:
  if dest.exists():assert dest.read_bytes()==data,m
  else:
   dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 rows.append({'module':m,'source':str(source),'destination':str(rel),
  'sha256':sha(data),'byte_exact':True,'already_in_conditional_probe':row['already_in_conditional_probe']})
 if opt.copy_cache:
  for prefix in ['lib/lean','ir']:
   build=up/'.lake/build'/prefix
   base=build/Path(m.replace('.','/'))
   for src in base.parent.glob(base.name+'.*'):
    dst=here/'.lake/build'/prefix/src.relative_to(build)
    dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);products+=1
(here/'CLOSURE_SOURCE_MANIFEST.json').write_text(json.dumps({
 'status':'COMPUTED copy/provenance only; full gate and human comparison pending',
 'upstream':'mo271/Zeta5','commit':info['commit'],'authors':info['authors'],'license':info['license'],
 'additional_modules':info['additional_modules'],'overlap_modules':info['already_shared_modules'],
 'cache_products_copied_this_run':products,'files':rows},indent=2)+'\n')
print(f"COMPUTED: {info['additional_modules']} exact additional modules copied; {info['already_shared_modules']} overlaps match; {products} cache products copied")
