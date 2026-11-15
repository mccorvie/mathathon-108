"""COMPUTED whole local import-closure size in physical Lean source lines.
Codex lane C; Fauzan re-derivation using Firsching, no novelty claim.
All local data/helper files count. External Mathlib/PNT excluded on both sides.
"""
from pathlib import Path
import argparse,hashlib,re,json,datetime
P=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--project',type=Path,default=P/'project');ap.add_argument('--module',default='SplitEntry');ap.add_argument('--output',type=Path,default=P/'SIZE_VARIANT.json');a=ap.parse_args()
def closure(root,module):
 pending=[module];rows={};external=set()
 while pending:
  m=pending.pop()
  if m in rows:continue
  f=root/(m.replace('.','/')+'.lean')
  if not f.is_file():external.add(m);continue
  data=f.read_bytes();imports=[]
  for line in data.decode().splitlines():
   match=re.match(r'^(?:public\s+)?import\s+(.+)$',line)
   if match:imports.extend(match[1].split('--',1)[0].split())
  rows[m]=dict(path=str(f.relative_to(root)),lines=len(data.splitlines()),bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),imports=imports)
  pending.extend(imports)
 return dict(root=module,files=len(rows),lines=sum(x['lines'] for x in rows.values()),bytes=sum(x['bytes'] for x in rows.values()),modules=rows,external_imports=sorted(external))
base=closure(P.parent/'C-zeta5-compact/project','CompactEntry');assert base['lines']==69392 and base['files']==282
cur=closure(a.project,a.module);assert a.module in cur['modules']
physical=list(x for x in a.project.rglob('*.lean') if '.lake' not in x.parts)
out=dict(author='Codex lane C',status='COMPUTED source size only; use separate final gate',created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),unit='physical local Lean source lines, including comments, numerical data and helpers; external dependencies excluded equally',current=cur,baseline=base,physical_project_files=len(physical),physical_project_lines=sum(len(x.read_bytes().splitlines()) for x in physical),reduction_percent=100*(1-cur['lines']/base['lines']),build_forecast_lines=35123,qualification_ceiling_lines=52044)
a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['physical_project_files','physical_project_lines','reduction_percent']},indent=2));print('reachable',cur['files'],cur['lines'])
