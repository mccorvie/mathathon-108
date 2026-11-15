"""COMPUTED byte-exact component reception into lane C receiver only.
Codex lane C; Fauzan/Firsching re-derivation, no new theorem claim.
"""
from pathlib import Path
import argparse,json,re,hashlib,shutil,datetime
P=Path(__file__).resolve().parent;target=P/'project'
ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--module',required=True);ap.add_argument('--receipt',type=Path,required=True);a=ap.parse_args()
pending=[a.module];seen=set();rows=[];external=[]
while pending:
 m=pending.pop()
 if m in seen:continue
 seen.add(m);rel=Path(m.replace('.','/')+'.lean');src=a.source/rel
 if not src.exists():external.append(m);continue
 data=src.read_bytes();dst=target/rel;existed=dst.exists()
 if existed:assert dst.read_bytes()==data,('canonical overlap mismatch',m)
 else:
  dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
 for line in data.decode().splitlines():
  match=re.match(r'^(?:public\s+)?import\s+(.+)$',line)
  if match:pending.extend(match[1].split('--',1)[0].split())
 if not existed:
  stem=Path(m.replace('.','/'))
  for tree in ['lib/lean','ir']:
   folder=a.source/'.lake/build'/tree/stem.parent
   for product in folder.glob(stem.name+'.*'):
    if product.is_file():
     dest=target/'.lake/build'/tree/stem.parent/product.name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(product,dest)
 rows.append(dict(module=m,path=str(rel),sha256=hashlib.sha256(data).hexdigest(),lines=len(data.splitlines()),existing_byte_exact=existed))
config=(target/'lakefile.toml').read_text();registered=set(re.findall(r'\[\[lean_lib\]\]\s*\nname\s*=\s*"([^"]+)"',config))
for root in sorted({x['module'].split('.')[0] for x in rows}-registered):config+='\n[[lean_lib]]\nname = '+json.dumps(root)+'\n'
(target/'lakefile.toml').write_text(config)
a.receipt.write_text(json.dumps(dict(author='Codex lane C',status='COMPUTED byte-exact import closure copy; separate receiving gate required',created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source=str(a.source),target=str(target),module=a.module,modules=rows,external=sorted(external)),indent=2)+'\n')
print('received',len(rows),'local modules;',sum(not r['existing_byte_exact'] for r in rows),'new; canonical overlaps all exact')
