"""E608 computed source preparation; numerical instance constants only.
Codex lane C. Known Fauzan theorem via Firsching; not a new proof claim.
"""
from pathlib import Path
import shutil,json,re,hashlib,datetime
p=Path(__file__).resolve().parent; old=p.parent/'C-zeta5-compact/project'; new=p/'project'
assert datetime.datetime.now(datetime.timezone.utc)>=datetime.datetime(2026,11,15,5,30,11,tzinfo=datetime.timezone.utc)
new.mkdir(exist_ok=True);rows=[]
for src in old.rglob('*.lean'):
 if '.lake' in src.parts:continue
 rel=src.relative_to(old);dst=new/rel;dst.parent.mkdir(parents=True,exist_ok=True)
 data=src.read_bytes();dst.write_bytes(data);rows.append({'path':str(rel),'source_sha256':hashlib.sha256(data).hexdigest()})
for name in ['lean-toolchain','lake-manifest.json','LICENSE','NOTICE']:
 src=old/name
 if src.exists():shutil.copy2(src,new/name)
config=(old/'lakefile.toml').read_text().replace('defaultTargets = ["CompactEntry"]','defaultTargets = ["ArithmeticEntry"]')
(new/'lakefile.toml').write_text(config)
for name in ['Interface.lean','CArithProofs.lean','ArithInterface.lean']:
 dst=new/name;s=dst.read_text();s=re.sub(r'\b400\b','1000000',s)
 if name=='Interface.lean':s=s.replace('-2678491 / 2000000','-2650371 / 2000000').replace('-1323 / 200','-32999 / 5000')
 dst.write_text(s)
packages=new/'.lake/packages';packages.parent.mkdir(exist_ok=True)
common=(p.parent/'L-zeta5-general-s/v435/.lake/packages').resolve()
if not packages.exists():packages.symlink_to(common,target_is_directory=True)
# Cache only hash-identical old local build artifacts; Lake still validates traces.
for src in (old/'.lake/build').rglob('*'):
 if not src.is_file():continue
 rel=src.relative_to(old/'.lake/build');dst=new/'.lake/build'/rel
 dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
(p/'RECEIVER_PREP.json').write_text(json.dumps({'author':'Codex lane C','status':'COMPUTED copied source hashes; necessary numeric instances changed only','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_project':str(old),'project':str(new),'adapted_files':['Interface.lean','CArithProofs.lean','ArithInterface.lean'],'changes':['M400→1000000','u -2678491/2000000→-2650371/2000000','interface T -1323/200→-32999/5000'],'sources':rows},indent=2)+'\n')
print('prepared',len(rows),'sources',new)
