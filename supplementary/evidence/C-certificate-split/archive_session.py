"""Archive native full raw histories outside immutable E607. No Lean work."""
from pathlib import Path
import json,gzip,hashlib,re,datetime
p=Path(__file__).resolve().parent
ids=['01a1dd30-fe96-74a3-907d-2562486a52c8','01a1dd3a-762a-7052-a252-79c82f790c79','01a1dd42-1439-7be1-abe3-f596da005357','01a1dd44-c082-7e91-90e6-48d3c363d6ea']
rows=[]
for sid in ids:
 matches=list(Path('/Users/[user]/.codex/sessions').rglob('*'+sid+'.jsonl'));assert len(matches)==1
 src=matches[0];data=src.read_bytes();assert not re.search(rb'nuc_(?:ak|oc)_[A-Za-z0-9_-]{12,}',data)
 lines=data.splitlines();parsed=[json.loads(x) for x in lines]
 dst=p/('native-session-'+sid+'.jsonl.gz');dst.write_bytes(gzip.compress(data,mtime=0));assert gzip.decompress(dst.read_bytes())==data
 rows.append(dict(session=sid,source=str(src),archive=dst.name,bytes=len(data),records=len(lines),sha256=hashlib.sha256(data).hexdigest(),last_timestamp=parsed[-1].get('timestamp')))
(p/'SESSION_ARCHIVES.json').write_text(json.dumps(dict(author='Codex lane C',status='COMPUTED raw full native snapshots through stated cutoff; refresh at completion',captured_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sessions=rows),indent=2)+'\n')
print([(x['session'],x['records']) for x in rows])
