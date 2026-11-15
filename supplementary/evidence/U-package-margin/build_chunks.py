#!/usr/bin/env python3
"""COMPUTED compiler orchestration only. Codex U18; no mathematical assumptions."""
from pathlib import Path
import concurrent.futures as cf
import subprocess,time,json

HERE=Path(__file__).resolve().parent
OUT=HERE/'.lake/build/lib/lean/MarginPieces'
OUT.mkdir(parents=True,exist_ok=True)
LOG=HERE/'chunk-logs';LOG.mkdir(exist_ok=True)
def build(p):
    start=time.monotonic()
    with (LOG/(p.stem+'.log')).open('w') as log:
        r=subprocess.run(['/Users/[user]/.elan/bin/lake','env','lean','-DautoImplicit=false',
                          '-o',str(OUT/(p.stem+'.olean')),str(p)],cwd=HERE,stdout=log,stderr=subprocess.STDOUT)
    return {'file':str(p.relative_to(HERE)),'exit':r.returncode,'seconds':round(time.monotonic()-start,2)}
paths=sorted((HERE/'MarginPieces').glob('Chunk*.lean'))
results=[]
with cf.ThreadPoolExecutor(max_workers=4) as pool:
    futures={pool.submit(build,p):p for p in paths}
    for future in cf.as_completed(futures):
        if future.cancelled():continue
        result=future.result();results.append(result)
        (HERE/'chunk-build.json').write_text(json.dumps({'status':'COMPUTED compiler runs','results':results},indent=2)+'\n')
        print(result,flush=True)
        if result['exit']:
            for f in futures:f.cancel()
            print('FAILURE: pending jobs cancelled; inspect the located chunk log.',flush=True)
            break
if any(r['exit'] for r in results):raise SystemExit(1)
if len(results)!=len(paths):raise SystemExit('not every chunk finished')
print('ALL CHUNKS COMPILE',len(results),flush=True)
