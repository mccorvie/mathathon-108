#!/usr/bin/env python3
"""Codex E213/U18. COMPUTED direct compiler records for the final composition."""
from pathlib import Path
import subprocess, time, json
rows=[]
for module in ['PackageTail.Centered','PackageTail.Primitive','PackageTail.Bound','AllM']:
    source=module.replace('.', '/')+'.lean'
    output=Path('.lake/build/lib/lean')/(module.replace('.', '/')+'.olean')
    output.parent.mkdir(parents=True,exist_ok=True)
    log=Path('/private/tmp')/('u18-allM-'+module.replace('.','-')+'.log')
    start=time.monotonic()
    with log.open('w') as f:
        result=subprocess.run(['/Users/[user]/.elan/bin/lake','env','lean','-DautoImplicit=false','-o',str(output),source],stdout=f,stderr=subprocess.STDOUT)
    row={'module':module,'exit':result.returncode,'seconds':round(time.monotonic()-start,3),'log':str(log)}
    rows.append(row)
    Path('composition-build.json').write_text(json.dumps({'author':'Codex','status':'COMPUTED direct compiler runs','results':rows},indent=2)+'\n')
    print(row,flush=True)
    if result.returncode: raise SystemExit(result.returncode)
