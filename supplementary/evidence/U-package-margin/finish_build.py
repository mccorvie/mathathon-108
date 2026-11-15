#!/usr/bin/env python3
"""COMPUTED build orchestration only, Codex U18. No mathematical assertion is assumed."""
from pathlib import Path
import json,time,subprocess

HERE=Path(__file__).resolve().parent
while True:
    try:
        d=json.loads((HERE/'chunk-build.json').read_text())
        if any(r['exit'] for r in d['results']):raise SystemExit('chunk failure')
        if len(d['results'])==84:break
    except (FileNotFoundError,json.JSONDecodeError):pass
    time.sleep(3)
def compile(name):
    log=Path('/private/tmp')/('u18-'+name+'.log')
    t=time.monotonic()
    with log.open('w') as out:
        r=subprocess.run(['/Users/[user]/.elan/bin/lake','env','lean','-DautoImplicit=false',
          '-o',str(HERE/'.lake/build/lib/lean'/f'{name}.olean'),str(HERE/f'{name}.lean')],
          cwd=HERE,stdout=out,stderr=subprocess.STDOUT)
    print(name,'exit',r.returncode,'seconds',round(time.monotonic()-t,2),flush=True)
    return r.returncode
if compile('UPackageMargin'):raise SystemExit(1)
if compile('PrefixBounds'):raise SystemExit(1)
