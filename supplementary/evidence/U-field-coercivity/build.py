#!/usr/bin/env python3
"""Codex (GPT-6), U43/E238: reproduce the direct Lean compilation only."""
from pathlib import Path
import datetime, json, resource, shutil, subprocess, sys, time
p=Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_NOFILE, (16384, resource.getrlimit(resource.RLIMIT_NOFILE)[1]))
(p/'.lake/build/lib/lean').mkdir(parents=True,exist_ok=True)
start=time.monotonic()
cmd=['/Users/[user]/.elan/bin/lake','env','lean','-DautoImplicit=false','-o','.lake/build/lib/lean/FieldCoercivity.olean','FieldCoercivity.lean']
with (p/'.lake/compile-live.stdout').open('w') as out:
 r=subprocess.run(cmd,cwd=p,stdout=out,stderr=subprocess.STDOUT)
shutil.copyfile(p/'.lake/compile-live.stdout',p/'compiler.log')
record={'author':'Codex (GPT-6)','status':'COMPUTED','command':cmd,'exit_code':r.returncode,'elapsed_seconds':time.monotonic()-start,'completed_at':datetime.datetime.now().astimezone().isoformat(),'soft_fd_limit':resource.getrlimit(resource.RLIMIT_NOFILE)[0]}
(p/'build-result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
print((p/'compiler.log').read_text())
sys.exit(r.returncode)
