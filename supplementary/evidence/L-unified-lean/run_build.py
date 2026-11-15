#!/usr/bin/env python3
"""One requested trial build, exact process duration."""
from pathlib import Path
import os,subprocess,time,json,sys
here=Path(__file__).resolve().parent
where=here/'v435' if '--435' in sys.argv else here
os.environ['PATH']='/Users/[user]/.elan/bin:'+os.environ['PATH']
t=time.monotonic()
with (where/'.lake/build-live.log').open('w') as f:p=subprocess.run(['lake','build','Unified108'],cwd=where,stdout=f,stderr=subprocess.STDOUT)
(where/'log/build.log').write_bytes((where/'.lake/build-live.log').read_bytes())
out={'seconds':time.monotonic()-t,'exit_code':p.returncode,'trial':'v4.35.0' if '--435' in sys.argv else 'v4.33.1'}
(where/'log/build-timing.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out));sys.exit(p.returncode)
