#!/usr/bin/env python3
from pathlib import Path
import os,signal,time,subprocess,json
here=Path(__file__).resolve().parent
while not (here/'log/finish-gate.log').exists():time.sleep(10)
pid=json.loads((here/'log/build-control.json').read_text())['trial_process_group']
p=subprocess.run(['ps','-p',str(pid),'-o','command='],capture_output=True,text=True)
if p.returncode==0 and 'run_build.py --435' in p.stdout:
    os.killpg(pid,signal.SIGCONT)
    (here/'log/trial-resumed.json').write_text(json.dumps({'group':pid,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())})+'\n')
    print('Resumed owned v4.35 trial after v4.33.1 gate')
