#!/usr/bin/env python3
"""COMPUTED local build/printed-axiom replay, Codex outer_sum E432.

The repository's parent lean_check.py gate and human comparison are separate.
Live logs remain in /tmp; only completed logs are archived in this probe.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import shutil
import subprocess
import time

r = Path(__file__).resolve().parent
lake = '/tmp/lean-4.33.1-linux/bin/lake'
stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
history = r / 'build-history'
history.mkdir(exist_ok=True)
jobs = [('sources', ['python3', 'check_sources.py']),
        ('build', [lake, 'build', 'Final']),
        ('audit', [lake, 'env', 'lean', 'Audit.lean'])]
records = []
for label, command in jobs:
    live = Path('/tmp') / f'b-full-bridge-{stamp}-{label}.log'
    start = time.monotonic()
    with live.open('w') as out:
        result = subprocess.run(command, cwd=r, stdout=out, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - start
    saved = history / live.name
    shutil.copy2(live, saved)
    record = dict(name=label, command=command, exit_code=result.returncode,
        seconds=round(elapsed, 3), log=str(saved.relative_to(r)))
    records.append(record)
    print(json.dumps(record), flush=True)
    if result.returncode:
        break

names = ['inner_local_statement', 'inner_limit_statement',
         'explicit_normalizer_limit_statement', 'zeta_seven_explicit_margin_limit_statement']
axioms_ok = False
if len(records) == 3 and all(x['exit_code'] == 0 for x in records):
    output = (r / records[-1]['log']).read_text()
    axioms_ok = all(f"'BFullBridge.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" in output for name in names)
files = ['Final.lean', 'Audit.lean', 'ExplicitTargets.lean', 'RangeTargets.lean',
         'lakefile.toml', 'lake-manifest.json', 'lean-toolchain']
hashes = {name: hashlib.sha256((r/name).read_bytes()).hexdigest() for name in files}
packet = dict(status='COMPUTED local build and printed-axiom replay; parent gate/human comparison separate',
    timestamp_utc=stamp, records=records, four_standard_axiom_outputs=axioms_ok,
    all_pass=len(records) == 3 and all(x['exit_code'] == 0 for x in records) and axioms_ok,
    file_sha256=hashes)
(r / 'build-check.json').write_text(json.dumps(packet, indent=2)+'\n')
raise SystemExit(0 if packet['all_pass'] else 1)
