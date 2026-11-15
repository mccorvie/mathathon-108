#!/usr/bin/env python3
"""COMPUTED bounded receiving build; Codex GPT-6.1 sol, lane C.
Re-derivation of Fauzan's theorem reusing Firsching's formalisation
(mo271/Zeta5 be1c0d82, Apache-2.0; Comparator metadata Paul-Lez).
No target is certified by the scheduler; the repository --final gate follows.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import datetime
import hashlib
import json
import shutil
import subprocess
import time

root = Path(__file__).resolve().parent
source = root.parent / 'C-heavy-analysis'
modules = json.loads((root / 'SIZE_HEAVY.json').read_text())['current']['modules']
producer = json.loads((source / 'SOURCE_MANIFEST.json').read_text())['modules']
assert '**Overall: PASS**' in (source / 'log/LEAN_CHECK.md').read_text()
finished = set(producer)
for name, record in producer.items():
    assert (root / record['destination']).read_bytes() == (source / record['destination']).read_bytes()
pending = set(modules) - finished
dependencies = {name: set(row['imports']) & set(modules) for name, row in modules.items()}
live = root / '.lake/receiving-bounded'
live.mkdir(parents=True, exist_ok=True)
archive = root / 'log/receiving-bounded'
archive.mkdir(parents=True, exist_ok=True)
records = []
running = {}
start = time.monotonic()
failed = False

def snapshot():
    packet = dict(status='COMPUTED bounded receiving build; final gate pending',
        total=len(modules), complete=len(finished), failed=failed, parallel=6,
        producer_gated_baseline_modules=len(producer), running=sorted(running.values()),
        seconds=round(time.monotonic() - start, 3), records=records)
    (live / 'STATUS.json').write_text(json.dumps(packet, indent=2) + '\n')

def build(name):
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    log = live / (name + '-' + stamp + '.log')
    before = time.monotonic()
    with log.open('w') as stream:
        result = subprocess.run([str(Path.home() / '.elan/bin/lake'), 'build', name],
            cwd=root, stdout=stream, stderr=subprocess.STDOUT)
    copied = archive / log.name
    shutil.copy2(log, copied)
    return dict(module=name, exit_code=result.returncode,
        seconds=round(time.monotonic() - before, 3),
        finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        source_sha256=hashlib.sha256((root / modules[name]['path']).read_bytes()).hexdigest(),
        log=str(copied.relative_to(root)))

with ThreadPoolExecutor(max_workers=6) as pool:
    while pending or running:
        if not failed:
            ready = sorted(name for name in pending if dependencies[name] <= finished)
            while ready and len(running) < 6:
                name = ready.pop(0)
                pending.remove(name)
                running[pool.submit(build, name)] = name
        if not running:
            assert not pending or failed, 'Unresolved local dependency graph'
            break
        snapshot()
        done, _ = wait(running, return_when=FIRST_COMPLETED)
        for future in done:
            name = running.pop(future)
            receipt = future.result()
            records.append(receipt)
            print(json.dumps(receipt), flush=True)
            if receipt['exit_code']:
                failed = True
            else:
                finished.add(name)
        snapshot()
if failed:
    raise SystemExit(1)
snapshot()
print(json.dumps(dict(status='COMPUTED receiving build completed; repository gate still required',
    modules=len(finished), actual_receiving_builds=len(records), seconds=round(time.monotonic()-start, 3))))
