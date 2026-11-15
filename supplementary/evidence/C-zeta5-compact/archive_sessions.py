#!/usr/bin/env python3
"""COMPUTED native transcript snapshots; Codex GPT-6.1 sol, lane C.
Re-derivation of Fauzan's theorem reusing Firsching/Paul-Lez formalisation;
this attribution utility makes no mathematical claim.
"""
from pathlib import Path
import datetime
import gzip
import hashlib
import json
import re

here = Path(__file__).resolve().parent
repo = here.parents[3]
native = Path.home() / '.codex/sessions/2026/11/14'
destination = repo / 'log/transcripts/native-[team machine]'
destination.mkdir(parents=True, exist_ok=True)
sessions = {
    'driver': '01a1dd30-fe96-74a3-907d-2562486a52c8',
    'c3_arithmetic': '01a1dd3a-762a-7052-a252-79c82f790c79',
    'c_leading': '01a1dd42-1439-7be1-abe3-f596da005357',
    'c_heavy_analysis': '01a1dd44-c082-7e91-90e6-48d3c363d6ea',
}
receipts = []
for role, session in sessions.items():
    files = list(native.glob('*' + session + '.jsonl'))
    assert len(files) == 1, (role, files)
    source = files[0]
    data = source.read_bytes()
    assert not re.search(rb'nuc_(?:ak|oc)_[A-Za-z0-9_-]{12,}', data), 'Possible key: do not archive'
    rows = []
    records = []
    for line in data.splitlines():
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            break
        rows.append(line)
        records.append(record)
    complete = b'\n'.join(rows) + b'\n'
    filename = 'C-lane-01a1dd30.jsonl.gz' if role == 'driver' else 'native-session-' + session + '.jsonl.gz'
    output = destination / filename
    with gzip.open(output, 'wb') as stream:
        stream.write(complete)
    with gzip.open(output, 'rb') as stream:
        assert stream.read() == complete
    receipts.append(dict(role=role, source=str(source), destination=str(output.relative_to(repo)),
        session_id=session, records=len(records), bytes=len(complete),
        last_record_timestamp=records[-1].get('timestamp'),
        sha256=hashlib.sha256(complete).hexdigest(),
        models=sorted({row.get('payload', {}).get('model') for row in records
                       if row.get('type') == 'turn_context' and row.get('payload', {}).get('model')})))
packet = dict(status='COMPUTED raw native snapshots; active sessions continue after cutoff',
    captured_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), sessions=receipts)
(here / 'TRANSCRIPTS.json').write_text(json.dumps(packet, indent=2) + '\n')
print(json.dumps([dict(role=row['role'], records=row['records'], bytes=row['bytes']) for row in receipts]))
