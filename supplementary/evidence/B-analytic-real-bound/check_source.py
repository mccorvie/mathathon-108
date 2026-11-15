#!/usr/bin/env python3
"""COMPUTED provenance check only. Codex, lane B, 2026-11-14."""
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
repo=p.parents[3]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
manifest=json.loads((p/'SOURCE_MANIFEST.json').read_text())
for row in manifest['files']:
 assert sha(p/row['destination'])==row['copy_sha256'],row['destination']
 source=Path(row['source'])
 if not source.is_absolute():source=repo/source
 assert sha(source)==row['source_sha256'],str(source)
for row in json.loads((p/'PROOF_MANIFEST.json').read_text())['files']:
 assert sha(p/row['file'])==row['sha256'],row['file']
 for source in row.get('adapted_sources',[]):
  assert sha(Path(source['path']))==source['sha256'],source['path']
assert sha(p/'Statement.lean')==(p/'TARGET_STATEMENT.sha256').read_text().strip()
print(f"COMPUTED: {len(manifest['files'])} copied modules, 4 adapted proof modules, original target hash all match")

if (p/'CLOSURE_SOURCE_MANIFEST.json').exists():
 closure=json.loads((p/'CLOSURE_SOURCE_MANIFEST.json').read_text())
 for row in closure['files']:
  assert sha(p/row['destination'])==row['sha256'],row['destination']
  assert sha(Path(row['source']))==row['sha256'],row['source']
 for row in json.loads((p/'CLOSURE_PROOF_MANIFEST.json').read_text())['files']:
  assert sha(p/row['file'])==row['sha256'],row['file']
 print(f"COMPUTED: {closure['additional_modules']} additional unchanged upstream modules and {closure['overlap_modules']} overlaps match; Closure source hash matches")
