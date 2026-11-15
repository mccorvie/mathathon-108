#!/usr/bin/env python3
"""COMPUTED reachable-source sizes, Codex GPT-6.1 sol, lane C.
A re-derivation of Fauzan's theorem reusing Firsching's formalisation
(mo271/Zeta5 be1c0d82; Apache-2.0; Comparator metadata Paul-Lez).
Counts source text, never certifies a theorem or infers compression from a stub.
"""
from pathlib import Path
from collections import defaultdict
import argparse
import hashlib
import json
import re

parser = argparse.ArgumentParser()
parser.add_argument('--module', default='CompactEntry')
parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parent)
parser.add_argument('--scope', default='unconditional compact endpoint; gate recorded separately')
parser.add_argument('--output', type=Path)
args = parser.parse_args()
integration = args.project / 'COMPACT_INTEGRATION.json'
if not integration.is_file():
    integration = args.project.parent / 'COMPACT_INTEGRATION.json'
field_modules = set()
if integration.is_file():
    field_modules = {row['module'] for row in json.loads(integration.read_text())['added']
                     if 'U-compact-local-field/final435' in row['provider']}

def category(module):
    if module in field_modules:
        return 'event compact field certificate'
    if module.startswith(('Apery.Table.', 'Apery.Table2.')):
        return 'prior energy table modules'
    if module.startswith('MarginPieces.'):
        return 'event arithmetic scalar cell tables'
    if module.startswith('Apery.'):
        return 'other prior Apery modules'
    if module.startswith('Zeta5S.'):
        return 'symbolic arithmetic and finite normalization'
    if module.startswith('Mathathon.'):
        return 'local event arithmetic package and PNT interface'
    return 'other local bridge, analysis, interfaces and assembly'

def closure(project, root):
    pending = [root]
    records = {}
    external = set()
    while pending:
        module = pending.pop()
        if module in records:
            continue
        relative = Path(module.replace('.', '/') + '.lean')
        source = project / relative
        if not source.is_file():
            external.add(module)
            continue
        data = source.read_bytes()
        imports = []
        for line in data.decode().splitlines():
            match = re.match(r'^(?:public\s+)?import\s+(.+)$', line)
            if match:
                imports.extend(match.group(1).split('--', 1)[0].split())
        records[module] = dict(path=str(relative), lines=len(data.splitlines()),
            bytes=len(data), sha256=hashlib.sha256(data).hexdigest(),
            category=category(module), imports=imports)
        pending.extend(imports)
    grouped = defaultdict(lambda: dict(files=0, lines=0))
    for record in records.values():
        grouped[record['category']]['files'] += 1
        grouped[record['category']]['lines'] += record['lines']
    return dict(root=root, files=len(records), lines=sum(row['lines'] for row in records.values()),
        groups=dict(grouped), external_imports=sorted(external), modules=records)

baseline = closure(Path.home() / 'mathathon-cache/108/zeta5', 'Apery.Main')
assert (baseline['files'], baseline['lines']) == (209, 138236), 'Baseline drift: inspect pinned sources'
assert baseline['groups']['prior energy table modules'] == dict(files=118, lines=117029)
current = closure(args.project, args.module)
packet = dict(status='COMPUTED source/import audit only', author='Codex GPT-6.1 sol lane C',
    current_scope=args.scope, unit='local Lean source lines; external dependencies excluded for BOTH closures',
    warning='Source counts do not certify a theorem or establish novelty; use the separate recorded gate and exact scope.',
    current=current, baseline=baseline)
output = args.output or args.project / 'SIZE_CURRENT.json'
output.write_text(json.dumps(packet, indent=2) + '\n')
print(json.dumps(dict(scope=args.scope, current_files=current['files'], current_lines=current['lines'],
    baseline_files=baseline['files'], baseline_lines=baseline['lines'], groups=current['groups'])))
