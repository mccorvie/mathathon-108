"""COMPUTED source-only receiver export, followed by its own final gate.
Codex lane C; numerical-certificate revision of Fauzan/Firsching re-derivation.
No source proof-body compression; copy exact reachable source bytes.
"""
from pathlib import Path
import json,shutil,re,hashlib,argparse
P=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--size',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--module',default='SplitEntry');a=ap.parse_args()
source=P/'project';audit=json.loads(a.size.read_text())['current'];assert audit['root']==a.module
assert not a.output.exists(),'fresh variant output required'
a.output.mkdir(parents=True);rows=[]
for module,row in audit['modules'].items():
 f=source/row['path'];data=f.read_bytes();assert hashlib.sha256(data).hexdigest()==row['sha256']
 dst=a.output/row['path'];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
 rows.append(dict(module=module,path=row['path'],sha256=row['sha256'],lines=row['lines']))
 for tree in ['lib/lean','ir']:
  stem=Path(module.replace('.','/'));folder=source/'.lake/build'/tree/stem.parent
  for product in folder.glob(stem.name+'.*'):
   if product.is_file():
    dest=a.output/'.lake/build'/tree/stem.parent/product.name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(product,dest)
config=(source/'lakefile.toml').read_text().split('[[lean_lib]]',1)[0]
config=re.sub(r'defaultTargets = \[[^\n]*\]',f'defaultTargets = ["{a.module}"]',config)
for root in sorted({m.split('.')[0] for m in audit['modules']}):config+='\n[[lean_lib]]\nname = '+json.dumps(root)+'\n'
(a.output/'lakefile.toml').write_text(config)
for name in ['lean-toolchain','lake-manifest.json','LICENSE','NOTICE']:shutil.copy2(source/name,a.output/name)
packages=a.output/'.lake/packages';packages.parent.mkdir(exist_ok=True);packages.symlink_to((source/'.lake/packages').resolve(),target_is_directory=True)
(a.output/'SOURCE_MANIFEST.json').write_text(json.dumps(dict(author='Codex lane C',status='COMPUTED exact closure export; separate final gate required',root=a.module,files=rows,local_files=len(rows),local_lines=sum(r['lines'] for r in rows)),indent=2)+'\n')
(a.output/'README.md').write_text('''# Numerical certificate variant

Fauzan re-derivation using Moritz Firsching mo271/Zeta5@be1c0d82,
Apache-2.0; Comparator metadata by Paul-Lez. No new theorem or independent
proof is claimed. All local numerical data, helper proofs and imports are
included byte-exactly in SOURCE_MANIFEST.json. Standard Mathlib/PNT are
excluded from both source-line counts. Lean/Mathlib v4.35.0 are pinned;
local ignored cache symlinks are a convenience, never a source dependency.

Build: `lake exe cache get`, then `lake build`. Separate final gate and
literal statements are recorded in log/LEAN_CHECK.md. No label upgrades
are made by this export script.
''')
print(json.dumps(dict(project=str(a.output),files=len(rows),lines=sum(r['lines'] for r in rows))))
