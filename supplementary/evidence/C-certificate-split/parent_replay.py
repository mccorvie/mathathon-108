"""COMPUTED parent re-run of producer validators, no producer files changed.
Fauzan re-derivation reusing Firsching; native same-family verification.
"""
from pathlib import Path
import importlib.util,json,sys,hashlib,contextlib,io,datetime
sys.dont_write_bytecode=True
P=Path(__file__).resolve().parent;E=P.parent;O=P/'parent-replay';O.mkdir(exist_ok=True)
def mod(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
v=mod('closing_schema_parent',E/'C-split-closing/validate_schema.py')
v.HERE=O
capture=io.StringIO()
with contextlib.redirect_stdout(capture):v.main()
(O/'SCHEMA.stdout').write_text(capture.getvalue())
schema=json.loads((O/'SCHEMA_VALIDATION.json').read_text())
original=json.loads((E/'C-split-closing/SCHEMA_VALIDATION.json').read_text())
assert schema==original
field=mod('field_parent',E/'C-split-field/check.py')
fr=field.check(E/'C-split-field/results/m32999_5000.json')
# Load only pure function definitions; original script has unguarded output writes.
src=E/'C-split-numeric/inspect_primitives.py';text=src.read_text();prefix=text.split('\nselected=inspect(',1)[0]
ns={'__file__':str(src),'__name__':'primitive_parent'};exec(compile(prefix,str(src),'exec'),ns)
primitive=ns['inspect'](E/'C-split-field/results/m32999_5000-witnesses.json',False)
out=dict(author='Codex lane C driver, same-family parent replay',status='COMPUTED producer code rerun; not independent implementation, human check or Lean gate',
 captured_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),closing_schema_equal=True,closing_cells=schema['cells'],closed_constraints=schema['closed_rational_constraints'],
 field=fr,field_counts=field.COUNTS,primitives=primitive,
 scripts=[dict(path=str(x),sha256=hashlib.sha256(x.read_bytes()).hexdigest()) for x in [E/'C-split-closing/validate_schema.py',E/'C-split-closing/frontier.py',E/'C-split-field/check.py',src]])
(O/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['closing_schema_equal','closing_cells','closed_constraints','field','field_counts']},indent=2))
