#!/usr/bin/env python3
"""COMPUTED exact-copy provenance for B14; no theorem certification. Codex lane B."""
from pathlib import Path
import hashlib,json,sys
here=Path(__file__).resolve().parent
root=Path(sys.argv[1])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
paths=[here/(name+'.lean') for name in ['BAnalyticIntegral','BAnalyticMoments','Statement','Zeta5S']]+list((here/'Zeta5S').glob('*.lean'))
for p in sorted(paths):
    rel=p.relative_to(here)
    src=here/'../B-analytic-gram'/rel
    if p.read_bytes()!=src.read_bytes():raise SystemExit('Copy mismatch: '+str(rel))
    rows.append({'file':str(rel),'source':'../B-analytic-gram/'+str(rel),'byte_equal':True,'sha256':sha(p)})
print(json.dumps({'status':'COMPUTED','copied_files':rows,
 'upstream_commit':'be1c0d82070da93c343f93bffd495b8ebc323645',
 'adapted_source':{'file':'Apery/Zeta5.lean','lines':[13,18],
 'changes':'natural s>=2 instead of5; actual imported zetaS; numeral-only Nat.cast_ofNat rewrite omitted',
 'sha256':sha(root/'Apery/Zeta5.lean')},
 'mathlib_input':{'file':'Mathlib/NumberTheory/LSeries/RiemannZeta.lean',
 'theorem':'zeta_nat_eq_tsum_of_gt_one','line':223,'pinned_revision':'0df444a360eaa60ab8c11dca51a86af692955474'},
 'new_source_sha256':sha(here/'ZetaIdentification.lean')},indent=2))
