#!/usr/bin/env python3
"""Read-only inventory for the byte-exact unified project, Codex lane L."""
from pathlib import Path
import re,hashlib,json
here=Path(__file__).resolve().parent
repo=here.parents[3];evidence=here.parent
probes=['L-zeta5-general-s','U-energy-witness-lean/probe','U-translation-lean',
'U-finite-energy-duality','U-arcsine-identification','U-arcsine-pairs','U-field-average',
'U-arcsine-measure','U-integral-witness','U-package-margin','U-package-tail',
'lean_witness','lean_skip']
sources=[('root',repo)]+[(n,evidence/n) for n in probes]
modules={}
for label,base in sources:
    if label=='root':paths=list((repo/'Mathathon').rglob('*.lean'))+[repo/'Mathathon.lean']
    else:
        paths=[p for p in base.rglob('*.lean') if not any(x in p.relative_to(base).parts for x in ['.lake','v435','log','printed'])]
    for p in paths:
        rel=p.relative_to(base)
        if any(x.lower().startswith(('axiomaudit','audit','print','statement','check','scratch','test')) for x in [p.stem]):continue
        mod=str(rel.with_suffix('')).replace('/','.')
        b=p.read_bytes()
        modules.setdefault(mod,[]).append({'probe':label,'path':str(p.relative_to(repo)),
            'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),
            'imports':re.findall(r'^import (\S+)',b.decode(),re.M)})
conflicts={m:v for m,v in modules.items() if len(set(x['sha256'] for x in v))>1}
(here/'inventory.json').write_text(json.dumps(modules,indent=2)+'\n')
(here/'module-conflicts.json').write_text(json.dumps(conflicts,indent=2)+'\n')
print('modules',len(modules),'source copies',sum(map(len,modules.values())),'differing module names',len(conflicts))
for m,v in conflicts.items():print(m,[(x['probe'],x['bytes'],x['sha256'][:12]) for x in v])
