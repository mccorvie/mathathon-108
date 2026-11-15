"""Receive only a final-gated field component; replace certificate adapter.
Codex lane C, known Fauzan/Firsching re-derivation. No proof-term golf.
"""
from pathlib import Path
import subprocess,sys,json
P=Path(__file__).resolve().parent;source=P.parent/'C-split-field/project'
gate=(source/'log/LEAN_CHECK.md').read_text();assert '**Overall: PASS**' in gate and 'CSplitField.local_field_certificate' in gate
subprocess.run([sys.executable,str(P/'receive_component.py'),'--source',str(source),'--module','SplitField','--receipt',str(P/'FIELD_RECEPTION.json')],check=True)
f=P/'project/SplitAnalytic.lean';s=f.read_text();assert 'import LocalField' in s
s=s.replace('import LocalField','import SplitField')
a=s.index('/-- PROOF-DRAFT: old certified cover');b=s.index('/-- PROOF-DRAFT: the unchanged scalar transport',a)
s=s[:a]+'''/-- PROOF-DRAFT: complete selected129-cell field certificate, no caller hypotheses. -/
theorem local_field : U48.LocalFieldStatement ((-32999:ℝ)/5000) :=
  CSplitField.local_field_certificate

'''+s[b:]
s=s.replace("The first checkpoint keeps E607's field certificate byte-exactly, weakens\nits threshold, and instantiates the existing generic analytic transports.","This variant uses the selected129-cell field certificate and instantiates\nthe existing generic analytic transports at the selected threshold.")
f.write_text(s)
f=P/'project/SplitEntry.lean';s=f.read_text().replace('This first checkpoint keeps the old field cover and uses the new closing\ncertificate; a separate source-only export and final gate freeze it.','This full variant uses both selected numerical certificates; a separate\nsource-only export and final gate freeze the complete local import closure.')
f.write_text(s)
print('full129field adapter received; E607 and E611 frozen projects unchanged')
