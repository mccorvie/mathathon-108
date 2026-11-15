"""Capture immutable sources and compare printed types; this does not run Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,datetime
root=Path(__file__).resolve().parents[4]
out=Path(__file__).resolve().parent
project=root/'problems/108-zeta-odd-autopsy/evidence/L-merge/project'
judged=Path('/Users/[user]/code/mathathon-108')
commit='f385dbf705d94fb411b74c9692639e508fd0b546'
files=['Mathathon/P108/SStep.lean','Mathathon/P108/SStepAll.lean',
'Mathathon/P108/OuterDefs.lean','Mathathon/P108/InnerShift.lean',
'Mathathon/P108/OuterValues58.lean','Mathathon/P108/OffsetGap.lean',
'LeanWitness/ClassLoss.lean','Mathathon/P108/LaiSkip.lean','Mathathon/P108/LaiSkipData.lean',
'AllM.lean','ShortArithmeticFloor.lean','Zeta5S/FiniteStep.lean','Zeta5S/SharpAssembly.lean']
semantic={'Mathathon/P108/SStep.lean','Mathathon/P108/OuterDefs.lean',
'Mathathon/P108/InnerShift.lean','LeanWitness/ClassLoss.lean',
'Mathathon/P108/LaiSkip.lean','Mathathon/P108/LaiSkipData.lean'}
# Mask nested comments while retaining offsets/line numbers.
def mask_comments(s):
    r=list(s); i=0; depth=0
    while i<len(s):
        if depth:
            if s.startswith('/-',i): depth+=1; r[i:i+2]='  '; i+=2
            elif s.startswith('-/',i): depth-=1; r[i:i+2]='  '; i+=2
            else:
                if s[i]!='\n':r[i]=' '
                i+=1
        elif s.startswith('/-',i):depth=1; r[i:i+2]='  ';i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i);j=len(s) if j<0 else j
            r[i:j]=' '*(j-i);i=j
        else:i+=1
    return ''.join(r)
command=re.compile(r'^(?:(?:noncomputable|private|protected)\s+)*(?:def|abbrev|theorem|lemma|instance|structure|namespace|end|variable|section|open|attribute|set_option|#\w+)\b',re.M)
definition=re.compile(r'^(?:(?:noncomputable|private|protected)\s+)*(?:def|abbrev)\s+(\S+)')
receipts=[]; defs=[]
for f in files:
    b=(project/f).read_bytes()
    c=subprocess.run(['git','-C',str(judged),'show',commit+':'+f],check=True,capture_output=True).stdout
    assert b==c,f
    receipts.append({'path':f,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'identical_to_judged_commit':True})
    if f not in semantic:continue
    s=b.decode(); mask=mask_comments(s); starts=list(command.finditer(mask))
    for i,m in enumerate(starts):
        end=starts[i+1].start() if i+1<len(starts) else len(s)
        dm=definition.match(mask[m.start():end])
        if dm:
            # The masked tail removes comments that introduce the next command.
            trimmed=len(mask[m.start():end].rstrip())
            defs.append({'file':f,'line':s[:m.start()].count('\n')+1,'name':dm.group(1),'text':s[m.start():m.start()+trimmed]})
tex=(root/'report/report.tex').read_text()
(root/'.lake/R-final-compare-report.tex').write_text(tex)
gate=(project/'log/LEAN_CHECK.md').read_text()
blocks={n:b.strip() for n,b in re.findall(r'### `([^`]+)`\s*```lean\s*(.*?)```',gate,re.S)}
items=[(5,'Mathathon.P108.thetaPkg_sstep'),(6,'Mathathon.P108.theta_sstep_7_6'),
(7,'Mathathon.P108.sstep_ge'),(8,'Mathathon.P108.thetaPkg_odd_ge'),(9,'Mathathon.P108.gain58_formal'),
(20,'Mathathon.P108.classLoss_witness'),(20,'Mathathon.P108.lai_offset_gap_7_2'),
(20,'Mathathon.P108.Skip.lai_skip_witness'),(20,'Mathathon.P108.Skip.Delta_eq')]
checks=[]; excerpts=[]
normalize=lambda s:re.sub(r'\s+','',s).lstrip('@')
for d,name in items:
    start=tex.index('\\textbf{D'+str(d)+'.}')
    nxt=tex.find('\\textbf{D'+str(d+1)+'.}',start)
    part=tex[start:nxt if nxt>=0 else len(tex)]
    verb=re.search(r'\\begin\{verbatim\}(.*?)\\end\{verbatim\}',part,re.S).group(1)
    lines=verb.strip().split('\n\n')
    statement=next(x for x in lines if x.lstrip().startswith(name+' :'))
    printed=blocks[name]
    same=normalize(statement)==normalize(printed)
    checks.append({'report_id':'D'+str(d),'declaration':name,'report_type_matches_gate_ignoring_whitespace':same,'gate_printed_type':printed,'report_printed_type':statement})
    excerpts.append((name,printed))
assert all(x['report_type_matches_gate_ignoring_whitespace'] for x in checks),checks
meta={'captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'Codex GPT-6.1 sol, lane R, no subagents','scope':'Statement/type/definition review only; no new Lean gate or proof-body audit','report_sha256':hashlib.sha256(tex.encode()).hexdigest(),'report_snapshot_ignored':'.lake/R-final-compare-report.tex','judged_local_commit':commit,'judged_commit_is_local_not_public_push_receipt':True,'gate_report_sha256':hashlib.sha256(gate.encode()).hexdigest(),'sources':receipts,'definition_count':len(defs),'checks':checks}
(out/'INPUTS.json').write_text(json.dumps(meta,indent=2)+'\n')
(out/'DEFINITIONS.json').write_text(json.dumps(defs,indent=2,ensure_ascii=False)+'\n')
md=['# Unfolded custom definitions\n','COMPUTED: verbatim source extraction at the hashes in INPUTS.json. Namespace context: Mathathon.P108 for scalar definitions and ClassLoss; ClassLoss list operations are in Mathathon.P108.Poly; skip definitions/data are in Mathathon.P108.Skip. All library primitives are Mathlib objects. This is a source appendix, not a new proof.\n']
for x in defs:
    md.append(f"## {x['file']}:{x['line']} — {x['name']}\n\n```lean\n{x['text']}\n```\n")
(out/'UNFOLDED_DEFINITIONS.md').write_text('\n'.join(md))
md=['# Printed statements\n','COMPUTED: the nine report types equal their submitted-project gate types after deleting whitespace. This does not compare meanings by itself; see REVIEW.md.\n']
for name,p in excerpts:md.append('## '+name+'\n\n```lean\n'+p+'\n```\n')
(out/'PRINTED_STATEMENTS.md').write_text('\n'.join(md))
print(json.dumps({'source_files_equal_judged_commit':len(receipts),'definitions':len(defs),'printed_types_equal':len(checks),'report_sha256':meta['report_sha256']}))
