#!/usr/bin/env python3
"""Check the frozen source package and its complete declaration/axiom report."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys

HERE=Path(__file__).resolve().parents[1]
LEAN=HERE.parents[4]
ROOT=LEAN.parent
PREFIX='OAI.MathematicalPhysics.BFSS.Contrib.Kotler.'
ALLOWED={'propext','Classical.choice','Quot.sound'}

def require(ok,message):
    if not ok:raise SystemExit(message)

def git_blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()

def check_declarations(data):
    declarations=json.loads((HERE/'declarations.json').read_text())['declarations']
    names=[row['name'] for row in declarations]
    require(names and len(names)==len(set(names)),'empty or duplicate declaration inventory')
    modules={row['module']:row for row in data['modules']};sources={}
    for row in declarations:
        require(row['module'] in modules and row['path']==modules[row['module']]['path'],
            'declaration source mismatch: '+row['name'])
        if row['path'] not in sources:sources[row['path']]=(ROOT/row['path']).read_text().splitlines()
        lines=sources[row['path']]
        require(isinstance(row['line'],int) and 1<=row['line']<=len(lines),
            'declaration line mismatch: '+row['name'])
        # Read the complete source token, including Unicode suffixes. This is a
        # spelling check for the indexed headers, not a Lean namespace resolver.
        token=re.search(r'\b'+re.escape(row['kind'])+r'\s+([^\s:({\[]+)',lines[row['line']-1])
        require(token is not None and (row['name']==token[1] or row['name'].endswith('.'+token[1])),
            'declaration spelling mismatch: '+row['name'])
    audited=re.findall(r'^#print axioms (.+)$',(HERE/'Audit.lean').read_text(),re.M)
    require(len(audited)==len(names) and set(audited)==set(names),'audit/index declaration mismatch')
    print('BFSS_BUNDLE_DECLARATION_INDEX_PASS:',len(names),'source spellings')

def check_contribution_base():
    data=json.loads((HERE/'manifest.json').read_text())
    subprocess.run(['git','merge-base','--is-ancestor',data['contribution_base_commit'],'HEAD'],cwd=ROOT,check=True)
    notes=data['required_notes']
    require(git_blob((ROOT/notes['path']).read_bytes())==notes['blob'],'required follow-up notes mismatch')
    print('BFSS_BUNDLE_CONTRIBUTION_BASE_PASS: follow-up ancestry and original NOTES.md')

def check_sources():
    data=json.loads((HERE/'manifest.json').read_text())
    require((LEAN/'lean-toolchain').read_text().strip()==data['toolchain'],'toolchain mismatch')
    lake=json.loads((LEAN/'lake-manifest.json').read_text())
    require(next(p['rev'] for p in lake['packages'] if p['name']=='mathlib')==data['mathlib_commit'],'Mathlib revision mismatch')
    rows=data['modules'];mods={r['module'] for r in rows}
    require(len(mods)==len(rows)==789,'module inventory mismatch')
    order=data['topological_order'];require(set(order)==mods and len(order)==len(mods),'build order mismatch')
    done=set()
    for n in order:
        row=next(r for r in rows if r['module']==n)
        require(git_blob((ROOT/row['path']).read_bytes())==row['destination_blob'],'source blob mismatch: '+row['path'])
        for im in row['imports']:
            if im.startswith(PREFIX):require(im in mods,'missing contribution import: '+im)
            if im in mods:require(im in done,'non-topological dependency: '+n+' -> '+im)
        done.add(n)
    print('BFSS_BUNDLE_SOURCE_PREFLIGHT_PASS: 789 production modules')
    check_declarations(data)

def check_report(path):
    names={r['name'] for r in json.loads((HERE/'declarations.json').read_text())['declarations']}
    text=path.read_text()
    require(not re.search(r'(?m)^.*\b(?:warning|error)(?:\([^)\n]*\))?:',text),
        'Lean diagnostic in declaration audit')
    reports=re.findall(r"(?m)^'([^\n]+)' depends on axioms: \[([^\]]*)\]",text)
    empty=re.findall(r"(?m)^'([^\n]+)' does not depend on any axioms",text)
    require(len(reports)+len(empty)==len(names),'declaration report count mismatch')
    require({n for n,_ in reports}|set(empty)==names,'declaration report names mismatch')
    for name,axs in reports:
        require({a.strip() for a in axs.split(',') if a.strip()}<=ALLOWED,'unpermitted axioms: '+name+' '+axs)
    require('BFSS_BUNDLE_DECLARATION_AUDIT_COMPLETE' in text,'missing completion marker')
    print('BFSS_BUNDLE_AXIOM_REPORT_PASS:',len(names),'declarations')

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--report',type=Path)
    parser.add_argument('--check-contribution-base',action='store_true');args=parser.parse_args()
    check_sources()
    if args.check_contribution_base:check_contribution_base()
    if args.report:check_report(args.report)
