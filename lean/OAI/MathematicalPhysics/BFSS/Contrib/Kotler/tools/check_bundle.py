#!/usr/bin/env python3
"""Check the frozen source package and its complete declaration/axiom report."""
from pathlib import Path
import argparse,hashlib,json,re,sys

HERE=Path(__file__).resolve().parents[1]
LEAN=HERE.parents[4]
ROOT=LEAN.parent
PREFIX='OAI.MathematicalPhysics.BFSS.Contrib.Kotler.'
ALLOWED={'propext','Classical.choice','Quot.sound'}

def require(ok,message):
    if not ok:raise SystemExit(message)

def git_blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()

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

def check_report(path):
    names={r['name'] for r in json.loads((HERE/'declarations.json').read_text())['declarations']}
    text=path.read_text()
    reports=re.findall(r"(?m)^'([^\n]+)' depends on axioms: \[([^\]]*)\]",text)
    empty=re.findall(r"(?m)^'([^\n]+)' does not depend on any axioms",text)
    require(len(reports)+len(empty)==len(names),'declaration report count mismatch')
    require({n for n,_ in reports}|set(empty)==names,'declaration report names mismatch')
    for name,axs in reports:
        require({a.strip() for a in axs.split(',') if a.strip()}<=ALLOWED,'unpermitted axioms: '+name+' '+axs)
    require(not re.search(r'(?m)^.*(?:warning:|error:)',text),'Lean diagnostic in declaration audit')
    require('BFSS_BUNDLE_DECLARATION_AUDIT_PASS' in text,'missing completion marker')
    print('BFSS_BUNDLE_AXIOM_REPORT_PASS:',len(names),'declarations')

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--report',type=Path);args=parser.parse_args()
    check_sources()
    if args.report:check_report(args.report)
