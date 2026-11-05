#!/usr/bin/env python3
"""Compile every selected module freshly, then check the combined import and axiom inventory."""
from pathlib import Path
import argparse,json,os,subprocess,sys

HERE=Path(__file__).resolve().parents[1]
LEAN=HERE.parents[4]

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--logs',type=Path,required=True)
    args=parser.parse_args();args.logs.mkdir(parents=True,exist_ok=True)
    subprocess.run([sys.executable,str(HERE/'tools/check_bundle.py')],check=True)
    data=json.loads((HERE/'manifest.json').read_text());rows={r['module']:r for r in data['modules']}
    external=sorted({im for r in rows.values() for im in r['imports'] if im.startswith('OAI.') and im not in rows})
    with (args.logs/'upstream.log').open('w') as out:
        subprocess.run(['lake','build',*external],cwd=LEAN,stdout=out,stderr=subprocess.STDOUT,check=True,timeout=3150)
    modules=list(data['topological_order'])
    modules += ['OAI.MathematicalPhysics.BFSS.Contrib.Kotler.'+n for n in ['Concrete','Representations','LocalGeometry','GeometryAndRepresentations','PhysicalOperators','All']]
    for index,name in enumerate(modules,1):
        stem=name.replace('.','/');source=LEAN/(stem+'.lean');target=LEAN/'.lake/build/lib/lean'/(stem+'.olean')
        target.parent.mkdir(parents=True,exist_ok=True);target.unlink(missing_ok=True)
        print(f'[{index}/{len(modules)}] {name}',flush=True)
        log=args.logs/f'{index:04d}-{name.split(".")[-1]}.log'
        with log.open('w') as out:
            subprocess.run(['lake','env','lean','-DautoImplicit=false','-DwarningAsError=true','-o',str(target.relative_to(LEAN)),stem+'.lean'],cwd=LEAN,stdout=out,stderr=subprocess.STDOUT,check=True,timeout=840)
        if not target.exists() or not target.stat().st_size:raise SystemExit('Missing fresh object: '+name)
    audit=args.logs/'declaration-audit.log'
    with audit.open('w') as out:
        subprocess.run(['lake','env','lean','-DautoImplicit=false','-DwarningAsError=true',str((HERE/'Audit.lean').relative_to(LEAN))],cwd=LEAN,stdout=out,stderr=subprocess.STDOUT,check=True,timeout=600)
    subprocess.run([sys.executable,str(HERE/'tools/check_bundle.py'),'--report',str(audit)],check=True)
    print('BFSS_COMPLETE_CONTRIBUTION_BUILD_PASS',flush=True)

if __name__=='__main__':main()
