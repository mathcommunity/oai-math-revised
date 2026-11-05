#!/usr/bin/env python3
"""Compile every selected module freshly, then check the combined import and axiom inventory."""
from pathlib import Path
import argparse,json,shutil,subprocess,sys

HERE=Path(__file__).resolve().parents[1]
LEAN=HERE.parents[4]

def run_logged(command,log,*,timeout,env=None):
    with log.open('w') as out:
        try:
            subprocess.run(command,cwd=LEAN,env=env,stdout=out,stderr=subprocess.STDOUT,check=True,timeout=timeout)
        except (subprocess.CalledProcessError,subprocess.TimeoutExpired):
            out.flush()
            print(f'FAILED: {log.name}\n{log.read_text(errors="replace")}',flush=True)
            raise

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--logs',type=Path,required=True)
    args=parser.parse_args();args.logs.mkdir(parents=True,exist_ok=True)
    subprocess.run([sys.executable,str(HERE/'tools/check_bundle.py')],check=True)
    data=json.loads((HERE/'manifest.json').read_text());rows={r['module']:r for r in data['modules']}
    external=sorted({im for r in rows.values() for im in r['imports'] if im.startswith('OAI.') and im not in rows})
    run_logged(['lake','build',*external],args.logs/'upstream.log',timeout=3150)
    # Resolve Lake once. Repeating `lake env` reparses every package configuration;
    # its administrative warnings must also stay separate from the Lean audit.
    with (args.logs/'lake-environment.log').open('w') as out:
        resolved=subprocess.run(['lake','env',sys.executable,'-c',
            'import json,os; print(json.dumps(dict(os.environ)))'],cwd=LEAN,
            stdout=subprocess.PIPE,stderr=out,text=True,check=True,timeout=120)
    env=json.loads(resolved.stdout)
    lean=shutil.which('lean',path=env['PATH'])
    if not lean:raise SystemExit('Lean executable missing from resolved Lake environment')
    run_logged([lean,'--version'],args.logs/'lean-version.log',timeout=30,env=env)
    modules=list(data['topological_order'])
    modules += ['OAI.MathematicalPhysics.BFSS.Contrib.Kotler.'+n for n in ['Concrete','Representations','LocalGeometry','GeometryAndRepresentations','PhysicalOperators','All']]
    for index,name in enumerate(modules,1):
        stem=name.replace('.','/');source=LEAN/(stem+'.lean');target=LEAN/'.lake/build/lib/lean'/(stem+'.olean')
        target.parent.mkdir(parents=True,exist_ok=True);target.unlink(missing_ok=True)
        print(f'[{index}/{len(modules)}] {name}',flush=True)
        log=args.logs/f'{index:04d}-{name.split(".")[-1]}.log'
        run_logged([lean,'-DautoImplicit=false','-DwarningAsError=true','-o',str(target.relative_to(LEAN)),stem+'.lean'],log,timeout=840,env=env)
        if not target.exists() or not target.stat().st_size:raise SystemExit('Missing fresh object: '+name)
    audit=args.logs/'declaration-audit.log'
    run_logged([lean,'-DautoImplicit=false','-DwarningAsError=true',str((HERE/'Audit.lean').relative_to(LEAN))],audit,timeout=600,env=env)
    subprocess.run([sys.executable,str(HERE/'tools/check_bundle.py'),'--report',str(audit)],check=True)
    print('BFSS_COMPLETE_CONTRIBUTION_BUILD_PASS',flush=True)

if __name__=='__main__':main()
