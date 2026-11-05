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

def object_path(name):
    return LEAN/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean')

def remove_objects(name):
    target=object_path(name)
    for path in [target,Path(str(target)+'.private'),Path(str(target)+'.server'),target.with_suffix('.ilean')]:
        path.unlink(missing_ok=True)

def compile_modules(modules,rows,lean,env,logs,*,timeout=840):
    # Remove every selected old object before processing the graph. A failed Lean
    # process may emit recovery objects; those must never reach its dependants.
    for name in modules:remove_objects(name)
    results=[];status={};progress=logs/'module-progress.jsonl';progress.write_text('')
    for index,name in enumerate(modules,1):
        stem=name.replace('.','/');target=object_path(name)
        blocked=[im for im in rows[name]['imports'] if im in rows and status.get(im)!='passed']
        entry={'module':name,'status':'blocked' if blocked else 'passed'}
        print(f'[{index}/{len(modules)}] {name}',flush=True)
        if blocked:
            entry['blocked_by']=blocked
            print('BLOCKED: '+', '.join(blocked),flush=True)
        else:
            target.parent.mkdir(parents=True,exist_ok=True)
            log=logs/f'{index:04d}-{name.split(".")[-1]}.log';entry['log']=log.name
            try:
                run_logged([lean,'-DautoImplicit=false','-DwarningAsError=true','-o',str(target.relative_to(LEAN)),stem+'.lean'],log,timeout=timeout,env=env)
                if not target.exists() or not target.stat().st_size:
                    raise RuntimeError('Missing fresh object: '+name)
            except (subprocess.CalledProcessError,subprocess.TimeoutExpired,RuntimeError) as error:
                entry['status']='failed';entry['reason']=str(error)
                remove_objects(name)
                print('MODULE FAILED: '+name+': '+str(error),flush=True)
        status[name]=entry['status'];results.append(entry)
        with progress.open('a') as out:out.write(json.dumps(entry)+'\n')
    counts={s:sum(r['status']==s for r in results) for s in ['passed','failed','blocked']}
    (logs/'module-results.json').write_text(json.dumps({'counts':counts,'modules':results},indent=2)+'\n')
    print('BFSS_MODULE_COMPILE_SUMMARY: '+json.dumps(counts),flush=True)
    if counts['failed'] or counts['blocked']:
        raise SystemExit('BFSS_COMPLETE_CONTRIBUTION_BUILD_FAIL: source failures or blocked dependencies; axiom audit not run')

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
    wrappers=['OAI.MathematicalPhysics.BFSS.Contrib.Kotler.'+n for n in ['Concrete','Representations','LocalGeometry','GeometryAndRepresentations','PhysicalOperators','All']]
    for name in wrappers:
        source=LEAN/(name.replace('.','/')+'.lean')
        rows[name]={'imports':[line.split()[1] for line in source.read_text().splitlines() if line.startswith('import ')]}
    compile_modules(modules+wrappers,rows,lean,env,args.logs)
    audit=args.logs/'declaration-audit.log'
    run_logged([lean,'-DautoImplicit=false','-DwarningAsError=true',str((HERE/'Audit.lean').relative_to(LEAN))],audit,timeout=600,env=env)
    subprocess.run([sys.executable,str(HERE/'tools/check_bundle.py'),'--report',str(audit)],check=True)
    print('BFSS_COMPLETE_CONTRIBUTION_BUILD_PASS',flush=True)

if __name__=='__main__':main()
