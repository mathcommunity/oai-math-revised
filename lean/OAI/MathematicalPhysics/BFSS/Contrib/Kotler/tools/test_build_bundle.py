"""Runner control-flow fixtures using a fake compiler, not Lean proof evidence."""
from pathlib import Path
import contextlib,io,json,os,sys,tempfile,unittest
from unittest.mock import patch
import build_bundle as build

class BuildFailurePropagation(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name);self.logs=self.root/'logs';self.logs.mkdir()
        self.fake=self.root/'fake-lean'
        self.fake.write_text('#!'+sys.executable+'\n'+'''
from pathlib import Path
import os,sys,time
expected='-DwarningAsError=false' if os.environ.get('FIXTURE_DIAGNOSTICS') else '-DwarningAsError=true'
assert '-DautoImplicit=false' in sys.argv and expected in sys.argv
source=Path(sys.argv[-1]);mode=source.read_text()
with Path('invocations.log').open('a') as out:out.write(source.name+'\\n')
target=Path(sys.argv[sys.argv.index('-o')+1]);target.parent.mkdir(parents=True,exist_ok=True)
if mode=='NO_OUTPUT':raise SystemExit(0)
target.write_text('fresh '+source.name)
for suffix in ['.private','.server']:Path(str(target)+suffix).write_text('fresh')
if mode=='FAIL':
 print('error: expected fixture diagnostic',flush=True)
 raise SystemExit(7)
if mode=='TIMEOUT':time.sleep(5)
if mode=='WARN':
 print('warning: expected fixture diagnostic',flush=True)
 if expected=='-DwarningAsError=true':raise SystemExit(7)
''')
        self.fake.chmod(0o755)
        self.rows={'A':{'imports':[]},'B':{'imports':['A']},'C':{'imports':[]}}
        for name in self.rows:
            (self.root/(name+'.lean')).write_text('OK')
            target=self.root/'.lake/build/lib/lean'/(name+'.olean')
            target.parent.mkdir(parents=True,exist_ok=True)
            for suffix in ['','.private','.server']:Path(str(target)+suffix).write_text('stale')

    def run_graph(self,*,timeout=5,diagnose_warnings=False):
        with patch.object(build,'LEAN',self.root),contextlib.redirect_stdout(io.StringIO()):
            env=dict(os.environ)
            if diagnose_warnings:env['FIXTURE_DIAGNOSTICS']='1'
            build.compile_modules(list(self.rows),self.rows,str(self.fake),env,self.logs,timeout=timeout,diagnose_warnings=diagnose_warnings)

    def check_rejection(self,mode,*,timeout=5,diagnose_warnings=False):
        (self.root/'A.lean').write_text(mode)
        with self.assertRaises(SystemExit):self.run_graph(timeout=timeout,diagnose_warnings=diagnose_warnings)
        result=json.loads((self.logs/'module-results.json').read_text())
        expected={'passed':1,'failed':1,'blocked':1}
        if diagnose_warnings:expected['warning']=0
        self.assertEqual(result['counts'],expected)
        self.assertEqual([r['status'] for r in result['modules']],['failed','blocked','passed'])
        self.assertEqual((self.root/'invocations.log').read_text().splitlines(),['A.lean','C.lean'])
        for name in ['A','B']:
            for suffix in ['','.private','.server']:
                self.assertFalse((self.root/'.lake/build/lib/lean'/(name+'.olean'+suffix)).exists())
        self.assertEqual((self.root/'.lake/build/lib/lean/C.olean').read_text(),'fresh C.lean')

    def test_failed_recovery_objects_cannot_reach_dependants(self):self.check_rejection('FAIL')
    def test_missing_fresh_output_is_failure(self):self.check_rejection('NO_OUTPUT')
    def test_timeout_blocks_dependants(self):self.check_rejection('TIMEOUT',timeout=0.5)
    def test_strict_warning_rejects_and_blocks(self):self.check_rejection('WARN')
    def test_diagnostic_hard_error_still_blocks(self):self.check_rejection('FAIL',diagnose_warnings=True)
    def test_diagnostic_warning_allows_inspection_but_rejects_result(self):
        (self.root/'A.lean').write_text('WARN')
        with self.assertRaises(SystemExit):self.run_graph(diagnose_warnings=True)
        result=json.loads((self.logs/'module-results.json').read_text())
        self.assertEqual(result['mode'],'warning-diagnostics')
        self.assertEqual(result['counts'],{'passed':2,'failed':0,'blocked':0,'warning':1})
        self.assertEqual((self.root/'invocations.log').read_text().splitlines(),['A.lean','B.lean','C.lean'])
    def test_all_modules_must_pass(self):
        self.run_graph()
        result=json.loads((self.logs/'module-results.json').read_text())
        self.assertEqual(result['counts'],{'passed':3,'failed':0,'blocked':0})
        self.assertEqual((self.root/'invocations.log').read_text().splitlines(),['A.lean','B.lean','C.lean'])

if __name__=='__main__':unittest.main()
