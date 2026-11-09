"""Inventory/report rejection fixtures; these do not establish Lean proofs."""
from pathlib import Path
import contextlib,io,json,tempfile,unittest
from unittest.mock import patch
import check_bundle as check


class DeclarationChecks(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name);self.here=self.root/'package';self.here.mkdir()
        self.source=self.here/'Fixture.lean'
        self.tokens=['vector_ι',"paired₂'",'gauge_ι_mul']
        self.source.write_text('namespace Fixture\n'+'\n'.join(
            'theorem '+name+' : True := by trivial' for name in self.tokens)+'\nend Fixture\n')
        self.rows=[{'name':'Fixture.'+name,'kind':'theorem','module':'Fixture',
            'path':'package/Fixture.lean','line':i+2} for i,name in enumerate(self.tokens)]
        self.data={'modules':[{'module':'Fixture','path':'package/Fixture.lean'}]}
        self.write_inventory()

    def write_inventory(self):
        (self.here/'declarations.json').write_text(json.dumps({'declarations':self.rows}))
        (self.here/'Audit.lean').write_text('\n'.join('#print axioms '+r['name'] for r in self.rows)+'\n')

    def check_index(self):
        with patch.object(check,'ROOT',self.root),patch.object(check,'HERE',self.here),contextlib.redirect_stdout(io.StringIO()):
            check.check_declarations(self.data)

    def report(self):
        lines=["'"+r['name']+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for r in self.rows]
        lines[1]="'"+self.rows[1]['name']+"' does not depend on any axioms"
        return '\n'.join(lines)+'\nBFSS_BUNDLE_DECLARATION_AUDIT_COMPLETE\n'

    def check_report(self,text):
        path=self.here/'report.log';path.write_text(text)
        with patch.object(check,'HERE',self.here),contextlib.redirect_stdout(io.StringIO()):
            check.check_report(path)

    def test_complete_unicode_source_names(self):
        self.check_index()

    def test_truncated_unicode_names_are_rejected_even_when_audit_agrees(self):
        for index,short in [(0,'vector_'),(2,'gauge_')]:
            with self.subTest(index=index):
                name=self.rows[index]['name'];self.rows[index]['name']='Fixture.'+short;self.write_inventory()
                with self.assertRaisesRegex(SystemExit,'spelling mismatch'):self.check_index()
                self.rows[index]['name']=name;self.write_inventory()

    def test_stale_source_line_is_rejected(self):
        self.rows[0]['line']=3;self.write_inventory()
        with self.assertRaisesRegex(SystemExit,'spelling mismatch'):self.check_index()

    def test_duplicate_index_is_rejected(self):
        self.rows.append(dict(self.rows[0]));self.write_inventory()
        with self.assertRaisesRegex(SystemExit,'duplicate declaration'):self.check_index()

    def test_audit_and_index_must_match(self):
        p=self.here/'Audit.lean';p.write_text(p.read_text().replace('vector_ι','vector_'))
        with self.assertRaisesRegex(SystemExit,'audit/index'):self.check_index()

    def test_permitted_complete_report_with_unicode_names(self):
        self.check_report(self.report())

    def test_forbidden_axiom_is_rejected(self):
        with self.assertRaisesRegex(SystemExit,'unpermitted axioms'):
            self.check_report(self.report().replace('Quot.sound','sorryAx',1))

    def test_missing_or_duplicated_report_is_rejected(self):
        text=self.report()
        with self.assertRaises(SystemExit):self.check_report('\n'.join(text.splitlines()[1:]))
        with self.assertRaisesRegex(SystemExit,'names mismatch'):
            self.check_report(text.replace(self.rows[0]['name'],self.rows[2]['name']))

    def test_legacy_and_coded_diagnostics_are_rejected_with_complete_reports(self):
        for severity in ['error','warning','error(lean.unknownIdentifier)','warning(lean.deprecated)']:
            with self.subTest(severity=severity),self.assertRaisesRegex(SystemExit,'Lean diagnostic'):
                self.check_report(self.report()+'Audit.lean:1:1: '+severity+': fixture diagnostic\n')

    def test_missing_completion_marker_is_rejected(self):
        with self.assertRaisesRegex(SystemExit,'completion marker'):
            self.check_report(self.report().replace('BFSS_BUNDLE_DECLARATION_AUDIT_COMPLETE',''))


if __name__=='__main__':unittest.main()
