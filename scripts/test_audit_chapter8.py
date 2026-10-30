#!/usr/bin/env python3
"""Test auditor safeguards without claiming synthetic reports as native acceptance."""
from contextlib import contextmanager
import copy
import importlib.util
import json
from pathlib import Path
import sys
import subprocess
import time
from unittest import mock
import tempfile
import unittest

import audit_chapter8 as audit

PREP = Path(__file__).resolve().parents[1]
import os
ROOT = Path(os.environ.get('BC4LEAN_TEST_ROOT', str(PREP)))
PROTOTYPE = PREP/'scripts/check_chapter7_retained.py'


@contextmanager
def trusted():
    name = '_audit8_python_test_retained_provider'
    spec = importlib.util.spec_from_file_location(name, PROTOTYPE)
    provider = importlib.util.module_from_spec(spec)
    assert name not in sys.modules
    sys.modules[name] = provider
    try:
        spec.loader.exec_module(provider)
        manifest = provider.load_manifest(provider.MANIFEST_PATH.read_bytes())
        sources = provider.verified_helper_sources(provider.RepositoryReader(ROOT), manifest)
        with sources.open() as helpers:
            yield helpers['audit_chapter7']
    finally:
        sys.modules.pop(name, None)


def inventory():
    return json.loads((PREP/audit.INVENTORY).read_bytes())


def blueprint(inv):
    parts = []
    for label, item in {**inv['targets'], **inv['milestones']}.items():
        kind = item['statement_kind']
        links = item['required_declarations'] if label != 'conj:baum-connes' else [audit.CONJECTURE]
        marker = r'\leanok' if item['status'] == 'implemented' else r'\notready'
        parts.append(r'\begin{' + kind + r'}\label{' + label + '}' + marker +
                     r'\lean{' + ','.join(links) + '}' + ' Synthetic parser fixture only. ' + r'\end{' + kind + '}')
        if item['status'] == 'implemented' and kind != 'definition':
            parts.append(r'\begin{proof}\leanok Synthetic parser fixture only.\end{proof}')
    return '\n'.join(parts)


class InventoryBlueprintTests(unittest.TestCase):
    def load(self, value):
        return audit.load_inventory(Path('not-read'), json.dumps(value).encode())

    def test_inventory_preserves_milestone_policy_and_exact_registered_modules(self):
        value = self.load(inventory())
        self.assertEqual(value['modules'], audit.MODULES)
        self.assertIn(value['targets']['def:baum-connes-property']['status'], {'candidate','implemented'})
        self.assertEqual(value['targets']['conj:baum-connes']['status'], 'pending')

    def test_drop_general_property_unit_endpoint_or_kind_is_rejected(self):
        for attack in ['general-status','general-proof','general-kind','property-kind','unit-drop','kind-drop','extra-module','duplicate']:
            value = inventory()
            if attack == 'general-status': value['targets']['conj:baum-connes']['status'] = 'implemented'
            elif attack == 'general-proof': value['targets']['conj:baum-connes']['required_declarations'] = [audit.CONJECTURE]
            elif attack == 'general-kind': value['required_declaration_kinds'][audit.CONJECTURE] = 'theorem'
            elif attack == 'property-kind': value['targets']['def:baum-connes-property']['statement_kind'] = 'theorem'
            elif attack == 'unit-drop': value['milestones'].pop('thm:baum-connes-unit')
            elif attack == 'kind-drop': value['required_declaration_kinds'].pop(audit.UNIT)
            elif attack == 'extra-module': value['modules'].append('BC4lean.Hidden')
            else: value['milestones']['thm:baum-connes-unit']['required_declarations'].append(audit.UNIT)
            with self.subTest(attack=attack), self.assertRaises(ValueError): self.load(value)

    def test_separate_general_definition_report_metadata_cannot_be_missing_or_relabelled_as_proof(self):
        inv=self.load(inventory())
        audit.check_statement_definition_metadata({'statement_definition_declarations':inv['statement_definition_declarations']},inv)
        for metadata in [{},{'conj:baum-connes':[]},{'conj:baum-connes':[audit.UNIT]},
                         {'conj:baum-connes':[audit.CONJECTURE,'BC4lean.Assembly.fakeGeneralProof']}]:
            record={} if not metadata else {'statement_definition_declarations':metadata}
            with self.subTest(metadata=metadata),self.assertRaisesRegex(ValueError,'Prop-definition metadata'):
                audit.check_statement_definition_metadata(record,inv)

    def test_candidates_remain_pending_and_general_definition_can_be_linked(self):
        inv = self.load(inventory())
        for item in [*inv['targets'].values(),*inv['milestones'].values()]:
            if item['status'] != 'pending': item['status']='candidate'
        with trusted() as helper:
            links, targets, milestones = audit.audit_blueprint(blueprint(inv), inv, helper)
        self.assertIn(audit.CONJECTURE, links)
        self.assertFalse(targets['conj:baum-connes']['ready'])
        self.assertFalse(any(item['ready'] for item in milestones.values()))

    def test_checked_conjecture_proof_or_missing_named_statement_rejected(self):
        inv = self.load(inventory()); source = blueprint(inv)
        attacks = [source.replace(r'\begin{conjecture}\label{conj:baum-connes}\notready',
                                  r'\begin{conjecture}\label{conj:baum-connes}\leanok'),
                   source.replace(r'\end{conjecture}', r'\end{conjecture}\begin{proof}\leanok\end{proof}'),
                   source.replace(audit.CONJECTURE, 'BC4lean.WrongDefinition'),
                   source.replace(r'\label{def:baum-connes-property}', r'\label{def:missing}'),
                   source + r'\begin{theorem}\label{thm:unregistered}\leanok\end{theorem}']
        with trusted() as helper:
            for source in attacks:
                with self.subTest(source=source[:90]), self.assertRaises(ValueError):
                    audit.audit_blueprint(source, inv, helper)

    def test_impl_parser_fixture_requires_real_endpoint_links_and_checked_attached_proof(self):
        inv = self.load(inventory())
        for item in [*inv['targets'].values(),*inv['milestones'].values()]:
            if item['status'] == 'candidate': item['status'] = 'implemented'
        source = blueprint(inv)
        with trusted() as helper:
            _, targets, milestones = audit.audit_blueprint(source, inv, helper)
            self.assertTrue(targets['def:baum-connes-property']['ready'])
            self.assertFalse(targets['conj:baum-connes']['ready'])
            self.assertTrue(all(x['ready'] for x in milestones.values()))
            with self.assertRaises(ValueError):
                audit.audit_blueprint(source.replace(r'\begin{proof}\leanok',r'\begin{proof}\notready',1),inv,helper)
        # These were in-memory parser assertions, never a native acceptance report.


class QueryKindAndSourceTests(unittest.TestCase):
    def stream(self):
        modules=['BC4lean.Test']; links=sorted(audit.REQUIRED_KINDS); endpoints=links
        lines=['CH8_START|1']
        for name in links:
            lines += ['CH8_DECL|BC4lean.Test|'+name+'|', 'CH8_KIND|'+name+'|'+audit.REQUIRED_KINDS[name]]
        for name in links: lines.append('CH8_LINK|'+name+'|BC4lean.Test|')
        lines.append('CH8_MODULE|BC4lean.Test|3')
        for name in links: lines.append('CH8_ENDPOINT|'+name+'|BC4lean.Test|')
        lines.append('CH8_END|3|3|3')
        return '\n'.join(lines),modules,links,endpoints

    def parse(self,source,modules,links,endpoints,helper):
        return audit.parse_kernel(source,modules,links,endpoints,audit.REQUIRED_KINDS,helper)

    def test_query_is_uncapped_private_aware_kind_census_and_metadata_only_budget_zero(self):
        with trusted() as helper:
            query=audit.generate_query(audit.MODULES,[audit.PROPERTY,audit.CONJECTURE,audit.UNIT],
                                       [audit.PROPERTY,audit.CONJECTURE,audit.UNIT],helper)
        self.assertIn('env.constants.toList',query)
        self.assertIn('(← Lean.getEnv).setExporting false',query)
        self.assertIn('CH8_KIND|',query)
        self.assertIn('set_option maxHeartbeats 0',query)
        self.assertNotIn('.take ',query)
        self.assertIn('New axiom declaration',query)

    def test_definitions_and_unit_theorem_kind_are_enforced_without_census_cap(self):
        source,modules,links,endpoints=self.stream()
        with trusted() as helper:
            result=self.parse(source,modules,links,endpoints,helper)
            self.assertEqual(result['declaration_kinds'][audit.UNIT],'theorem')
            for name,kind in audit.REQUIRED_KINDS.items():
                bad=source.replace('CH8_KIND|'+name+'|'+kind,'CH8_KIND|'+name+'|'+('theorem' if kind=='definition' else 'definition'))
                with self.subTest(name=name), self.assertRaises(ValueError): self.parse(bad,modules,links,endpoints,helper)

    def test_missing_duplicate_outside_frame_axiom_private_and_count_omissions_rejected(self):
        source,modules,links,endpoints=self.stream()
        kindline='CH8_KIND|'+audit.UNIT+'|theorem'
        attacks=[source.replace(kindline,''),source.replace(kindline,kindline+'\n'+kindline),
                 kindline+'\n'+source.replace(kindline,''),source.replace(kindline,'')+'\n'+kindline,
                 source.replace(kindline,kindline.replace('theorem','axiom')),
                 source.replace('CH8_MODULE|BC4lean.Test|3','CH8_MODULE|BC4lean.Test|2'),
                 source.replace('CH8_DECL|BC4lean.Test|'+audit.UNIT+'|','CH8_DECL|BC4lean.Test|'+audit.UNIT+'|sorryAx')]
        with trusted() as helper:
            for data in attacks:
                with self.subTest(data=data[-100:]),self.assertRaises((ValueError,RuntimeError)):
                    self.parse(data,modules,links,endpoints,helper)
            with self.assertRaisesRegex(RuntimeError,'Private declarations missing'):
                helper.check_private_coverage({'BC4lean.Test':'private theorem actual : True := True.intro'},result_declarations(source))

    def test_source_budgets_holes_environment_patches_and_option_weakening_rejected(self):
        with trusted() as helper:
            audit.check_sources('set_option autoImplicit false\ntheorem x : True := True.intro','test',helper)
            for text in ['axiom x : False','example : True := sorry','set_option maxHeartbeats 0',
                         'set_option maxHeartbeats 400000','set_option maxRecDepth 10000',
                         'set_option autoImplicit true','run_cmd pure ()','local notation "x" => 1']:
                with self.subTest(text=text),self.assertRaises((ValueError,RuntimeError)):
                    audit.check_sources(text,'test',helper)


def result_declarations(_):
    return [{'module':'BC4lean.Test','name':'BC4lean.public'}]


class EvidenceRejectionTests(unittest.TestCase):
    def test_four_exact_recorded_commands_and_reject_weak_or_unrelated_variants(self):
        origin='/original/source';output=Path('/canonical/evidence/audit.json');digest='a'*64
        lean=['lake','env','lean','-j1','-DwarningAsError=true','-DautoImplicit=false','-DrelaxedAutoImplicit=false']
        commands={
            'retained-preservation':['python3','-B',origin+'/'+audit.RETAINED,'--root',origin,'--new-inventory',audit.INVENTORY,'--output','/outside/receipt.json'],
            'build-gate':['lake','--wfail','--no-build','--no-cache','build','BC4lean'],
            'expected-types':lean+[origin+'/'+audit.FIXTURE],
            'kernel':lean+[str(output.with_suffix('.lean'))],
        }
        for stage,command in commands.items():
            audit.strict_recorded_command(stage,command,origin,output,digest,{'query_sha256':digest,'query_source_location':str(output.with_suffix('.lean'))})
            for change in ['option-drop','wrong-target','extra-argument']:
                changed=list(command)
                if change=='option-drop':changed.pop(1)
                elif change=='wrong-target':changed[-1]='unrelated'
                else:changed.append('--extra')
                with self.subTest(stage=stage,change=change),self.assertRaises(ValueError):
                    audit.strict_recorded_command(stage,changed,origin,output,digest,{'query_sha256':digest,'query_source_location':str(output.with_suffix('.lean'))})
        with self.assertRaises(ValueError):
            audit.strict_recorded_command('kernel',commands['kernel'],origin,output,digest,{'query_sha256':'b'*64,'query_source_location':str(output.with_suffix('.lean'))})
        unrelated=list(commands['kernel']);unrelated[-1]='/unrelated/directory/audit.lean'
        with self.assertRaisesRegex(ValueError,'weakened or unrelated'):
            audit.strict_recorded_command('kernel',unrelated,origin,output,digest,{'query_sha256':digest,'query_source_location':str(output.with_suffix('.lean'))})
        wrong=list(commands['retained-preservation']);wrong[-1]=origin+'/self/receipt.json'
        with self.assertRaises(ValueError):audit.strict_recorded_command('retained-preservation',wrong,origin,output,digest,{})

    def test_independent_fixture_binding_retains_closed_unit_and_actual_canonical_maps(self):
        fixture=(PREP/audit.FIXTURE).read_bytes()
        self.assertEqual(audit.sha(fixture),audit.EXPECTED_TYPES_SHA)
        source=fixture.decode()
        self.assertIn('Function.Bijective (Assembly.reducedAssemblyHom',source)
        self.assertIn('BaumConnesConjecture',source)
        self.assertIn('baumConnesProperty_unit',source)
        with trusted() as helper:
            self.assertNotIn('#check',helper.code_only(source))
            audit.validate_fixture(fixture,inventory(),helper)
            bad=inventory();bad['expected_type_endpoints']=bad['expected_type_endpoints'][:-1]
            with self.assertRaisesRegex(ValueError,'retain all independently typed'):
                audit.validate_fixture(fixture,bad,helper)
            with self.assertRaisesRegex(ValueError,'reviewed binding'):
                audit.validate_fixture(fixture.replace(b'Bijective',b'Injective'),inventory(),helper)

    def test_partial_failed_generated_or_general_complete_evidence_rejected_before_provider_import(self):
        for status in ['generated_only','verification_failed','verified_partial_metadata']:
            with tempfile.TemporaryDirectory(prefix='chapter8-audit-negative-') as directory:
                path=Path(directory)/'audit.json'
                path.write_text(json.dumps({'status':status,'chapter_complete':False,'general_conjecture_proved':False}))
                with self.subTest(status=status),self.assertRaisesRegex(ValueError,'No actual verified'):
                    audit.load_verified_audit(Path(directory),path,'a'*40)

    def test_malformed_json_duplicate_unsafe_paths_and_wrong_receipt_are_rejected(self):
        with self.assertRaisesRegex(ValueError,'Duplicate JSON'):
            audit.obj(b'{"a":1,"a":2}','fixture')
        for path in ['../bad','/bad','a//b','a\\b','a\nb']:
            with self.subTest(path=path),self.assertRaises(ValueError):audit.safe(path)
        for receipt in [{},{'status':'passed'},{'chapter8_complete':True}]:
            with self.subTest(receipt=receipt),self.assertRaises(ValueError):
                audit.check_retained_receipt(receipt,audit.MODULES)

    def test_build_failure_or_missing_real_runs_rejected_without_writing_success(self):
        with trusted() as helper:
            for build in [{},{'status':'passed','runs':[]},{'status':'failed'}]:
                with self.subTest(build=build),self.assertRaises(ValueError):
                    audit.build_replay(ROOT,build,b'',inventory(),{},helper)

    def test_compiler_mutex_exclusion_release_and_unknown_owner_preservation(self):
        with tempfile.TemporaryDirectory(prefix='chapter8-mutex-python-') as directory:
            root=Path(directory); lock=root/'compiler.lock'; output=root/'unused.json'; run_id='a'*32
            with audit.compiler_lock(root,output,run_id,lock) as lease:
                owner=json.loads((lock/'owner.json').read_bytes())
                self.assertEqual(owner['pid'],os.getpid()); self.assertEqual(owner['phase'],'audit-prerequisites')
                with self.assertRaisesRegex(ValueError,'occupied'):
                    with audit.compiler_lock(root,output,'b'*32,lock): self.fail('mutex bypass')
                lease.phase('fixture-phase')
                self.assertEqual(json.loads((lock/'owner.json').read_bytes())['phase'],'fixture-phase')
            self.assertFalse(lock.exists())
            with self.assertRaisesRegex(RuntimeError,'isolated exception'):
                with audit.compiler_lock(root,output,run_id,lock): raise RuntimeError('isolated exception')
            self.assertFalse(lock.exists())
            with audit.compiler_lock(root,output,run_id,lock):
                (lock/'owner.json').write_text(json.dumps({'unknown':'preserve'}))
            self.assertTrue(lock.exists())
            self.assertEqual(json.loads((lock/'owner.json').read_bytes()),{'unknown':'preserve'})

    def test_actual_failed_python_child_retains_real_durable_record_without_native(self):
        with tempfile.TemporaryDirectory(prefix='chapter8-failed-python-') as directory:
            root=Path(directory); output=root/'not-an-audit.json'; run_id='c'*32
            with audit.compiler_lock(root,output,run_id,root/'test.lock') as lease:
                with self.assertRaisesRegex(ValueError,'subprocess failed'):
                    audit.run_process(root,[sys.executable,'-B','-c','print("actual Python failure fixture"); raise SystemExit(7)'],
                                      output,'python-failure-test',lease,run_id)
            record=json.loads(audit.sidecar(output,'python-failure-test-run.json').read_bytes())
            raw=audit.sidecar(output,'python-failure-test.log').read_bytes()
            self.assertEqual(record['status'],'completed');self.assertEqual(record['exit_code'],7)
            self.assertEqual(record['stdout_stderr_sha256'],audit.sha(raw));self.assertIn(b'actual Python failure fixture',raw)
            self.assertGreaterEqual(record['finished_utc'],record['started_utc'])
            self.assertFalse(output.exists())

    def test_generation_cannot_be_combined_with_native_milestone_acceptance(self):
        result=subprocess.run([sys.executable,'-B',str(PREP/'scripts/audit_chapter8.py'),
                               '--generate-only','--require-milestone'],capture_output=True)
        self.assertEqual(result.returncode,2)
        self.assertIn(b'not allowed with argument',result.stderr)

    def test_failed_preflight_invalidates_old_passing_output(self):
        with tempfile.TemporaryDirectory(prefix='chapter8-stale-python-') as directory:
            root=Path(directory); output=root/audit.DIRECTORY/'audit.json';output.parent.mkdir(parents=True)
            output.write_text(json.dumps({'status':'verified_milestone','milestone_verified':True}))
            result=subprocess.run([sys.executable,'-B',str(PREP/'scripts/audit_chapter8.py'),
                                   '--root',str(root),'--output',str(output),'--generate-only'],capture_output=True)
            self.assertEqual(result.returncode,1)
            retained=json.loads(output.read_bytes())
            self.assertEqual(retained['status'],'verification_not_started')
            self.assertFalse(retained['milestone_verified']);self.assertFalse(retained['general_conjecture_proved'])

    def test_protected_repository_outputs_are_rejected_before_any_write(self):
        with tempfile.TemporaryDirectory(prefix='chapter8-protected-output-') as directory:
            root=Path(directory)
            sentinels=['docs/audits/chapter7/audit.json','docs/audits/chapter8/ExpectedTypes.json',
                       'BC4lean/proof.json','.git/objects/protected.json','arbitrary.json']
            for relative in sentinels:
                path=root/relative;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(b'protected sentinel')
            before={p.relative_to(root).as_posix():p.read_bytes() for p in root.rglob('*') if p.is_file()}
            for relative in sentinels:
                result=subprocess.run([sys.executable,'-B',str(PREP/'scripts/audit_chapter8.py'),
                                       '--root',str(root),'--output',str(root/relative),'--generate-only'],capture_output=True)
                self.assertEqual(result.returncode,1)
                self.assertIn(b'Repository audit output is restricted',result.stderr)
            after={p.relative_to(root).as_posix():p.read_bytes() for p in root.rglob('*') if p.is_file()}
            self.assertEqual(before,after)

    def test_outside_output_scope_canonical_root_and_symlink_sidecars(self):
        with tempfile.TemporaryDirectory(prefix='chapter8-output-scope-') as directory:
            base=Path(directory).resolve();root=base/'repo';root.mkdir();outside=base/'outside/audit.json'
            self.assertEqual(audit.validate_output_scope(root,outside),outside)
            self.assertFalse(outside.parent.exists())
            canonical=root/audit.DIRECTORY/'audit.json'
            self.assertEqual(audit.validate_output_scope(root,canonical),canonical)
            canonical.parent.mkdir(parents=True)
            sentinel=base/'sentinel.lean';sentinel.write_bytes(b'protected')
            canonical.with_suffix('.lean').symlink_to(sentinel)
            with self.assertRaisesRegex(ValueError,'symlink'):
                audit.validate_output_scope(root,canonical)
            self.assertEqual(sentinel.read_bytes(),b'protected')
            link=base/'linked.json';link.symlink_to(root/'old.json')
            with self.assertRaisesRegex(ValueError,'symlink'):audit.validate_output_scope(root,link)

    def test_owned_parent_descendant_interruption_stops_heartbeat_before_mutex_release(self):
        # A real harmless parent/grandchild pair; both have bounded natural TTL.
        with tempfile.TemporaryDirectory(prefix='chapter8-owned-group-') as directory:
            root=Path(directory);heartbeat=root/'heartbeat';output=root/'failed-python-only.json';lock=root/'test.lock'
            grandchild='import pathlib,time; p=pathlib.Path('+repr(str(heartbeat))+'); end=time.monotonic()+4;\nwhile time.monotonic()<end:\n with p.open("a") as h: h.write("beat\\n"); h.flush()\n time.sleep(0.03)'
            parent='import subprocess,sys,time; subprocess.Popen([sys.executable,"-B","-c",'+repr(grandchild)+']); time.sleep(5)'
            real_popen=subprocess.Popen
            class InterruptOnce(real_popen):
                interrupted=False
                def wait(self,timeout=None):
                    if not self.interrupted:
                        deadline=time.monotonic()+2
                        while not heartbeat.exists() and time.monotonic()<deadline:time.sleep(0.01)
                        self.interrupted=True
                        if not heartbeat.exists():raise RuntimeError('owned child did not start heartbeat')
                        raise KeyboardInterrupt('isolated real owned-child interruption')
                    return super().wait(timeout=timeout)
            with self.assertRaises(KeyboardInterrupt):
                with audit.compiler_lock(root,output,'d'*32,lock) as lease:
                    with mock.patch.object(audit.subprocess,'Popen',InterruptOnce):
                        audit.run_process(root,[sys.executable,'-B','-c',parent],output,'owned-python-interruption',lease,'d'*32)
            before=heartbeat.read_bytes();time.sleep(0.15);self.assertEqual(heartbeat.read_bytes(),before)
            record=json.loads(audit.sidecar(output,'owned-python-interruption-run.json').read_bytes())
            self.assertEqual(record['status'],'interrupted')
            if lock.exists():
                self.assertFalse(record['owned_process_group_quiescent'])
                self.assertIn('cleanup-unconfirmed',json.loads((lock/'owner.json').read_bytes())['phase'])
            else:self.assertTrue(record['owned_process_group_quiescent'])

    def test_uncertain_owned_group_cleanup_retains_mutex_and_rejects_completion(self):
        with tempfile.TemporaryDirectory(prefix='chapter8-uncertain-group-') as directory:
            root=Path(directory);output=root/'failed-python-only.json';lock=root/'test.lock'
            with self.assertRaisesRegex(ValueError,'active owned descendants'):
                with audit.compiler_lock(root,output,'e'*32,lock) as lease:
                    # Simulate inability to establish quiescence after an actual
                    # harmless child exits; no native process is launched.
                    with mock.patch.object(audit,'owned_group_exists',return_value=True):
                        audit.run_process(root,[sys.executable,'-B','-c','pass'],output,'uncertain-python',lease,'e'*32)
            self.assertTrue(lock.exists())
            record=json.loads(audit.sidecar(output,'uncertain-python-run.json').read_bytes())
            self.assertFalse(record['owned_process_group_quiescent']);self.assertEqual(record['status'],'interrupted')

    def test_unknown_constructor_interruption_retains_mutex_without_guessing_child_absence(self):
        with tempfile.TemporaryDirectory(prefix='chapter8-unknown-spawn-') as directory:
            root=Path(directory);output=root/'failed-python-only.json';lock=root/'test.lock'
            with self.assertRaises(KeyboardInterrupt):
                with audit.compiler_lock(root,output,'f'*32,lock) as lease:
                    # Inject the constructor boundary interruption; no child is
                    # launched by this component test and no PID is invented.
                    with mock.patch.object(audit.subprocess,'Popen',side_effect=KeyboardInterrupt('constructor boundary')):
                        audit.run_process(root,[sys.executable,'-B','-c','pass'],output,'unknown-python-spawn',lease,'f'*32)
            self.assertTrue(lock.exists())
            owner=json.loads((lock/'owner.json').read_bytes())
            self.assertIn('cleanup-unconfirmed',owner['phase']);self.assertIsNone(owner['child_pid'])
            record=json.loads(audit.sidecar(output,'unknown-python-spawn-run.json').read_bytes())
            self.assertEqual(record['status'],'interrupted');self.assertFalse(record['owned_process_group_quiescent'])
            self.assertNotIn('pid',record)

    def test_historical_output_location_replays_portably_without_accepting_protected_or_aliased_paths(self):
        origin='/original/mac/source'
        for output in ['/original/task/evidence/audit.json',origin+'/'+audit.DIRECTORY+'/audit.json']:
            metadata={'source_root_provenance':origin,'audit_output_provenance':output,
                      'query_source_location':str(Path(output).with_suffix('.lean'))}
            self.assertEqual(audit.recorded_locations(metadata),(origin,Path(output)))
        for output in [origin+'/docs/audits/chapter7/audit.json',origin+'/BC4lean/proof.json',
                       '/original/task/../aliased/audit.json']:
            metadata={'source_root_provenance':origin,'audit_output_provenance':output,
                      'query_source_location':str(Path(output).with_suffix('.lean'))}
            with self.subTest(output=output),self.assertRaises(ValueError):audit.recorded_locations(metadata)
        metadata={'source_root_provenance':origin,'audit_output_provenance':'/outside/audit.json',
                  'query_source_location':'/unrelated/audit.lean'}
        with self.assertRaises(ValueError):audit.recorded_locations(metadata)

    def test_process_provenance_missing_started_running_reuse_and_clock_reversal_rejected(self):
        # In-memory record component assertions only; never written as an audit.
        record={'schema':'chapter8.actual.process.v1','status':'completed','stage':'kernel','run_id':'a'*32,
                'source_root':'/original','pid':1,'parent_pid':2,'exit_code':0,'process_group':1,'owned_process_group_quiescent':True,
                'started_utc':'2026-10-19T00:00:00+00:00','finished_utc':'2026-10-19T00:00:01+00:00'}
        audit.validate_process_record(record,'kernel','a'*32,'/original')
        for key,value in [('status','starting'),('status','running'),('status','interrupted'),('run_id','b'*32),
                          ('source_root','/forged'),('pid',False),('parent_pid',0),('exit_code',False),
                          ('process_group',3),('owned_process_group_quiescent',False),
                          ('finished_utc','2026-10-18T00:00:00+00:00'),('started_utc','2026-10-19T00:00:00')]:
            bad={**record,key:value}
            with self.subTest(key=key,value=value),self.assertRaises(ValueError):
                audit.validate_process_record(bad,'kernel','a'*32,'/original')

    def test_build_raw_replay_rejects_omitted_old_source_log_and_order_forgery(self):
        # In-memory structural test data only. This does not create a passing
        # native report: no build.json/log is written, no native process runs,
        # and the temporary baseline would fail the real pinned-manifest gate.
        baseline=json.loads((PREP/'docs/audits/chapter8/Chapter7Baseline.json').read_bytes())
        inv=inventory();modules=inv['modules']
        with tempfile.TemporaryDirectory(prefix='chapter8-build-parser-') as directory:
            root=Path(directory)
            target=root/audit.BASELINE;target.parent.mkdir(parents=True);target.write_text(json.dumps(baseline))
            hashes={path:'a'*64 for path in baseline['proof_sources']}
            for module in modules:
                path=module.replace('.','/')+'.lean';file=root/path;file.parent.mkdir(parents=True,exist_ok=True)
                file.write_text('-- Isolated Python parser fixture; not a compiled proof.\n');hashes[path]=audit.sha(file.read_bytes())
            controls={audit.INVENTORY,audit.IMPORTS,'BC4lean.lean','scripts/audit_chapter6.py','lean-toolchain','lakefile.toml','lake-manifest.json'}
            hashes.update({path:'b'*64 for path in controls})
            runs=[];raw=b''
            for module in modules+['BC4lean']:
                command=['lake','--wfail','--no-cache','build',module];segment=b'synthetic parser data only\n'
                raw+=('COMMAND '+json.dumps(command)+'\n').encode()+segment
                runs.append({'command':command,'exit_code':0,'stdout_stderr_sha256':audit.sha(segment),
                             'started_utc':'2026-10-19T00:00:00+00:00','finished_utc':'2026-10-19T00:00:00+00:00'})
            queue=audit.sha((json.dumps(modules,indent=2)+'\n').encode())
            build={'status':'passed','sources_unchanged_during_build':True,'sequential_leaf_builds':True,
                   'environment':{'LEAN_NUM_THREADS':'1'},'combined_log_sha256':audit.sha(raw),'runs':runs,
                   'all_input_sha256':dict(hashes),'source_sha256':{m:hashes[m.replace('.','/')+'.lean'] for m in modules},
                   'order_validation':{'status':'verified_actual_source_order_only','library_module_count':930+len(modules),'module_count':len(modules),
                       'order_sha256':queue,'inventory_sha256':hashes[audit.INVENTORY],'aggregate_sha256':hashes['BC4lean.lean'],
                       'frozen_prefix_sha256':audit.PREFIX7_SHA,'parser_sha256':hashes['scripts/audit_chapter6.py'],
                       'generated_order_sha256':queue,'internal_dependency_edges':0,'provided_order_path':None}}
            with trusted() as helper:
                audit.build_replay(root,build,raw,inv,hashes,helper)
                for attack in ['old-source-drop','new-source-hash','extra-input','run-count','run-exit','segment','order','generated-order','parser-hash','time-reversal','duplicate-target']:
                    candidate=copy.deepcopy(build);candidate_raw=raw
                    if attack=='old-source-drop':candidate['all_input_sha256'].pop(next(iter(baseline['proof_sources'])))
                    elif attack=='new-source-hash':candidate['source_sha256'][modules[0]]='0'*64
                    elif attack=='extra-input':candidate['all_input_sha256']['unregistered']='0'*64
                    elif attack=='run-count':candidate['runs'].pop()
                    elif attack=='run-exit':candidate['runs'][0]['exit_code']=False
                    elif attack=='segment':
                        candidate_raw=raw.replace(b'synthetic parser data only',b'forged parser data only',1)
                        candidate['combined_log_sha256']=audit.sha(candidate_raw)
                    elif attack=='order':candidate['order_validation']['order_sha256']='0'*64
                    elif attack=='generated-order':candidate['order_validation']['generated_order_sha256']='0'*64
                    elif attack=='parser-hash':candidate['order_validation']['parser_sha256']='0'*64
                    elif attack=='time-reversal':candidate['runs'][0]['finished_utc']='2026-10-18T00:00:00+00:00'
                    else:candidate['runs'][1]['command'][-1]=modules[0]
                    with self.subTest(attack=attack),self.assertRaises(ValueError):
                        audit.build_replay(root,candidate,candidate_raw,inv,hashes,helper)


if __name__=='__main__':unittest.main(verbosity=2)
