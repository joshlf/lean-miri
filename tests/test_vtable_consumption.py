"""Diagnostic joins distinguish finite source material from runtime consumption."""
import importlib.util
import json
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location('vtable_erasure',
    Path(__file__).resolve().parents[1] / 'tools/check-vtable-erasure.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ConsumptionTests(unittest.TestCase):
    def setUp(self):
        # Synthetic parser controls only; never a genuine nonidentity witness.
        self.document = {
            'producer': {'rustc_commit': 'unit-test'},
            'types': [{'source_layout': {'normalized_type': 0}}],
            'compiler_predicate_queries': [
                {'predicate_id': 0, 'erased': 1}, {'predicate_id': 1, 'erased': 1}],
        }
        self.mapping = 'vtable_source_map input_type=0 input_predicates=#[0] output_type=0 output_predicates=#[1]\n'
        self.runtime = 'vtable_query input_type=0 input_predicates=#[0] output_type=0 output_predicates=#[1]\n'

    def summarize(self, runtime):
        return MODULE.summarize_queries(json.dumps(self.document).encode(), self.mapping, runtime)

    def test_material_nonidentity_is_not_runtime_coverage(self):
        result = self.summarize('')
        self.assertEqual(result['nonidentity_source_keys'], 1)
        self.assertEqual(result['runtime_nonidentity_calls'], 0)

    def test_summary_identifies_exact_source_bytes(self):
        result = self.summarize(self.runtime)
        raw = json.dumps(self.document).encode()
        self.assertEqual(result['snapshot_fnv1a64'], MODULE.fingerprint(raw))
        self.assertEqual(result['snapshot_byte_length'], len(raw))

    def test_counts_actual_repeated_lookup(self):
        self.assertEqual(self.summarize(self.runtime * 2)['runtime_nonidentity_calls'], 2)

    def test_rejects_wrong_complete_pair(self):
        with self.assertRaisesRegex(ValueError, 'exact source key'):
            self.summarize(self.runtime.replace('output_predicates=#[1]', 'output_predicates=#[0]'))

    def test_rejects_missing_key(self):
        with self.assertRaisesRegex(ValueError, 'incomplete exact source query trace'):
            self.summarize(self.runtime.replace('input_predicates=#[0] ', ''))

    def test_rejects_duplicate_mapping(self):
        self.mapping *= 2
        with self.assertRaisesRegex(ValueError, 'duplicate source key'):
            self.summarize(self.runtime)

    def test_rejects_incorrect_identity_mapping(self):
        self.mapping = self.mapping.replace('output_predicates=#[1]', 'output_predicates=#[0]')
        with self.assertRaisesRegex(ValueError, 'exact source key'):
            self.summarize(self.runtime)

    def test_rejects_absent_source_material(self):
        with self.assertRaisesRegex(ValueError, 'no predicate source material'):
            self.summarize(self.runtime.replace('input_predicates=#[0]', 'input_predicates=#[9]'))


class ExternalConstantTests(unittest.TestCase):
    def setUp(self):
        self.document = {'body_roots': [{'def_path': 'miri_start', 'body': 0}],
                         'bodies': [{'basic_blocks': [{'constant': {
                             'kind': 'evaluated_const', 'value': {
                                 'kind': 'indirect_allocation', 'allocation': 10}}}]}],
                         'allocations': [{'allocation_id': 10, 'relocations': [{'target': 20}]},
                                         {'allocation_id': 20, 'kind': 'vtable'}]}
        self.mir = 'fn miri_start() {\n _1 = const dependency::OBJECT;\n}'

    def test_resolved_constant_with_independent_compiler_origin(self):
        MODULE.require_external_constant(self.document, 'dependency::OBJECT', self.mir)

    def test_rejects_unrelated_external_constant(self):
        with self.assertRaisesRegex(SystemExit, 'lacks external constant'):
            MODULE.require_external_constant(self.document, 'dependency::OTHER', self.mir)

    def test_rejects_ambiguous_external_origins(self):
        with self.assertRaisesRegex(SystemExit, 'ambiguous external constant'):
            MODULE.require_external_constant(self.document, 'dependency::OBJECT',
                self.mir.replace('\n}', '\n _2 = const other::OBJECT;\n}'))

    def test_rejects_local_unsize_control(self):
        with self.assertRaisesRegex(SystemExit, 'local vtable'):
            MODULE.require_external_constant(self.document, 'dependency::OBJECT',
                                             self.mir.replace('\n}', '\n PointerCoercion(Unsize)\n}'))

    def test_rejects_missing_symbolic_relocation(self):
        self.document['allocations'][1]['kind'] = 'memory'
        with self.assertRaisesRegex(SystemExit, 'missing external constant'):
            MODULE.require_external_constant(self.document, 'dependency::OBJECT', self.mir)


if __name__ == '__main__':
    unittest.main()
