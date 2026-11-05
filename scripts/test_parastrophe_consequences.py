"""The compiled conversion export must feed both graph builders with provenance."""
import json
import tempfile
import unittest
from pathlib import Path

import parastrophe_consequences as pc
from generate_research_site import Export, KEYS


class ConsequenceTests(unittest.TestCase):
    def sample(self):
        ref = dict(name='Proof.image', file='equational_theories/Parastrophes/Exact.lean',
                   line=1, status='PROVED')
        fact = dict(name='Generated.forward', source=14, target=29, kind='termStructural',
                    scope='fin', side='left', refs=[ref['name']])
        return dict(version=2, consequences=[fact, dict(fact, kind='fineSpectrum')],
                    consequenceSources=[ref])

    def load(self, data):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'parastrophes.json'
            path.write_text(json.dumps(data))
            return pc.load(path)

    def test_native_arrow_and_source_links(self):
        data = self.load(self.sample())
        exporter = Export([])
        exporter.parastrophes(data)
        self.assertEqual(len(exporter.positive), 1)
        fact = exporter.positive[0]
        self.assertEqual((KEYS[fact['key']], fact['s'], fact['t']),
                         ('termStructural-fin', [14], [29]))
        self.assertEqual(fact['parastrophe'], 'left')
        self.assertEqual(fact['generatedTheorem'], 'Generated.forward')
        self.assertEqual(exporter.sources[fact['refs'][0]]['name'], 'Proof.image')
        # Fine-spectrum equality is separate data, not an extra implication edge.
        self.assertEqual(len(pc.arrows(data)), 1)

    def test_unproved_or_missing_premise_rejected(self):
        for status in ['PROOF_AVAILABLE', 'UNVERIFIED']:
            data = self.sample()
            data['consequenceSources'][0]['status'] = status
            with self.assertRaisesRegex(ValueError, 'unproved'):
                self.load(data)
        data = self.sample()
        data['consequenceSources'] = []
        with self.assertRaisesRegex(ValueError, 'Missing'):
            self.load(data)

    def test_old_export_cannot_silently_drop_new_arrows(self):
        with self.assertRaisesRegex(ValueError, 'Regenerate'):
            self.load(dict(version=2, records=[]))

    def test_unknown_relation_and_bad_scope_rejected(self):
        for field, value in [('scope', 'maybe'), ('kind', 'implies'), ('target', 4695)]:
            data = self.sample()
            data['consequences'][0][field] = value
            with self.assertRaises(ValueError):
                self.load(data)


if __name__ == '__main__':
    unittest.main()
