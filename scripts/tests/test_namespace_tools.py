import sys
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_namespace_layout
import namespace_dependencies


class NamespaceToolsTest(unittest.TestCase):
    def test_collect_groups_root_level_challenge_and_imports(self):
        root = Path(__file__).resolve().parents[2]
        groups, edges, _ = namespace_dependencies.collect(root)
        self.assertGreaterEqual(groups['ComparatorChallenges'], 2)
        self.assertIn(('ComparatorChallenges', 'PseudoPrime.PrimeTestBounds'), edges)
        rendered = namespace_dependencies.render(root)
        self.assertIn('ComparatorChallenges (', rendered)

    def test_root_challenge_namespace_and_mismatch(self):
        root = Path(__file__).resolve().parents[2]
        path = root / 'ComparatorChallenges' / 'Example.lean'
        with patch.object(Path, 'read_text', return_value=(
                'namespace ComparatorChallenges\ndef example := 1\nend ComparatorChallenges\n')):
            _, errors = check_namespace_layout.inspect(path, root, {})
            self.assertEqual(errors, [])
        with patch.object(Path, 'read_text', return_value=(
                'namespace PseudoPrime.Challenges\ndef example := 1\nend PseudoPrime.Challenges\n')):
            _, errors = check_namespace_layout.inspect(path, root, {})
            self.assertEqual(len(errors), 1)
            self.assertEqual(errors[0]['expected'], 'ComparatorChallenges')


if __name__ == '__main__':
    unittest.main()
