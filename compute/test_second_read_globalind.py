import contextlib
import io
import unittest

import second_read_globalind as s


class TestSecondReadGlobalind(unittest.TestCase):
    def test_poset_counts(self):
        self.assertEqual([len(s.posets(n)) for n in range(1, 6)], [1, 3, 19, 219, 4231])

    def test_identity_and_controls(self):
        with contextlib.redirect_stdout(io.StringIO()):
            for n in range(2, 5):
                self.assertTrue(s.check(n))


if __name__ == "__main__":
    unittest.main()
