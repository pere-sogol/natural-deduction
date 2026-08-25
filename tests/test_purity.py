"""The editor never builds a proof except through apply().

This is the property that lets ndweb.refine be a heuristic.  If a module
reached for ``AndIntro`` directly it could construct a proof by a route
the engine had not checked, and the guarantee would be gone.  A comment
would not survive; a test does.
"""

import importlib
import pkgutil
import unittest

import nd.rules
import ndweb


class TestSoundness(unittest.TestCase):
    def test_no_rule_class_is_reachable_from_the_editor(self):
        forbidden = set(nd.rules.__all__)
        for info in pkgutil.iter_modules(ndweb.__path__):
            module = importlib.import_module("ndweb." + info.name)
            leaked = sorted(forbidden & set(vars(module)))
            self.assertEqual(
                leaked, [],
                "ndweb.{0} imports {1} -- build proofs through apply() only"
                .format(info.name, ", ".join(leaked)),
            )

    def test_the_editor_does_reach_the_engine_the_proper_way(self):
        """The guard above must not pass merely because nothing is imported."""
        from ndweb import attempt

        self.assertTrue(hasattr(attempt, "apply"))
