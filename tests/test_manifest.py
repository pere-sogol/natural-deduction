"""The browser loads what web/manifest.json lists, and nothing else.

A module missing from the manifest is invisible until the page is opened,
where it shows up as an import error behind a blank screen.  Cheaper to
find here.
"""

import json
import os
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def manifest():
    with open(os.path.join(ROOT, "web", "manifest.json")) as handle:
        return json.load(handle)


class TestManifest(unittest.TestCase):
    def test_it_lists_every_module_the_editor_needs(self):
        listed = manifest()
        found = []
        for package in ("nd", "ndweb"):
            for name in sorted(os.listdir(os.path.join(ROOT, package))):
                if name.endswith(".py"):
                    found.append("{0}/{1}".format(package, name))
        self.assertEqual(sorted(listed), sorted(found))

    def test_every_listed_file_is_there(self):
        listed = manifest()
        for path in listed:
            self.assertTrue(os.path.exists(os.path.join(ROOT, path)), path)

    def test_the_entry_point_is_outside_both_packages(self):
        """As demo.py is, and for the same reason: no module imported twice."""
        self.assertTrue(os.path.exists(os.path.join(ROOT, "web", "bootstrap.py")))
        listed = manifest()
        self.assertNotIn("web/bootstrap.py", listed)
