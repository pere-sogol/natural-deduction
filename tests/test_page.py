"""The page and the scripts still agree with each other.

There is no browser automation on this machine, so anything that can only
be seen rendered is untested.  These are the checks that do not need a
browser: that every element the script reaches for exists, that every
class it queries is one the painter puts on, that every file the page
loads is there, and that every failure the checker can report has a style
saying how to show it.  All of them fail silently in a browser -- a
``null`` here, an unstyled bar there -- which is exactly why they are
worth catching from Python.
"""

import os
import re
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def read(*parts):
    with open(os.path.join(ROOT, *parts), encoding="utf-8") as handle:
        return handle.read()


class PageTestCase(unittest.TestCase):
    def setUp(self):
        self.html = read("web", "index.html")
        self.css = read("web", "style.css")
        self.app = read("web", "app.js")
        self.render = read("web", "render.js")
        self.js = self.app + self.render


class TestElements(PageTestCase):
    def test_every_element_the_script_reaches_for_is_on_the_page(self):
        wanted = set(re.findall(r'\$\("([\w-]+)"\)', self.js))
        wanted |= set(re.findall(r'getElementById\("([\w-]+)"\)', self.js))
        present = set(re.findall(r'id="([\w-]+)"', self.html))
        self.assertTrue(wanted, "the check found nothing to check")
        self.assertEqual(sorted(wanted - present), [])

    def test_every_file_the_page_loads_is_there(self):
        for path in re.findall(r'(?:src|href)="([^":]+)"', self.html):
            self.assertTrue(
                os.path.exists(os.path.join(ROOT, "web", path)), path
            )

    def test_nothing_is_fetched_from_the_browser_s_cache(self):
        """A mixed load is worse than a slow one.

        The sources are separate files fetched separately, so a browser
        free to cache them can serve some from disk and some from the
        network -- half of ``nd`` as it was last night and half as it is
        now, registering rules the rest of the code has never heard of.
        The symptom is a palette showing a rule that no longer exists.
        ``web/serve.py`` sends ``no-store``, but the page is also opened
        behind other static servers, so it must ask as well.
        """
        calls = re.findall(r"fetch\((.*?)\)", self.app)
        self.assertTrue(calls, "the check found no fetch to check")
        for call in calls:
            self.assertIn('cache: "no-store"', call, call)


class TestClasses(PageTestCase):
    def painted(self):
        """Classes the painter puts on, plus those the page ships with."""
        found = set()
        for group in re.findall(r'el\("\w+",\s*"([^"]+)"', self.render):
            found |= set(group.split())
        for group in re.findall(r'classList\.add\("([\w-]+)"\)', self.js):
            found.add(group)
        for group in re.findall(r'class="([^"]+)"', self.html):
            found |= set(group.split())
        # painted from data rather than a literal: kind, status, source
        found |= {"slot", "step", "blank", "written", "derived", "schema"}
        return found

    def test_every_class_the_script_queries_is_one_something_puts_on(self):
        queried = set()
        for pattern in (r'closest\("\.([\w-]+)', r'querySelectorAll?\("\.([\w-]+)'):
            queried |= set(re.findall(pattern, self.js))
        self.assertTrue(queried)
        self.assertEqual(sorted(queried - self.painted()), [])

    def test_the_classes_a_sentence_is_cut_into_are_all_styled(self):
        """An unclassed piece would set as upright roman and look wrong."""
        from ndweb.typeset import pieces

        seen = set()
        for text in ("∀x(Fx → ∃y Rxy)", "Loves(a_1, b) ∧ ¬P", "a=b", "φ ∨ ψ"):
            seen |= set(piece["c"] for piece in pieces(text))
        for name in sorted(seen):
            self.assertRegex(self.css, r"\.{0}\b".format(name), name)


class TestTheTracker(PageTestCase):
    """The assumption panel reads fields off the state and paints tones.

    Both go wrong silently in a browser -- ``undefined.length`` throws
    where nobody is looking, and an unstyled row is merely a row that
    looks like every other one -- so both are checked from here.
    """

    def sent(self):
        from nd.formula import reset_arities
        from ndweb.session import Session

        reset_arities()
        session = Session()
        session.dispatch({"op": "new", "goal": "Q", "premises": ["P -> Q", "P"]})
        return session.state()

    def test_every_field_the_panel_reads_is_one_python_sends(self):
        tracker = self.sent()["assumptions"]
        wanted = set(re.findall(r"tracker\.(\w+)", self.render))
        self.assertTrue(wanted, "the check found nothing to check")
        self.assertEqual(sorted(wanted - set(tracker)), [])

    def test_every_field_a_row_reads_is_one_python_sends(self):
        rows = self.sent()["assumptions"]["premises"]
        self.assertTrue(rows, "the check needs a row to check")
        wanted = set(re.findall(r"row\.(\w+)", self.render))
        self.assertTrue(wanted)
        self.assertEqual(sorted(wanted - set(rows[0])), [])

    def test_the_state_carries_the_blank_slots_the_status_counts(self):
        self.assertIn("blankSlots", self.sent())
        self.assertIn("state.blankSlots", self.app)

    def test_every_tone_a_row_is_given_is_styled(self):
        """An unstyled tone is a row that says nothing by being coloured."""
        for name in ("premise", "extra", "closed", "unused"):
            self.assertRegex(self.css, r"\.rest\.{0}\b".format(name), name)


class TestTheHandles(PageTestCase):
    """What the shell reaches for, the painter has to have put there.

    The page carries the model's node numbers in ``data-`` attributes and
    reads them back when the pointer lands on something.  Both halves fail
    quietly: a hook nobody sets reads as ``undefined``, which reaches
    Python as ``NaN`` and comes back as "no such block", and an operation
    nobody handles comes back as "unknown action" in the notice bar.  In a
    browser each of those looks like the editor doing nothing at all.
    """

    def test_every_data_hook_the_shell_reads_is_one_the_painter_sets(self):
        read = set(re.findall(r"dataset\.(\w+)", self.app))
        written = set(re.findall(r"dataset\.(\w+)\s*=", self.js))
        self.assertTrue(read, "the check found nothing to check")
        self.assertEqual(sorted(read - written), [])

    def test_every_operation_the_shell_sends_is_one_the_session_handles(self):
        from ndweb.session import Session

        sent = set(re.findall(r'op:\s*"([\w-]+)"', self.js))
        self.assertTrue(sent, "the check found nothing to check")
        missing = [name for name in sorted(sent)
                   if not hasattr(Session, "_op_" + name.replace("-", "_"))]
        self.assertEqual(missing, [])


class TestStatuses(PageTestCase):
    def test_a_bar_is_drawn_wrong_unless_something_says_otherwise(self):
        """Styling by exception is what makes a new failure kind safe.

        Listing every kind that should be red would leave the next one
        drawn as though the step were sound, which is the one mistake this
        stylesheet must not make.
        """
        self.assertRegex(self.css, r"\n\.inf > \.bar \{[^}]*--bad")
        for named in ("ok", "pending", "drift"):
            self.assertIn('data-status="{0}"'.format(named), self.css, named)

    def test_the_named_ones_are_the_only_ones_that_are_not_failures(self):
        from ndweb.attempt import BUG_KINDS, _RULE_KINDS

        failures = set(name for _, name in _RULE_KINDS) | BUG_KINDS | {"rule"}
        named = set(re.findall(r'data-status="([\w-]+)"', self.css))
        self.assertEqual(sorted(named & failures), [])

    def test_a_bug_in_the_editor_is_not_dressed_up_as_a_refusal(self):
        from ndweb.attempt import BUG_KINDS, _RULE_KINDS

        self.assertEqual(BUG_KINDS & set(name for _, name in _RULE_KINDS), set())
