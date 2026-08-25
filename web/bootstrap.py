"""What Pyodide runs once the sources are in place.

Kept outside both packages, for the same reason ``demo.py`` is: running a
module of a package as ``__main__`` imports it a second time under its
real name, giving two copies of every class, and equality between a
formula from one copy and a formula from the other would silently be
false.

The boundary is deliberately one function taking a string and returning a
string.  Passing objects across would be faster and would cost the thing
that matters more: with JSON in and JSON out, the tests drive exactly the
call the browser drives, and ``json.dumps`` fails loudly if a ``Formula``
ever escapes into the view.
"""

import json
import sys

sys.path.insert(0, "/lib")

from ndweb.session import Session

_session = Session()


def dispatch(payload):
    """One action in, the whole state out."""
    return json.dumps(_session.dispatch(json.loads(payload)), ensure_ascii=False)
