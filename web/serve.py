"""Serve the editor for development: ``python3 -m web.serve``.

The page has to come over http rather than from a file, because Safari
refuses to fetch the Python sources from a ``file://`` page.  Serving the
repository root is deliberate: the front end lives in ``web/`` and reaches
the two packages beside it.
"""

from __future__ import annotations

import http.server
import os
import socketserver
import webbrowser

PORT = 8000
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class Handler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=ROOT, **kwargs)

    def end_headers(self):
        # The sources change while the editor is open; never serve a stale one.
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def log_message(self, format, *args):
        pass


def main() -> None:
    socketserver.TCPServer.allow_reuse_address = True
    with socketserver.TCPServer(("127.0.0.1", PORT), Handler) as server:
        url = "http://127.0.0.1:{0}/web/".format(PORT)
        print("serving {0} at {1}".format(ROOT, url))
        print("press ctrl-c to stop")
        webbrowser.open(url)
        server.serve_forever()


if __name__ == "__main__":
    main()
