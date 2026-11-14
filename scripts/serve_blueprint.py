"""Serve this project's blueprint on its own loopback port."""

import argparse
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
import socket


class BlueprintServer(ThreadingHTTPServer):
    # Windows otherwise permits two http.server processes to share a port.
    allow_reuse_address = False

    def server_bind(self):
        if hasattr(socket, "SO_EXCLUSIVEADDRUSE"):
            self.socket.setsockopt(socket.SOL_SOCKET, socket.SO_EXCLUSIVEADDRUSE, 1)
        super().server_bind()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--port", type=int, default=8873)
    args = parser.parse_args()
    directory = Path(__file__).resolve().parents[1] / "blueprint/web"
    if not (directory / "index.html").is_file():
        parser.error("Build the blueprint first: python scripts/build_blueprint.py")
    handler = partial(SimpleHTTPRequestHandler, directory=str(directory))
    with BlueprintServer(("127.0.0.1", args.port), handler) as server:
        print(f"Ulam floating blueprint: http://127.0.0.1:{args.port}/", flush=True)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass


if __name__ == "__main__":
    main()
