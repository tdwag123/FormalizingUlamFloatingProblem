"""Build the Lean blueprint HTML without requiring a system TeX installation.

plasTeX already implements the packages used by this blueprint. Resolve its
local TeX inputs directly so an unconfigured MiKTeX/kpsewhich cannot interfere.
The standard `leanblueprint web` command remains available on configured hosts.
"""

from pathlib import Path
from html import escape
import os
import re

from plasTeX.TeX import TeX
from plasTeX.client import main


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "blueprint/src"


def write_source_index():
    """Provide real local destinations for blueprint declaration links."""
    target = ROOT / "blueprint/web/find"
    target.mkdir(parents=True, exist_ok=True)
    chunks = ['<!doctype html><html lang="en"><meta charset="utf-8">',
              '<title>Lean source — Ulam floating</title>',
              '<style>body{max-width:1100px;margin:2rem auto;padding:0 1rem;'
              'font-family:system-ui}pre{overflow:auto;padding:1rem;background:#f5f5f5}'
              ':target{background:#fff1a8}a{color:#164b93}</style>',
              '<a href="../index.html">Back to the blueprint</a>',
              '<h1>Lean source</h1><p>Source listing; proof status is recorded '
              'separately in the blueprint. This is not generated API documentation.</p>']
    pattern = re.compile(r"^(?:@\[.*?\]\s*)?(?:theorem|def|abbrev|structure)\s+([\w.]+)")
    for path in sorted((ROOT / "UlamFloating").glob("*.lean")):
        chunks.append(f"<h2>{escape(path.name)}</h2><pre><code>")
        for line in path.read_text(encoding="utf-8").splitlines():
            match = pattern.match(line)
            anchor = f' id="doc/UlamFloating.{match[1]}"' if match else ""
            chunks.append(f"<span{anchor}>{escape(line)}</span>\n")
        chunks.append("</code></pre>")
    chunks.append("</html>")
    (target / "index.html").write_text("".join(chunks), encoding="utf-8")


def local_tex_input(self, name):
    candidate = Path(name)
    bases = [SOURCE]
    current = getattr(self, "filename", None)
    if current:
        bases.insert(0, Path(current).resolve().parent)
    for base in bases:
        path = base / candidate
        for option in (path, path.with_suffix(".tex")):
            if option.is_file():
                return str(option.resolve())
    raise FileNotFoundError(f"No local blueprint input: {name}")


if __name__ == "__main__":
    os.chdir(SOURCE)
    TeX.kpsewhich = local_tex_input
    main(["-c", "plastex.cfg", "web.tex"])
    write_source_index()
