"""Check generated HTML links, source anchors, and the dependency graph."""

from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1] / "blueprint/web"


class Links(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.ids = set()
        self.urls = []
        self.feed(text)

    def handle_starttag(self, tag, attributes):
        attrs = dict(attributes)
        if "id" in attrs:
            self.ids.add(attrs["id"])
        for key in ("href", "src", "xlink:href"):
            if attrs.get(key):
                self.urls.append(attrs[key])


def main():
    files = list(ROOT.rglob("*.html"))
    if not files:
        raise SystemExit("Build the blueprint first")
    parsed = {p.resolve(): Links(p.read_text(encoding="utf-8")) for p in files}
    checked = 0
    for source, page in parsed.items():
        for url in page.urls:
            parts = urlsplit(url)
            if parts.scheme or parts.netloc:
                continue
            target = (source.parent / unquote(parts.path)).resolve() if parts.path else source
            if target.is_dir():
                target /= "index.html"
            if not target.exists():
                raise SystemExit(f"Missing link target: {source.name}: {url}")
            if parts.fragment and target.suffix in (".html", ".svg"):
                dest = parsed.get(target) or Links(target.read_text(encoding="utf-8"))
                if unquote(parts.fragment) not in dest.ids:
                    raise SystemExit(f"Missing anchor: {source.name}: {url}")
            checked += 1
    graph = (ROOT / "dep_graph_document.html").read_text(encoding="utf-8")
    if "<svg" not in graph:
        raise SystemExit("Missing dependency graph SVG")
    print(f"Checked {len(files)} HTML pages and {checked} local links/anchors; graph present.")


if __name__ == "__main__":
    main()
