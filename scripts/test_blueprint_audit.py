"""Exercise the production blueprint audit against valid and invalid Lean fixtures."""

from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_blueprint


PROJECT = check_blueprint.ROOT


class BlueprintAuditTests(unittest.TestCase):
    def audit(self, declarations: str, nodes: str) -> str:
        # Only the fixture blueprint and declarations differ. Use the production
        # source generator, theorem-kind checks, axiom collector, and result parser.
        with tempfile.TemporaryDirectory(prefix="audit-test-", dir=PROJECT / ".lake") as tmp:
            fixture = Path(tmp)
            (fixture / "blueprint/src").mkdir(parents=True)
            (fixture / ".lake").mkdir()
            (fixture / "blueprint/src/content.tex").write_text(nodes, encoding="utf-8")

            def run_fixture(*args: str) -> str:
                if args == ("lake", "build"):
                    # The real library is built by CI before these isolated tests.
                    return ""
                self.assertEqual(args[:3], ("lake", "env", "lean"))
                source = Path(args[3])
                marker = "import Lean.Util.CollectAxioms\n"
                text = source.read_text(encoding="utf-8")
                self.assertIn(marker, text)
                source.write_text(text.replace(marker, marker + declarations + "\n", 1),
                                  encoding="utf-8")
                result = subprocess.run(args, cwd=PROJECT, capture_output=True, text=True,
                                        encoding="utf-8", errors="replace")
                output = result.stdout + result.stderr
                if result.returncode:
                    raise SystemExit(output)
                return output

            output = StringIO()
            with patch.object(check_blueprint, "ROOT", fixture), \
                    patch.object(check_blueprint, "run", run_fixture), redirect_stdout(output):
                check_blueprint.main()
            return output.getvalue()

    @staticmethod
    def lemma(name: str) -> str:
        return (r"\begin{lemma}\label{fixture}\lean{" + name +
                r"}\leanok Fixture.\end{lemma}")

    def test_valid_shared_dependency(self):
        declarations = (
            "theorem AuditFixture.first : True := True.intro\n"
            "theorem AuditFixture.second : True := AuditFixture.first\n")
        nodes = self.lemma("AuditFixture.first,AuditFixture.second")
        self.assertIn("2 Lean links", self.audit(declarations, nodes))

    def test_transitive_custom_axiom_rejected(self):
        declarations = (
            "axiom AuditFixture.untrusted : False\n"
            "def AuditFixture.hidden : False := AuditFixture.untrusted\n"
            "theorem AuditFixture.claim : False := AuditFixture.hidden\n")
        with self.assertRaisesRegex(SystemExit, "Disallowed axiom dependency: AuditFixture.untrusted"):
            self.audit(declarations, self.lemma("AuditFixture.claim"))

    def test_sorry_rejected(self):
        with self.assertRaisesRegex(SystemExit, "Disallowed axiom dependency: sorryAx"):
            self.audit("theorem AuditFixture.claim : True := by sorry\n",
                       self.lemma("AuditFixture.claim"))

    def test_proposition_definition_is_not_a_proof(self):
        with self.assertRaisesRegex(SystemExit, "Expected a proved theorem: AuditFixture.claim"):
            self.audit("def AuditFixture.claim : Prop := False\n",
                       self.lemma("AuditFixture.claim"))

    def test_missing_declaration_rejected(self):
        nodes = (r"\begin{definition}\label{fixture}\lean{AuditFixture.missing}"
                 r"Fixture.\end{definition}")
        with self.assertRaisesRegex(SystemExit, "Missing checked declaration: AuditFixture.missing"):
            self.audit("", nodes)

    def test_statement_cannot_be_marked_proved(self):
        with self.assertRaisesRegex(SystemExit, "statement-only definition is marked as proved"):
            self.audit("def AuditFixture.claimStatement : Prop := False\n",
                       self.lemma("AuditFixture.claimStatement"))


if __name__ == "__main__":
    unittest.main()
