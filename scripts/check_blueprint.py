"""Validate blueprint links and audit their compiled Lean dependencies."""

from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def run(*args: str) -> str:
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True,
                            encoding="utf-8", errors="replace")
    if result.returncode:
        sys.stderr.write(result.stdout + result.stderr)
        raise SystemExit(result.returncode)
    return result.stdout + result.stderr


def main() -> None:
    # Lake emits Unicode status marks even when Windows uses a legacy console
    # encoding. Preserve its output instead of failing before the Lean audit.
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8")
    source = (ROOT / "blueprint/src/content.tex").read_text(encoding="utf-8")
    labels = re.findall(r"\\label\{([^}]+)\}", source)
    if len(labels) != len(set(labels)):
        raise SystemExit("Duplicate blueprint labels")
    deps = re.findall(r"\\uses\{([^}]+)\}", source)
    unknown = {s.strip() for group in deps for s in group.split(",")} - set(labels)
    if unknown:
        raise SystemExit(f"Unknown dependency labels: {sorted(unknown)}")
    groups = re.findall(r"\\lean\{([^}]+)\}", source)
    names = sorted({s.strip() for group in groups for s in group.split(",")})
    if not names or any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*", n) for n in names):
        raise SystemExit("Missing or malformed Lean declaration links")
    nodes = list(re.finditer(
        r"\\begin\{(definition|lemma|theorem|proposition)\}(.*?)\\end\{\1\}",
        source, re.DOTALL))
    specifications = set()
    proofs = set()
    for node in nodes:
        kind, body = node.group(1), node.group(2)
        linked = {s.strip() for group in re.findall(r"\\lean\{([^}]+)\}", body)
                  for s in group.split(",")}
        if not linked:
            raise SystemExit(f"Blueprint node lacks a Lean statement: {body[:100]}")
        specs = {name for name in linked if name.endswith("Statement")}
        if specs:
            following = re.match(r"\s*\\begin\{proof\}(.*?)\\end\{proof\}",
                                 source[node.end():], re.DOTALL)
            if r"\leanok" in body or (following and r"\leanok" in following[1]):
                raise SystemExit("A statement-only definition is marked as proved")
            specifications.update(specs)
        elif kind != "definition":
            proofs.update(linked)
    print("Building the Lean library...", flush=True)
    print(run("lake", "build"), end="", flush=True)
    # Keep the temporary Lean file in the project so Lake resolves its imports.
    with tempfile.TemporaryDirectory(prefix="blueprint-audit-", dir=ROOT / ".lake") as tmp:
        audit = Path(tmp) / "Audit.lean"
        root_names = ", ".join(f"`{name}" for name in names)
        proof_names = ", ".join(f"`{name}" for name in sorted(proofs))
        kind_check = (
            "\nopen Lean Elab Command in\nrun_cmd do\n"
            "  let env ← getEnv\n"
            f"  for name in ([{proof_names}] : List Name) do\n"
            "    match env.find? name with\n"
            "    | some (.thmInfo _) => pure ()\n"
            '    | _ => throwError "Expected a proved theorem: {name}"\n')
        spec_checks = "\n".join(f"example : Prop := {name}" for name in sorted(specifications))
        targets = {f"UlamFloating.{name}_rigidity": denominator for name, denominator in
                   (("third", 3), ("quarter", 4), ("fifth", 5))}
        target_checks = "\n".join(
            f"example : UlamFloating.PerimetralRigidity ((1 : ℝ) / {denominator}) := {name}"
            for name, denominator in targets.items() if name in proofs)
        # Use Lean's own axiom collector with one shared visited set. Checking
        # the union of all roots' dependencies against an allowlist is equivalent
        # to checking each root separately, without repeatedly walking mathlib.
        axiom_check = (
            "\nopen Lean Elab Command in\nrun_cmd do\n"
            "  let env ← getEnv\n"
            f"  let roots : List Name := [{root_names}]\n"
            "  for name in roots do\n"
            "    unless (env.checked.get.find? name).isSome do\n"
            '      throwError "Missing checked declaration: {name}"\n'
            "  let (_, state) := ((roots.forM Lean.CollectAxioms.collect).run env).run {}\n"
            "  for axiomName in state.axioms do\n"
            "    unless ([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains axiomName do\n"
            '      throwError "Disallowed axiom dependency: {axiomName}"\n'
            '    logInfo m!"ULAM_AUDIT_AXIOM {axiomName}"\n'
            '  logInfo m!"ULAM_AUDIT_ROOTS {roots.length}"\n')
        audit.write_text("import UlamFloating\nimport Lean.Util.CollectAxioms\n",
                         encoding="utf-8")
        with audit.open("a", encoding="utf-8") as handle:
            handle.write(spec_checks + "\n" + target_checks + "\n" + kind_check + axiom_check)
        print(f"Auditing {len(names)} declarations with Lean's shared dependency traversal...",
              flush=True)
        output = run("lake", "env", "lean", str(audit))
    if "sorryAx" in output:
        raise SystemExit("A linked declaration depends on sorryAx")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    reported = set(re.findall(r"^ULAM_AUDIT_AXIOM (\S+)$", output, re.MULTILINE))
    unexpected = reported - allowed
    if unexpected:
        raise SystemExit(f"Nonstandard axioms: {sorted(unexpected)}")
    reports = re.findall(r"^ULAM_AUDIT_ROOTS (\d+)$", output, re.MULTILINE)
    if reports != [str(len(names))]:
        raise SystemExit(f"Expected an audit of {len(names)} roots, received {reports}")
    print(f"Validated {len(labels)} blueprint nodes and {len(names)} Lean links; "
          "no admitted proofs or nonstandard axioms in their dependencies.")
    print(f"Distinguished {len(proofs)} proved lemmas from "
          f"{len(specifications)} statement-only propositions.")
    checked_targets = [str(denominator) for name, denominator in targets.items() if name in proofs]
    if checked_targets:
        print("Checked exact unconditional rigidity types at densities: " +
              ", ".join(f"1/{denominator}" for denominator in checked_targets) + ".")


if __name__ == "__main__":
    main()
