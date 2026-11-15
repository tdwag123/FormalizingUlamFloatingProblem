"""Build and kernel-audit the separate seventh-density project.

Use --require-target before claiming completion or publishing a completed proof.
An ordinary development audit explicitly reports an absent rigidity theorem.
"""

import argparse
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "UlamFloating.Seventh."


def run(*args):
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True,
                            encoding="utf-8", errors="replace")
    if result.returncode:
        print(result.stdout + result.stderr, flush=True)
        raise SystemExit(result.returncode)
    return result.stdout + result.stderr


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-target", action="store_true")
    args = parser.parse_args()
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8")
    declarations = {}
    for path in sorted((ROOT / "Seventh").glob("*.lean")):
        source = path.read_text(encoding="utf-8")
        for kind, name in re.findall(
                r"^(?:noncomputable )?(theorem|lemma|def|structure) ([A-Za-z_][A-Za-z_0-9.]*)",
                source, re.MULTILINE):
            full = PREFIX + name
            if full in declarations:
                raise SystemExit("Duplicate declaration in source scan: " + full)
            declarations[full] = kind
    if not declarations:
        raise SystemExit("No seventh-density declarations found")
    print("Building seventh-density project...", flush=True)
    print(run("lake", "build"), end="", flush=True)
    roots = ", ".join("`" + name for name in declarations)
    proofs = [name for name, kind in declarations.items() if kind in ("theorem", "lemma")]
    proof_list = ", ".join("`" + name for name in proofs)
    target = PREFIX + "rigidity"
    has_target = target in proofs
    target_check = (
        f"example : UlamFloating.PerimetralRigidity ((1 : ℝ) / 7) := {target}\n"
        if has_target else "")
    source = f'''import Seventh
import Lean.Util.CollectAxioms

example : UlamFloating.Seventh.rigidityStatement =
    UlamFloating.PerimetralRigidity ((1 : ℝ) / 7) := rfl
{target_check}
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots : List Name := [{roots}]
  for name in roots do
    unless (env.checked.get.find? name).isSome do
      throwError "Missing checked declaration: {{name}}"
  for name in ([{proof_list}] : List Name) do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Expected a proved theorem: {{name}}"
  let (_, state) := ((roots.forM Lean.CollectAxioms.collect).run env).run {{}}
  for axiomName in state.axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains axiomName do
      throwError "Disallowed axiom dependency: {{axiomName}}"
  logInfo m!"SEVENTH_AUDITED {{roots.length}}"
'''
    with tempfile.TemporaryDirectory(prefix="audit-", dir=ROOT / ".lake") as tmp:
        path = Path(tmp) / "Audit.lean"
        path.write_text(source, encoding="utf-8")
        print(f"Auditing {len(declarations)} declarations...", flush=True)
        output = run("lake", "env", "lean", str(path))
    reports = re.findall(r"^SEVENTH_AUDITED (\d+)$", output, re.MULTILINE)
    if reports != [str(len(declarations))]:
        raise SystemExit("Missing or inconsistent kernel-audit completion marker")
    print(f"PASS: {len(proofs)} theorems; all scanned declarations and their dependencies "
          "have no admitted proofs or nonstandard axioms.", flush=True)
    if has_target:
        print("PASS: exact unconditional PerimetralRigidity (1 / 7) theorem type.")
    else:
        print("INCOMPLETE: the seventh-density rigidity theorem is not yet proved.")
        if args.require_target:
            raise SystemExit(1)


if __name__ == "__main__":
    main()
