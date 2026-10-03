#!/usr/bin/env python3
"""Check compiled project dependencies of the retained conditional scalar proof.

This is a Lean-dependent gate. It inspects both types and proof/definition
values, recursively through project declarations. It does not infer arithmetic
interpretations, erase the legacy shell's extra fields, or establish that any
supplied arithmetic input is independently proved.
"""

from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]

PROBE = r'''
import Lean
import SixBirdsBSD

open Lean Elab Command

private def roots : Array Name := #[
  `SixBirdsBSD.Closure.ScalarBSD.normalizedFixityForcesScalarBSD,
  `SixBirdsBSD.Closure.ScalarBSD.rankGatedRecognitionForcesScalarBSD,
  `SixBirdsBSD.Closure.SelShell.piBSDForcesStrongBSD,
  `SixBirdsBSD.Closure.Landing.strongBSDConditional]

private def excluded (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "SixBirdsBSD.Closure.EtaFormula." ||
  s.startsWith "SixBirdsBSD.Closure.ChiCTp." ||
  s.startsWith "SixBirdsBSD.Closure.AORInstance." ||
  s == "SixBirdsBSD.Closure.SelShell.masterTheoremApplicability" ||
  s == "SixBirdsBSD.Closure.SelShell.compositeSignature" ||
  s.startsWith "SixBirdsBSD.Closure.SelShell.selBSDShell.ablate" ||
  s == "SixBirdsBSD.Closure.SelShell.selBSDShell.masterFromRecognitionAudits" ||
  s.startsWith "SixBirdsBSD.Closure.SelShell.selBSDShell.compositeComputable" ||
  s.startsWith "SixBirdsBSD.Closure.SelShell.selBSDShell.compositeFalsifiable" ||
  s.startsWith "SixBirdsBSD.Closure.SelShell.selBSDShell.genuineDependence"

private def visit (env : Environment) (root : Name) : CommandElabM Unit := do
  let mut todo := [root]
  let mut seen : NameSet := {}
  let mut count := 0
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if excluded n then
      throwError "excluded dependency in {root}: {n}"
    if n.toString.startsWith "SixBirdsBSD." then
      count := count + 1
      let some ci := env.find? n | throwError "missing declaration: {n}"
      for dep in ci.type.getUsedConstants do
        todo := dep :: todo
      if let some value := ci.value? then
        for dep in value.getUsedConstants do
          todo := dep :: todo
      if root.toString.startsWith "SixBirdsBSD.Closure.ScalarBSD." &&
          !n.toString.startsWith "SixBirdsBSD.Closure.ScalarBSD." then
        throwError "scalar core imports project record in {root}: {n}"
  logInfo m!"conditional dependency check: {root}: {count} project declarations; no excluded dependencies"

run_cmd do
  let env ← getEnv
  for root in roots do
    visit env root
'''


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="bsd-conditional-core-") as directory:
        probe = Path(directory) / "ConditionalCore.lean"
        probe.write_text(PROBE, encoding="utf-8")
        result = subprocess.run(
            ["lake", "env", "lean", str(probe)], cwd=ROOT / "lean",
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
    print(result.stdout, end="")
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
