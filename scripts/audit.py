"""Fail closed on proof placeholders or unexpected audited theorem axioms."""
import pathlib
import re
import sys

root = pathlib.Path(__file__).resolve().parent.parent
for path in (root / "JumpProcessesLean").rglob("*.lean"):
    text = path.read_text()
    forbidden = re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", text)
    if forbidden:
        raise SystemExit(f"Forbidden proof/trust token in {path.name}: {forbidden[0]}")
trust = pathlib.Path(sys.argv[1]).read_text()
results = re.findall(r"depends on axioms: \[([^\]]*)\]", trust)
results += [""] * len(re.findall(r"does not depend on any axioms", trust))
expected = len(re.findall(r"^#print axioms ", (root / "Tests/Trust.lean").read_text(), re.MULTILINE))
if len(results) != expected:
    raise SystemExit(f"Expected {expected} theorem audits; found {len(results)}")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for result in results:
    axioms = {s.strip() for s in result.split(",") if s.strip()}
    if not axioms <= allowed:
        raise SystemExit(f"Unexpected proof axioms: {axioms - allowed}")
print(f"PASS {expected} proof dependency audits: only standard Lean axioms")
