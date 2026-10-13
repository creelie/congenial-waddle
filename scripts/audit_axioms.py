"""Reads the output of `lake env lean Check.lean` and checks that every main theorem rests only on
the three standard axioms and the two axioms that `native_decide` records for the compiled search
(the Boolean equations `NilCore.root () = true` and `NilCore.checkCands () = true`)."""
import re
import sys

ALLOWED = {
    "propext", "Classical.choice", "Quot.sound",
    "NilCore.root_eq._native.native_decide.ax_1_1",
    "NilCore.checkCands_eq._native.native_decide.ax_1_1",
}
EXPECTED = 16

text = open(sys.argv[1]).read()
if "sorryAx" in text or "error" in text:
    sys.exit("audit: sorry or error in the output")
found = re.findall(r"^'(\S+)' depends on axioms: \[([^\]]*)\]", text, re.M)
bad = 0
for name, axioms in found:
    used = {a.strip() for a in axioms.split(",") if a.strip()}
    extra = used - ALLOWED
    native = sorted(a for a in used if "native" in a)
    print(f"{name}: {'standard axioms only' if not native else 'standard axioms + ' + ', '.join(native)}")
    if extra:
        print(f"  not allowed: {sorted(extra)}")
        bad += 1
if len(found) != EXPECTED:
    sys.exit(f"audit: expected {EXPECTED} theorems, found {len(found)}")
if bad:
    sys.exit("audit: unexpected axioms")
print(f"axiom audit: {len(found)} theorems, all within the allowed axioms")
