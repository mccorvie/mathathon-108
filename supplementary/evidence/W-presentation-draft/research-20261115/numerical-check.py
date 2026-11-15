#!/usr/bin/env python3
"""COMPUTED: exact endpoint recombination and selected finite-cutoff replay.

This reuses the event theta.py arithmetic algorithm; it is neither an independent
interval-engine audit nor a Lean proof. Saved interval endpoints are inputs.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
INPUT = HERE / "numerical-inputs.json"
raw = INPUT.read_bytes()
data = json.loads(raw)
A, S = data["A"], data["summary"]
theta_path = HERE / "numerical-source-theta.py"
theta_bytes = theta_path.read_bytes()
theta_git_blob = hashlib.sha1(b"blob " + str(len(theta_bytes)).encode() + b"\0" + theta_bytes).hexdigest()
assert theta_git_blob == "40b3e761c2b4ce777049867c622c49cb0e0455e4"
spec = importlib.util.spec_from_file_location("event_theta", theta_path)
theta = importlib.util.module_from_spec(spec)
spec.loader.exec_module(theta)

def item(value):
    return {"exact": str(value), "decimal": float(value)}

out = {
    "status": "COMPUTED; imported arithmetic algorithm and saved interval endpoints",
    "source_commit": data["source_commit"],
    "input_sha256": hashlib.sha256(raw).hexdigest(),
    "theta_sha256": hashlib.sha256(theta_bytes).hexdigest(),
    "theta_git_blob": theta_git_blob,
}
gain = F(1159, 28800)
low6, up6 = F(S["nu6_dual"]["LB_lower_exact"]), F(S["nu6_primal"]["U_upper_exact"])
low8, up8 = F(S["energy_lower_exact"]), F(S["energy_upper_exact"])
out["repaired_limiting_margins"] = {
    "5:6 upper": item(F(A["5:6"]["Astar_exact"][1]) + up6),
    "7:6 lower": item(F(A["7:6"]["Astar_exact"][0]) + low6),
    "5:8 lower original": item(F(A["5:8"]["Astar_exact"][0]) + low8),
    "5:8 upper improved": item(F(A["5:8"]["Astar_exact"][1]) - gain + up8),
    "7:8 lower": item(F(A["7:8"]["Astar_exact"][0]) + low8),
    "5:8 improved finite M200 lower": item(F(A["5:8"]["A200"]) - gain + low8),
}
out["conditional_actual_analytic_slack_ceiling"] = {
    "nu6": item(up6-low6), "nu8": item(up8-low8),
    "requires": "E204/E56 finite-arcsine Jensen lower bound; weak duality alone is insufficient",
}
out["exact_s_steps"] = {}
for nu, expected in [(6,F(751,768)),(8,F(12817,14400))]:
    step = F(A[f"7:{nu}"]["A200"]) - F(A[f"5:{nu}"]["A200"])
    from_outer = F(37,60) + F(A[f"7:{nu}"]["I_out"]) - F(A[f"5:{nu}"]["I_out"])
    assert step == from_outer == expected
    out["exact_s_steps"][str(nu)] = item(step)
out["stored_tail_lower_bound_checks"] = {}
for nu in [6,8]:
    c, k2 = F(A[f"7:{nu}"]["cM"]), F(A[f"7:{nu}"]["K2"])
    assert 40*c-k2 > 0
    out["stored_tail_lower_bound_checks"][str(nu)] = {
        "K2_over_c": item(k2/c), "40c_minus_K2": item(40*c-k2),
        "requires": "certify/README section3.6 period/tail proof; constants are read-back",
    }
out["finite_cutoff_replay"] = {}
for s, nu, cutoff in [(5,6,200),(5,8,200),(5,8,840)]:
    arithmetic = theta.A_M(theta.Pkg(s,nu,"S"),cutoff)
    if cutoff == 200:
        assert arithmetic == F(A[f"{s}:{nu}"]["A200"])
    upper = arithmetic + (up6 if nu==6 else up8-gain)
    out["finite_cutoff_replay"][f"{s}:{nu}:M{cutoff}"] = {
        "arithmetic": item(arithmetic), "margin_upper": item(upper),
        "improved_nu8": nu==8,
    }
assert out["finite_cutoff_replay"]["5:6:M200"]["margin_upper"]["decimal"] < 0
assert out["finite_cutoff_replay"]["5:8:M200"]["margin_upper"]["decimal"] > 0
assert out["finite_cutoff_replay"]["5:8:M840"]["margin_upper"]["decimal"] < 0
out["scalar_compositions"] = {
    "allM_floor": item(F(229,100)-F(139,100)),
    "triangle": item(F(37,60)-F(3,50)),
    "retaining_unremoved_pole_term": item(F(37,60)+2*F(2147,14400)-F(3,50)),
}
(HERE / "numerical-results.json").write_text(json.dumps(out,indent=2)+"\n")
for k,v in out["repaired_limiting_margins"].items(): print(k,v["decimal"])
for k,v in out["finite_cutoff_replay"].items(): print(k,v["margin_upper"]["decimal"])
print("ALL EXACT COMPARISONS PASS")
