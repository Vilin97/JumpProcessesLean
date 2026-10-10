"""Measure the Tree-RSSA generations against each other.

    python3 bench/generations.py --out bench/results/generations.json [--rounds 5]

For each network, the generations from 2 on and the RSSACR port are run alternately for several
rounds on the benchmark span, and each keeps its best time: alternating and taking the best
time make the comparison between generations robust to other load on the machine. Every run
also prints a digest of the final populations; all generations must agree, since each is
proved equal to the specification. Generations 0 and 1 are far slower and are measured by
`run.py` on shorter spans. The method `c-reference` runs the independent C implementation in
bench/c (path in CREF); its digest must agree too. A method `julia:<aggregator>` runs that
JumpProcesses.jl aggregator (warmed up, one repetition per round), so that Julia and Lean can
be measured alternately under the same conditions.
"""
import argparse
import json
import os
import pathlib
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import run as bench  # noqa: E402

FAST = ["treerssa-g2", "treerssa-g3", "treerssa-g4", "treerssa-g5", "treerssa-g6",
        "treerssa-g7", "treerssa-g8", "treerssa-g9", "treerssa-g10", "treerssa-g11",
        "treerssa-g12", "treerssa-g13", "treerssa-g14", "treerssa-g15", "treerssa-g16",
        "rssacr-port"]


def once(model, method, T):
    if method.startswith("julia:"):
        scratch = pathlib.Path(os.environ.get("BENCH_SCRATCH", "/tmp")) / "jumpbench"
        scratch.mkdir(parents=True, exist_ok=True)
        data = bench.run_julia(model, method[len("julia:"):], T, 1, scratch)
        return {"status": "ok", "events": data["events"][0], "seconds": data["times"][0],
                "digest": None}
    if method == "c-reference":
        # bench/c/treerssa.c, built with `cc -O3 -march=native -ffp-contract=off -o <CREF> bench/c/treerssa.c -lm`
        with bench.timed_section():
            out = subprocess.run([os.environ["CREF"], str(bench.rn(model)), f"{T:.6f}", "1"],
                                 capture_output=True, text=True, check=True).stdout
        row = json.loads(out)
        row["status"] = "ok"
        return row
    binary = os.environ.get("JUMPBENCH", str(bench.ROOT / ".lake/build/bin/jumpBench"))
    with bench.timed_section():
        out = subprocess.run([binary, str(bench.rn(model)), method, f"{T:.6f}", "1"],
                             capture_output=True, text=True, check=True).stdout
    row = json.loads([line for line in out.splitlines() if line.startswith("{")][0])
    if row["status"] != "ok":
        raise RuntimeError(f"{method} on {model}: {row['status']}")
    return row


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True)
    parser.add_argument("--rounds", type=int, default=5)
    parser.add_argument("--models", nargs="*", default=[m for m, _ in bench.MODELS])
    parser.add_argument("--methods", nargs="*", default=FAST)
    args = parser.parse_args()
    bench.ensure_rn()
    out = pathlib.Path(args.out)
    record = json.loads(out.read_text()) if out.exists() else {"results": {}}
    record["machine"] = bench.machine()
    record["rounds"] = args.rounds
    spans = dict(bench.MODELS)
    for model in args.models:
        T = spans[model]
        best, rows = {}, {}
        idle = []
        for _ in range(args.rounds):
            for method in args.methods:
                idle.append(bench.wait_idle())
                row = once(model, method, T)
                if method not in best or row["seconds"] < best[method]:
                    best[method] = row["seconds"]
                rows[method] = row
        entry = record["results"].setdefault(model, {})
        for method in args.methods:
            entry[method] = {"T": T, "events": rows[method]["events"],
                             "best_seconds": best[method],
                             "events_per_second": rows[method]["events"] / best[method],
                             "digest": rows[method]["digest"],
                             "measured": {k: record["machine"][k] for k in ("commit", "dirty", "date")}}
        digests = {v["digest"] for k, v in entry.items()
                   if isinstance(v, dict) and (k.startswith("treerssa") or k == "c-reference")}
        digests.discard(None)
        if len(digests) != 1:
            raise RuntimeError(f"implementations disagree on {model}: {digests}")
        entry["min_idle"] = min(idle + [entry.get("min_idle", 1.0)])
        print(model, "  ".join(f"{m.split('-')[-1]} {record['results'][model][m]['events_per_second']:.3g}"
                               for m in args.methods), flush=True)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(record, indent=1) + "\n")


if __name__ == "__main__":
    main()
