"""Run the SSA benchmark suite: JumpProcesses.jl aggregators and the Lean methods on the
five Catalyst-paper networks.

    python3 bench/run.py --julia --lean <method> ... --out bench/results/<name>.json

Every measurement simulates the full network on `(0, T)` from the initial populations.
Throughput is `total events / total wall time` over the repetitions. A method whose
projected run would exceed the time budget is measured on a shorter span `T' < T`
(recorded), since the event rate of the process does not depend on the method.
"""
import argparse
import contextlib
import datetime
import fcntl
import json
import os
import pathlib
import platform
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
MODELS = [  # name, T: about 0.5-1.5 s for the fastest Julia method
    ("multistate", 10000.0),
    ("multisite2", 300.0),
    ("egfr_net", 30.0),
    ("BCR", 10.0),
    ("fceri_gamma2", 300.0),
]
JULIA_METHODS = ["Direct", "SortingDirect", "RDirect", "FRM", "NRM", "CCNRM", "DirectCR",
                 "RSSA", "RSSACR"]
SIZES = {"multistate": (9, 18), "multisite2": (66, 288), "egfr_net": (356, 3749),
         "BCR": (1122, 24388), "fceri_gamma2": (3744, 58276)}


def rn(model):
    return ROOT / "bench" / "models" / "rn" / f"{model}.rn"


def ensure_rn():
    for model, _ in MODELS:
        if not rn(model).exists():
            rn(model).parent.mkdir(parents=True, exist_ok=True)
            subprocess.run([sys.executable, str(ROOT / "bench/scripts/net2rn.py"),
                            str(ROOT / "bench/models/catalyst" / f"{model}.net"), str(rn(model))],
                           check=True)


def julia_cmd():
    return [os.environ.get("JULIA", "julia"), "--startup-file=no", f"--project={ROOT / 'bench/julia'}",
            str(ROOT / "bench/julia/bench.jl")]


@contextlib.contextmanager
def timed_section():
    """Hold an exclusive lock on BENCH_LOCK (if set) for the duration of a timed run, so timed
    runs of cooperating processes on a shared machine never overlap."""
    path = os.environ.get("BENCH_LOCK")
    if not path:
        yield
        return
    with open(path, "a") as handle:
        fcntl.flock(handle, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)
    # leave the lock to a waiting process before this one asks for it again
    time.sleep(LOCK_GAP)


def run_julia(model, method, T, reps, scratch, timeout=None):
    out = scratch / f"julia_{model}_{method}.json"
    with timed_section():
        subprocess.run(julia_cmd() + [str(rn(model)), repr(T), str(reps), str(out), method],
                       check=True, stdout=subprocess.DEVNULL, timeout=timeout)
    data = json.loads(out.read_text())["results"][method]
    return {"times": data["times"], "events": data["events"]}


def run_lean(model, method, T, reps, timeout=None, max_events=10**12):
    binary = os.environ.get("JUMPBENCH", str(ROOT / ".lake/build/bin/jumpBench"))
    with timed_section():
        proc = subprocess.run([str(binary), str(rn(model)), method, f"{T:.6f}", str(reps),
                               str(max_events)], check=True, capture_output=True, text=True,
                              timeout=timeout)
    rows = [json.loads(line) for line in proc.stdout.splitlines() if line.startswith("{")]
    bad = [r for r in rows if r["status"] not in ("ok", "eventLimit")]
    if bad:
        raise RuntimeError(f"{method} on {model}: {bad[0]['status']}")
    return {"times": [r["seconds"] for r in rows], "events": [r["events"] for r in rows],
            "digests": [r.get("digest") for r in rows],
            "capped": any(r["status"] == "eventLimit" for r in rows)}


STARTUP = 120.0  # allowance for process start, model loading and compilation
IDLE = float(os.environ.get("BENCH_IDLE", "0"))  # wait for this idle CPU fraction before runs
# BENCH_LOCK: a lock file shared with other benchmarking processes on the machine
LOCK_GAP = float(os.environ.get("BENCH_LOCK_GAP", "2"))  # seconds without the lock between runs


def idle_fraction(dt=0.5):
    """Fraction of CPU time idle over `dt` seconds, from /proc/stat (1.0 where unavailable)."""
    def snap():
        fields = list(map(int, open("/proc/stat").readline().split()[1:]))
        return sum(fields), fields[3] + fields[4]
    try:
        t0, i0 = snap()
        time.sleep(dt)
        t1, i1 = snap()
    except OSError:
        return 1.0
    return (i1 - i0) / max(t1 - t0, 1)


def wait_idle(timeout=3600.0):
    """On a shared machine, wait (bounded) until other load drops; return the idle fraction."""
    start = time.time()
    idle = idle_fraction()
    while idle < IDLE and time.time() - start < timeout:
        time.sleep(5)
        idle = idle_fraction()
    return idle


def rate_on(runner, model, method, span, budget):
    """Throughput of one run on `(0, span)`; a run over budget is retried on a 10x shorter span."""
    while True:
        try:
            wait_idle()
            probe = runner(model, method, span, 1, timeout=budget + STARTUP)
            return span, max(sum(probe["events"]), 1) / max(sum(probe["times"]), 1e-9)
        except subprocess.TimeoutExpired:
            span /= 10


def measure(runner, model, method, T, budget, min_reps, probe_events):
    """Probe on growing spans (`T/100`, then `T/10`, since some methods slow down as more
    species are populated), then measure on the longest span that fits the budget."""
    span, rate = rate_on(runner, model, method, T / 100, budget)
    projected = probe_events / rate
    if span == T / 100 and projected * min_reps <= budget:
        _, rate10 = rate_on(runner, model, method, T / 10, budget)
        projected = max(projected, probe_events / rate10)
    if projected * min_reps <= budget:
        span, reps = T, max(min_reps, min(10, int(budget / max(projected, 1e-9))))
    else:
        span, reps = max(T * budget / (projected * min_reps), span / 10), min_reps
    while True:
        try:
            idle = wait_idle()
            result = runner(model, method, span, reps, timeout=3 * budget + STARTUP)
            break
        except subprocess.TimeoutExpired:
            span /= 4
    events, seconds = sum(result["events"]), sum(result["times"])
    result.update({"T": span, "reps": reps, "events_per_second": events / seconds, "idle": idle,
                   "mean_events": events / reps, "median_time": sorted(result["times"])[reps // 2],
                   "full_span": span == T})
    return result


def machine():
    cpu = "unknown"
    try:
        for line in open("/proc/cpuinfo"):
            if line.startswith("model name"):
                cpu = line.split(":", 1)[1].strip()
                break
    except OSError:
        pass
    commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True,
                            text=True).stdout.strip()
    # uncommitted changes: the measured code is then not exactly the recorded commit
    dirty = bool(subprocess.run(["git", "-C", str(ROOT), "status", "--porcelain"],
                                capture_output=True, text=True).stdout.strip())
    return {"cpu": cpu, "platform": platform.platform(), "commit": commit, "dirty": dirty,
            "date": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--julia", action="store_true")
    parser.add_argument("--julia-methods", nargs="*", default=JULIA_METHODS)
    parser.add_argument("--lean", nargs="*", default=[])
    parser.add_argument("--models", nargs="*", default=[m for m, _ in MODELS])
    parser.add_argument("--budget", type=float, default=30.0, help="seconds per measurement")
    parser.add_argument("--min-reps", type=int, default=3)
    parser.add_argument("--out", required=True)
    args = parser.parse_args()
    ensure_rn()
    scratch = pathlib.Path(os.environ.get("BENCH_SCRATCH", "/tmp")) / "jumpbench"
    scratch.mkdir(parents=True, exist_ok=True)
    out = pathlib.Path(args.out)
    record = json.loads(out.read_text()) if out.exists() else {"results": {}}
    # the file can merge several runs: the latest run's machine record, and each result's own
    record["machine"] = machine()
    spans = dict(MODELS)
    for model in args.models:
        T = spans[model]
        # expected events on (0, T) from a reference run, used to project full-span costs
        reference = record["results"].get(model, {}).get("julia:RSSACR") or \
            record["results"].get(model, {}).get("lean:rssacr-port")
        probe_events = reference["mean_events"] * (1 if reference["full_span"] else T / reference["T"]) \
            if reference else None
        tasks = [("julia", m) for m in (args.julia_methods if args.julia else [])] + \
                [("lean", m) for m in args.lean]
        if probe_events is None:
            first = ("julia", "RSSACR") if args.julia else ("lean", "rssacr-port")
            runner = (lambda mo, me, t, r, timeout=None: run_julia(mo, me, t, r, scratch, timeout)) \
                if first[0] == "julia" else run_lean
            quick = runner(model, first[1], T, 1)
            probe_events = sum(quick["events"])
        for language, method in tasks:
            runner = (lambda mo, me, t, r, timeout=None: run_julia(mo, me, t, r, scratch, timeout)) \
                if language == "julia" else run_lean
            started = time.time()
            result = measure(runner, model, method, T, args.budget, args.min_reps, probe_events)
            result["measured"] = {k: record["machine"][k] for k in ("commit", "dirty", "date")}
            record["results"].setdefault(model, {})[f"{language}:{method}"] = result
            print(f"{model:13s} {language}:{method:16s} {result['events_per_second']:12.4g} events/s"
                  f"  T={result['T']:.4g}  reps={result['reps']}  ({time.time() - started:.0f} s)",
                  flush=True)
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(json.dumps(record, indent=1) + "\n")
    record["models"] = {m: {"T": spans[m], "species": SIZES[m][0], "reactions": SIZES[m][1]}
                        for m in spans}
    out.write_text(json.dumps(record, indent=1) + "\n")


if __name__ == "__main__":
    main()
