"""Draw the benchmark figures from the recorded results (no dependencies).

    python3 bench/plot.py

Reads bench/results/{julia,lean,generations}.json and writes
  bench/results/history.svg      animated: Tree-RSSA generations vs JumpProcesses.jl aggregators
  bench/results/generations.svg  static: throughput per generation and network
  bench/results/headtohead.svg   static: Lean against the fastest Julia aggregator, same window
  bench/results/summary.md       the numbers behind them
Throughput is events per second of the best repetition of each measurement.
"""
import json
import math
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent
RES = ROOT / "results"
MODELS = [("multistate", 18), ("multisite2", 288), ("egfr_net", 3749), ("BCR", 24388),
          ("fceri_gamma2", 58276)]
LABEL = {"multistate": "multistate", "multisite2": "multisite2", "egfr_net": "egfr_net",
         "BCR": "BCR", "fceri_gamma2": "fcεRI γ2"}
JULIA = [("Direct", "#4c72b0", "circle"), ("SortingDirect", "#55a868", "square"),
         ("RDirect", "#8172b2", "triangle"), ("FRM", "#ccb974", "diamond"),
         ("NRM", "#64b5cd", "circle"), ("CCNRM", "#8c8c8c", "square"),
         ("DirectCR", "#dd8452", "triangle"), ("RSSA", "#937860", "diamond"),
         ("RSSACR", "#da8bc3", "star")]
GENERATIONS = [
    ("treerssa-spec", "specification: the proved Tree-RSSA itself"),
    ("treerssa-g1", "flat FloatArray sum tree, incremental path updates"),
    ("treerssa-g2", "native float operations, inlined draws, unchanged leaves kept"),
    ("treerssa-g3", "compiled mass-action factors, path updates batched per refresh"),
    ("treerssa-g4", "one allocation-free tail-recursive driver"),
    ("treerssa-g5", "per-species contiguous records, unchanged integer factors skipped"),
    ("treerssa-g6", "exact propensity only on lower-bound rejection, natural-number updates"),
    ("treerssa-g7", "finiteness as two inline comparisons (proved in Lean's float model)"),
    ("treerssa-g8", "no reference counting on the proposal path"),
    ("treerssa-g9", "inlined staleness test on firing"),
    ("treerssa-g10", "single-comparison tests: no joins on the proposal path"),
]
TREE = "#c0392b"


def load(name):
    path = RES / f"{name}.json"
    return json.loads(path.read_text()) if path.exists() else {"results": {}}


def best_rate(rec):
    """Best repetition: events / seconds."""
    if "best_seconds" in rec:
        return rec["events"] / rec["best_seconds"]
    pairs = list(zip(rec["events"], rec["times"]))
    return max(e / t for e, t in pairs if t > 0)


def collect():
    julia, lean, gens = load("julia"), load("lean"), load("generations")
    rates = {}
    for model, _ in MODELS:
        row = {}
        for key, rec in julia["results"].get(model, {}).items():
            row[key] = best_rate(rec)
        for key, rec in lean["results"].get(model, {}).items():
            row[key] = best_rate(rec)
        for key, rec in gens["results"].get(model, {}).items():
            if isinstance(rec, dict) and "best_seconds" in rec:
                row["lean:" + key] = best_rate(rec)
        rates[model] = row
    meta = {"julia": julia.get("machine", {}), "lean": lean.get("machine", {}),
            "generations": gens.get("machine", {})}
    return rates, meta


def marker(shape, x, y, color, r=4.2, fill="none", width=1.5):
    if shape == "circle":
        return f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r}" fill="{fill}" stroke="{color}" stroke-width="{width}"/>'
    if shape == "square":
        return (f'<rect x="{x - r:.1f}" y="{y - r:.1f}" width="{2 * r:.1f}" height="{2 * r:.1f}" '
                f'fill="{fill}" stroke="{color}" stroke-width="{width}"/>')
    if shape == "triangle":
        return (f'<path d="M{x:.1f},{y - r * 1.15:.1f}L{x + r:.1f},{y + r * 0.85:.1f}'
                f'L{x - r:.1f},{y + r * 0.85:.1f}Z" fill="{fill}" stroke="{color}" stroke-width="{width}"/>')
    if shape == "diamond":
        return (f'<path d="M{x:.1f},{y - r * 1.2:.1f}L{x + r:.1f},{y:.1f}L{x:.1f},{y + r * 1.2:.1f}'
                f'L{x - r:.1f},{y:.1f}Z" fill="{fill}" stroke="{color}" stroke-width="{width}"/>')
    pts = []
    for i in range(10):
        a = math.pi / 2 + i * math.pi / 5
        rr = r * 1.3 if i % 2 == 0 else r * 0.55
        pts.append(f"{x + rr * math.cos(a):.1f},{y - rr * math.sin(a):.1f}")
    return f'<path d="M{"L".join(pts)}Z" fill="{fill}" stroke="{color}" stroke-width="{width}"/>'


def history(rates, meta):
    W, H = 960, 690
    X0, X1, Y0, Y1 = 86, 690, 92, 584
    values = [v for row in rates.values() for v in row.values() if v > 0]
    lo = math.floor(math.log10(min(values)))
    hi = math.ceil(math.log10(max(values))) + 1  # an empty top decade holds the caption
    xs = lambda n: X0 + (math.log10(n) - 1) / 4 * (X1 - X0)
    ys = lambda v: Y1 - (math.log10(v) - lo) / (hi - lo) * (Y1 - Y0)
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" '
           f'font-family="Helvetica, Arial, sans-serif">',
           f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
           f'<text x="{W / 2}" y="30" text-anchor="middle" font-size="19" font-weight="bold" '
           f'fill="#222">Exact stochastic simulation: events per second vs network size</text>',
           f'<text x="{W / 2}" y="52" text-anchor="middle" font-size="12.5" fill="#555">'
           f'Catalyst-paper networks · JumpProcesses.jl 9.33.1 aggregators (static) · '
           f'Lean Tree-RSSA generations, each proved equal to its specification (animated)</text>']
    out.append('<g stroke="#e3e3e3" stroke-width="0.9">')
    for d in range(lo, hi + 1):
        out.append(f'<line x1="{X0}" x2="{X1}" y1="{ys(10 ** d):.1f}" y2="{ys(10 ** d):.1f}"/>')
    for d in range(1, 6):
        out.append(f'<line x1="{xs(10 ** d):.1f}" x2="{xs(10 ** d):.1f}" y1="{Y0}" y2="{Y1}"/>')
    out.append("</g>")
    out.append('<g font-size="13" fill="#555" font-family="Menlo, Consolas, monospace">')
    names = {0: "1", 1: "10", 2: "100", 3: "1k", 4: "10k", 5: "100k", 6: "1M", 7: "10M",
             8: "100M", 9: "1G"}
    for d in range(lo, hi + 1):
        out.append(f'<text x="{X0 - 8}" y="{ys(10 ** d) + 4.5:.1f}" text-anchor="end">'
                   f'{names.get(d, f"1e{d}")}</text>')
    for d in range(1, 6):
        out.append(f'<text x="{xs(10 ** d):.1f}" y="{Y1 + 18}" text-anchor="middle">'
                   f'{names[d]}</text>')
    out.append("</g>")
    for model, n in MODELS:
        out.append(f'<text x="{xs(n):.1f}" y="{Y1 + 34}" text-anchor="middle" font-size="11" '
                   f'fill="#777">{LABEL[model]}</text>')
    out.append(f'<rect x="{X0}" y="{Y0}" width="{X1 - X0}" height="{Y1 - Y0}" fill="none" '
               f'stroke="#cccccc"/>')
    out.append(f'<text x="{(X0 + X1) / 2}" y="{Y1 + 54}" text-anchor="middle" font-size="14.5" '
               f'fill="#222">reactions in the network (log)</text>')
    out.append(f'<text transform="translate(26 {(Y0 + Y1) / 2}) rotate(-90)" text-anchor="middle" '
               f'font-size="14.5" fill="#222">simulated events per second (log)</text>')

    def series(key):
        pts = [(xs(n), ys(rates[m][key])) for m, n in MODELS if rates[m].get(key, 0) > 0]
        return pts

    def path(pts):
        return "M" + "L".join(f"{x:.1f},{y:.1f}" for x, y in pts)

    # verified FloatLib drivers and the port: static Lean references
    for key, dash, color, label in [
            ("lean:c-reference", "1,2.5", "#222222", None),
            ("lean:direct-floatlib", "2,3", "#b0b0b0", None),
            ("lean:nrm-floatlib", "2,3", "#b0b0b0", None),
            ("lean:rssa-floatlib", "2,3", "#b0b0b0", None),
            ("lean:rssacr-port", "6,4", "#555555", None)]:
        pts = series(key)
        if len(pts) > 1:
            out.append(f'<path d="{path(pts)}" fill="none" stroke="{color}" stroke-width="1.6" '
                       f'stroke-dasharray="{dash}"/>')
            for x, y in pts:
                out.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="2.6" fill="{color}"/>')
    for name, color, shape in JULIA:
        pts = series("julia:" + name)
        if len(pts) > 1:
            width = 2.2 if name == "RSSACR" else 1.3
            out.append(f'<path d="{path(pts)}" fill="none" stroke="{color}" stroke-width="{width}" '
                       f'opacity="0.9"/>')
            for x, y in pts:
                out.append(marker(shape, x, y, color))
    # the animation: generation k is shown during segment k
    gens = [(key, title) for key, title in GENERATIONS
            if all(rates[m].get("lean:" + key, 0) > 0 for m, _ in MODELS)]
    if not gens:
        gens = []
    hold, move, final = 1.7, 0.5, 4.0
    if not gens:
        out.append("</svg>")
        return "\n".join(out) + "\n"
    dur = len(gens) * hold + (len(gens) - 1) * move + final
    times, frames = [0.0], [0]
    t = 0.0
    for k in range(len(gens)):
        t += hold if k < len(gens) - 1 else hold + final
        times.append(t)
        frames.append(k)
        if k < len(gens) - 1:
            t += move
            times.append(t)
            frames.append(k + 1)
    key_times = ";".join(f"{x / dur:.5f}" for x in times)
    gen_pts = [series("lean:" + key) for key, _ in gens]
    # trails: generation k fades in once the curve leaves it
    for k, pts in enumerate(gen_pts[:-1]):
        opac = ";".join("0.32" if f > k else "0" for f in frames)
        out.append(f'<path d="{path(pts)}" fill="none" stroke="{TREE}" stroke-width="1.4" '
                   f'opacity="0"><animate attributeName="opacity" values="{opac}" '
                   f'keyTimes="{key_times}" dur="{dur:.1f}s" repeatCount="indefinite" '
                   f'calcMode="discrete"/></path>')
    dvals = ";".join(path(gen_pts[f]) for f in frames)
    out.append(f'<path d="{path(gen_pts[0])}" fill="none" stroke="{TREE}" stroke-width="3.2">'
               f'<animate attributeName="d" values="{dvals}" keyTimes="{key_times}" '
               f'dur="{dur:.1f}s" repeatCount="indefinite" calcMode="linear"/></path>')
    for i in range(len(MODELS)):
        cy = ";".join(f"{gen_pts[f][i][1]:.1f}" for f in frames)
        out.append(f'<circle cx="{gen_pts[0][i][0]:.1f}" cy="{gen_pts[0][i][1]:.1f}" r="5.6" '
                   f'fill="{TREE}"><animate attributeName="cy" values="{cy}" '
                   f'keyTimes="{key_times}" dur="{dur:.1f}s" repeatCount="indefinite" '
                   f'calcMode="linear"/></circle>')
    # captions: generation title and geometric-mean ratio to the fastest Julia aggregator
    best_julia = {m: max([v for k, v in rates[m].items() if k.startswith("julia:")] or [1])
                  for m, _ in MODELS}
    def geomean(xs):
        xs = list(xs)
        return math.exp(sum(math.log(x) for x in xs) / len(xs))

    def versus(r):
        if r >= 0.1:
            return f"{r:.2f}× the speed of the fastest Julia aggregator"
        return f"1/{1 / r:,.0f} of the speed of the fastest Julia aggregator"

    for k, (key, title) in enumerate(gens):
        ratio = geomean(rates[m]["lean:" + key] / best_julia[m] for m, _ in MODELS)
        gain = geomean(rates[m]["lean:" + key] / rates[m]["lean:" + gens[0][0]]
                       for m, _ in MODELS)
        opac = ";".join("1" if f == k else "0" for f in frames)
        out.append(f'<g opacity="0"><animate attributeName="opacity" values="{opac}" '
                   f'keyTimes="{key_times}" dur="{dur:.1f}s" repeatCount="indefinite" '
                   f'calcMode="discrete"/>'
                   f'<text x="{X0 + 12}" y="{Y0 + 18}" font-size="15" font-weight="bold" '
                   f'fill="{TREE}">Tree-RSSA generation {k}</text>'
                   f'<text x="{X0 + 12}" y="{Y0 + 34}" font-size="12" fill="#333">{title}</text>'
                   f'<text x="{X0 + 12}" y="{Y0 + 49}" font-size="12" fill="#333">'
                   f'{versus(ratio) + (f"; {gain:,.0f}× generation 0" if k else "")}'
                   f' (geometric mean{"s" if k else ""})</text></g>')
    # legend
    LX, LY = X1 + 22, Y0 + 6
    out.append(f'<g font-size="12.5" fill="#222">')
    out.append(f'<text x="{LX}" y="{LY}" font-weight="bold">Lean (this repository)</text>')
    LY += 20
    out.append(f'<line x1="{LX}" x2="{LX + 26}" y1="{LY - 4}" y2="{LY - 4}" stroke="{TREE}" '
               f'stroke-width="3.2"/><circle cx="{LX + 13}" cy="{LY - 4}" r="4.5" fill="{TREE}"/>'
               f'<text x="{LX + 34}" y="{LY}">Tree-RSSA (proved)</text>')
    LY += 20
    out.append(f'<line x1="{LX}" x2="{LX + 26}" y1="{LY - 4}" y2="{LY - 4}" stroke="#555" '
               f'stroke-width="1.6" stroke-dasharray="6,4"/>'
               f'<text x="{LX + 34}" y="{LY}">RSSACR port</text>')
    LY += 20
    out.append(f'<line x1="{LX}" x2="{LX + 26}" y1="{LY - 4}" y2="{LY - 4}" stroke="#b0b0b0" '
               f'stroke-width="1.6" stroke-dasharray="2,3"/>'
               f'<text x="{LX + 34}" y="{LY}">verified FloatLib</text>'
               f'<text x="{LX + 34}" y="{LY + 15}" fill="#777" font-size="11">Direct, NRM, RSSA</text>')
    LY += 36
    out.append(f'<line x1="{LX}" x2="{LX + 26}" y1="{LY - 4}" y2="{LY - 4}" stroke="#222" '
               f'stroke-width="1.6" stroke-dasharray="1,2.5"/>'
               f'<text x="{LX + 34}" y="{LY}">same algorithm in C</text>'
               f'<text x="{LX + 34}" y="{LY + 15}" fill="#777" font-size="11">unverified cross-check</text>')
    LY += 42
    out.append(f'<text x="{LX}" y="{LY}" font-weight="bold">JumpProcesses.jl</text>')
    for name, color, shape in JULIA:
        LY += 20
        out.append(marker(shape, LX + 13, LY - 4, color) +
                   f'<line x1="{LX}" x2="{LX + 26}" y1="{LY - 4}" y2="{LY - 4}" stroke="{color}" '
                   f'stroke-width="{2.2 if name == "RSSACR" else 1.3}"/>'
                   f'<text x="{LX + 34}" y="{LY}">{name}</text>')
    out.append("</g>")
    m = meta["generations"] or meta["lean"]
    out.append(f'<text x="{W / 2}" y="{H - 26}" text-anchor="middle" font-size="9.5" '
               f'fill="#777">{m.get("cpu", "")} · Julia 1.11.7, SSAStepper, scale_rates=false · '
               f'Lean 4.34.0 · best repetition per measurement, spans in bench/run.py · '
               f'lean @ {m.get("commit", "")[:8]} · {m.get("date", "")[:10]}</text>')
    out.append(f'<text x="{W / 2}" y="{H - 12}" text-anchor="middle" font-size="9.5" '
               f'fill="#777">every Tree-RSSA generation returns bit-for-bit the same trajectory as '
               f'the specification (Lean theorems genK_simulate_eq); its law is proved in the reals'
               f'</text>')
    out.append("</svg>")
    return "\n".join(out) + "\n"


def generations_svg(rates):
    W, H = 900, 560
    X0, X1, Y0, Y1 = 80, 700, 60, 470
    gens = [key for key, _ in GENERATIONS]
    colors = ["#4c72b0", "#55a868", "#dd8452", "#8172b2", "#c44e52"]
    values = [rates[m].get("lean:" + g, 0) for m, _ in MODELS for g in gens]
    values += [max([v for k, v in rates[m].items() if k.startswith("julia:")] or [0])
               for m, _ in MODELS]
    values = [v for v in values if v > 0]
    lo, hi = math.floor(math.log10(min(values))), math.ceil(math.log10(max(values)))
    xs = lambda i: X0 + i / (len(gens) - 1) * (X1 - X0)
    ys = lambda v: Y1 - (math.log10(v) - lo) / (hi - lo) * (Y1 - Y0)
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" '
           f'font-family="Helvetica, Arial, sans-serif">',
           f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
           f'<text x="{W / 2}" y="30" text-anchor="middle" font-size="18" font-weight="bold" '
           f'fill="#222">Tree-RSSA throughput by generation</text>',
           '<g stroke="#e3e3e3" stroke-width="0.9">']
    for d in range(lo, hi + 1):
        out.append(f'<line x1="{X0}" x2="{X1}" y1="{ys(10 ** d):.1f}" y2="{ys(10 ** d):.1f}"/>')
    out.append("</g>")
    out.append('<g font-size="12.5" fill="#555" font-family="Menlo, Consolas, monospace">')
    names = {0: "1", 1: "10", 2: "100", 3: "1k", 4: "10k", 5: "100k", 6: "1M", 7: "10M",
             8: "100M", 9: "1G"}
    for d in range(lo, hi + 1):
        out.append(f'<text x="{X0 - 8}" y="{ys(10 ** d) + 4:.1f}" text-anchor="end">'
                   f'{names.get(d, f"1e{d}")}</text>')
    for i in range(len(gens)):
        out.append(f'<text x="{xs(i):.1f}" y="{Y1 + 18}" text-anchor="middle">{i}</text>')
    out.append("</g>")
    out.append(f'<rect x="{X0}" y="{Y0}" width="{X1 - X0}" height="{Y1 - Y0}" fill="none" '
               f'stroke="#cccccc"/>')
    out.append(f'<text x="{(X0 + X1) / 2}" y="{Y1 + 42}" text-anchor="middle" font-size="14" '
               f'fill="#222">generation (0 = specification)</text>')
    out.append(f'<text transform="translate(24 {(Y0 + Y1) / 2}) rotate(-90)" text-anchor="middle" '
               f'font-size="14" fill="#222">events per second (log)</text>')
    LY = Y0 + 10
    for (model, _), color in zip(MODELS, colors):
        pts = [(xs(i), ys(rates[model]["lean:" + g])) for i, g in enumerate(gens)
               if rates[model].get("lean:" + g, 0) > 0]
        if not pts:
            continue
        out.append(f'<path d="M{"L".join(f"{x:.1f},{y:.1f}" for x, y in pts)}" fill="none" '
                   f'stroke="{color}" stroke-width="2.4"/>')
        for x, y in pts:
            out.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="3.6" fill="{color}"/>')
        jb = max([v for k, v in rates[model].items() if k.startswith("julia:")] or [0])
        if jb <= 0:
            continue
        out.append(f'<line x1="{X0}" x2="{X1}" y1="{ys(jb):.1f}" y2="{ys(jb):.1f}" stroke="{color}" '
                   f'stroke-width="1.2" stroke-dasharray="5,4" opacity="0.8"/>')
        out.append(f'<line x1="{X1 + 20}" x2="{X1 + 44}" y1="{LY}" y2="{LY}" stroke="{color}" '
                   f'stroke-width="2.4"/><text x="{X1 + 52}" y="{LY + 4}" font-size="12.5" '
                   f'fill="#222">{LABEL[model]}</text>')
        LY += 22
    out.append(f'<line x1="{X1 + 20}" x2="{X1 + 44}" y1="{LY + 6}" y2="{LY + 6}" stroke="#666" '
               f'stroke-width="1.2" stroke-dasharray="5,4"/><text x="{X1 + 52}" y="{LY + 10}" '
               f'font-size="12" fill="#222">fastest Julia</text>'
               f'<text x="{X1 + 52}" y="{LY + 25}" font-size="12" fill="#222">aggregator</text>')
    out.append("</svg>")
    return "\n".join(out) + "\n"


def head_to_head():
    """Same-window comparison: best Julia aggregator vs Lean, from headtohead.json."""
    h2h = load("headtohead")["results"]
    rows = {}
    for model, _ in MODELS:
        rec = h2h.get(model, {})
        julia = {k: v["events_per_second"] for k, v in rec.items()
                 if isinstance(v, dict) and k.startswith("julia:")}
        if not julia:
            continue
        best = max(julia, key=julia.get)
        rows[model] = {"best_julia": best, "julia": julia[best],
                       "lean": rec.get("treerssa-g10", {}).get("events_per_second", 0),
                       "c": rec.get("c-reference", {}).get("events_per_second", 0),
                       "port": rec.get("rssacr-port", {}).get("events_per_second", 0)}
    return rows


def head_to_head_svg(rows):
    W, H = 900, 470
    X0, X1, Y0, Y1 = 90, 860, 70, 380
    series = [("lean", "Lean Tree-RSSA, generation 10 (proved)", TREE),
              ("c", "same algorithm in C (unverified)", "#444444"),
              ("port", "Lean port of RSSACR", "#999999")]
    ratios = [r[k] / r["julia"] for r in rows.values() for k, _, _ in series if r[k] > 0]
    top = max(1.5, math.ceil(max(ratios + [1]) * 4) / 4)
    ys = lambda v: Y1 - v / top * (Y1 - Y0)
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" '
           f'font-family="Helvetica, Arial, sans-serif">',
           f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
           f'<text x="{W / 2}" y="30" text-anchor="middle" font-size="18" font-weight="bold" '
           f'fill="#222">Head to head, same machine, same time window</text>',
           f'<text x="{W / 2}" y="50" text-anchor="middle" font-size="12.5" fill="#555">'
           f'throughput relative to the fastest JumpProcesses.jl aggregator on each network '
           f'(RSSA, RSSACR or SortingDirect), best of alternating rounds</text>']
    t = 0.0
    while t <= top + 1e-9:
        out.append(f'<line x1="{X0}" x2="{X1}" y1="{ys(t):.1f}" y2="{ys(t):.1f}" '
                   f'stroke="{"#888" if abs(t - 1) < 1e-9 else "#e3e3e3"}" '
                   f'stroke-width="{1.4 if abs(t - 1) < 1e-9 else 0.9}"/>'
                   f'<text x="{X0 - 8}" y="{ys(t) + 4:.1f}" text-anchor="end" font-size="12" '
                   f'fill="#555">{t:.2f}×</text>')
        t += 0.25
    n = len(rows)
    gw = (X1 - X0) / max(n, 1)
    bw = gw / (len(series) + 1.5)
    for i, (model, r) in enumerate(rows.items()):
        gx = X0 + i * gw + bw * 0.75
        for j, (key, _, color) in enumerate(series):
            if r[key] <= 0:
                continue
            v = r[key] / r["julia"]
            x = gx + j * bw
            out.append(f'<rect x="{x:.1f}" y="{ys(v):.1f}" width="{bw * 0.9:.1f}" '
                       f'height="{Y1 - ys(v):.1f}" fill="{color}"/>'
                       f'<text x="{x + bw * 0.45:.1f}" y="{ys(v) - 5:.1f}" text-anchor="middle" '
                       f'font-size="11" fill="#333">{v:.2f}</text>')
        out.append(f'<text x="{X0 + i * gw + gw / 2:.1f}" y="{Y1 + 20}" text-anchor="middle" '
                   f'font-size="13" fill="#222">{LABEL[model]}</text>'
                   f'<text x="{X0 + i * gw + gw / 2:.1f}" y="{Y1 + 36}" text-anchor="middle" '
                   f'font-size="11" fill="#777">vs {r["best_julia"].split(":")[1]} '
                   f'{r["julia"]:.3g}/s</text>')
    for (key, label, color), LX in zip(series, [X0, X0 + 330, X0 + 600]):
        out.append(f'<rect x="{LX}" y="{H - 34}" width="14" height="14" fill="{color}"/>'
                   f'<text x="{LX + 20}" y="{H - 22}" font-size="12.5" fill="#222">{label}</text>')
    out.append("</svg>")
    return "\n".join(out) + "\n"


def summary(rates, meta):
    lines = ["# Benchmark results", "",
             "Events per second, best repetition. Julia: JumpProcesses.jl 9.33.1 on Julia 1.11.7. "
             "Lean: this repository.", ""]
    cols = [m for m, _ in MODELS]
    lines.append("| method | " + " | ".join(cols) + " |")
    lines.append("|---|" + "---:|" * len(cols))
    keys = [("julia:" + n, f"Julia {n}") for n, _, _ in JULIA]
    keys += [("lean:" + k, f"Lean Tree-RSSA G{i}") for i, (k, _) in enumerate(GENERATIONS)]
    keys += [("lean:c-reference", "Tree-RSSA in C (unverified cross-check)"),
             ("lean:rssacr-port", "Lean RSSACR port"),
             ("lean:direct-floatlib", "Lean FloatLib Direct"),
             ("lean:nrm-floatlib", "Lean FloatLib NRM"),
             ("lean:rssa-floatlib", "Lean FloatLib RSSA")]
    for key, label in keys:
        cells = [f"{rates[m][key]:.3g}" if rates[m].get(key, 0) > 0 else "–" for m in cols]
        lines.append(f"| {label} | " + " | ".join(cells) + " |")
    rows = head_to_head()
    if rows:
        lines += ["", "## Head to head (same window, alternating rounds, best time)", "",
                  "| network | fastest Julia | Julia ev/s | Lean G10 ev/s | ratio | C ev/s | "
                  "Lean RSSACR port ev/s |", "|---|---|---:|---:|---:|---:|---:|"]
        for model, r in rows.items():
            lines.append(f"| {LABEL[model]} | {r['best_julia'].split(':')[1]} | {r['julia']:.3g} | "
                         f"{r['lean']:.3g} | {r['lean'] / r['julia']:.2f} | {r['c']:.3g} | "
                         f"{r['port']:.3g} |")
    lines += ["", "Machine: " + json.dumps(meta)]
    return "\n".join(lines) + "\n"


def main():
    rates, meta = collect()
    (RES / "history.svg").write_text(history(rates, meta))
    (RES / "generations.svg").write_text(generations_svg(rates))
    (RES / "summary.md").write_text(summary(rates, meta))
    rows = head_to_head()
    if rows:
        (RES / "headtohead.svg").write_text(head_to_head_svg(rows))
    print("wrote", RES / "history.svg", RES / "generations.svg", RES / "summary.md")


if __name__ == "__main__":
    main()
