"""Convert a BioNetGen `.net` reaction network into the plain mass-action `.rn` format.

The `.rn` format is read by both the Lean and the Julia benchmark drivers, so every method
simulates exactly the same network:

    jprn 1
    species <S>
    <S initial populations, one line, space separated>
    reactions <M>
    <rate bits> <r> <s_1> <nu_1> ... <s_r> <nu_r> <c> <s_1> <d_1> ... <s_c> <d_c>   (M lines)

`rate bits` is the IEEE binary64 bit pattern of the rate constant in hexadecimal, so the
two drivers decode identical constants. Species are 0-based. The reactant list gives each
distinct reactant species with its stoichiometry; the change list gives the net change of
every species whose population changes.

Propensities follow BioNetGen's convention for `.net` files: the rate constant already
contains the statistical factors, and the propensity is
`k * prod_s n_s (n_s - 1) ... (n_s - nu_s + 1)` (JumpProcesses `scale_rates = false`).
"""
import ast
import hashlib
import operator
import pathlib
import struct
import sys

BINARY = {ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul,
          ast.Div: operator.truediv, ast.Pow: operator.pow}


def evaluate(expression, env):
    """Evaluate a BioNetGen arithmetic expression over previously defined parameters."""
    tree = ast.parse(expression.replace("^", "**"), mode="eval")

    def go(node):
        if isinstance(node, ast.Expression):
            return go(node.body)
        if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)):
            return float(node.value)
        if isinstance(node, ast.Name):
            return env[node.id]
        if isinstance(node, ast.BinOp) and type(node.op) in BINARY:
            return BINARY[type(node.op)](go(node.left), go(node.right))
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
            value = go(node.operand)
            return -value if isinstance(node.op, ast.USub) else value
        raise ValueError(f"unsupported expression: {expression}")

    return go(tree)


def sections(text):
    current, blocks = None, {}
    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith("begin "):
            current = line[len("begin "):].strip()
            blocks[current] = []
        elif line.startswith("end "):
            current = None
        elif current is not None:
            blocks[current].append(line.split())
    return blocks


def species_list(field):
    return [] if field == "0" else [int(s) - 1 for s in field.split(",")]


def convert(path):
    text = pathlib.Path(path).read_text()
    blocks = sections(text)
    env = {}
    for fields in blocks.get("parameters", []):
        env[fields[1]] = evaluate(fields[2], env)
    populations = []
    for fields in blocks["species"]:
        value = evaluate(fields[2], env)
        if value < 0 or value != int(value):
            raise ValueError(f"non-integer initial population {value} for {fields[1]}")
        populations.append(int(value))
    reactions = []
    for fields in blocks["reactions"]:
        reactants, products = species_list(fields[1]), species_list(fields[2])
        rate = evaluate(fields[3], env)
        if rate < 0:
            raise ValueError(f"negative rate constant in reaction {fields[0]}")
        stoich = {}
        for s in reactants:
            stoich[s] = stoich.get(s, 0) + 1
        change = {}
        for s in reactants:
            change[s] = change.get(s, 0) - 1
        for s in products:
            change[s] = change.get(s, 0) + 1
        reactions.append((rate, sorted(stoich.items()), sorted((s, d) for s, d in change.items() if d)))
    return populations, reactions, hashlib.sha256(text.encode()).hexdigest()


def write(populations, reactions, destination):
    lines = ["jprn 1", f"species {len(populations)}", " ".join(map(str, populations)),
             f"reactions {len(reactions)}"]
    for rate, stoich, change in reactions:
        bits = struct.unpack("<Q", struct.pack("<d", rate))[0]
        parts = [f"{bits:016x}", str(len(stoich))]
        for s, nu in stoich:
            parts += [str(s), str(nu)]
        parts.append(str(len(change)))
        for s, d in change:
            parts += [str(s), str(d)]
        lines.append(" ".join(parts))
    pathlib.Path(destination).write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("usage: net2rn.py <input.net> <output.rn>")
    populations, reactions, digest = convert(sys.argv[1])
    write(populations, reactions, sys.argv[2])
    print(f"{pathlib.Path(sys.argv[1]).name}: {len(populations)} species, {len(reactions)} reactions, "
          f"sha256 {digest[:12]}")
