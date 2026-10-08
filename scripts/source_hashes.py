"""Record SHA-256 hashes of every tracked source file and the pinned revisions."""
import hashlib
import json
import pathlib
import subprocess

root = pathlib.Path(__file__).resolve().parent.parent
tracked = subprocess.run(["git", "-C", str(root), "ls-files"], capture_output=True, text=True,
                         check=True).stdout.split()
manifest = json.loads((root / "lake-manifest.json").read_text())
revisions = {package["name"]: package["rev"] for package in manifest["packages"]}
toolchain = (root / "lean-toolchain").read_text().strip().split(":v")[-1]
record = {
    "revisions": {
        "JumpProcesses.jl": "3c8c8edc8d8a84c47a7200064ab1f2fedd2ee22d",
        "FloatLib": revisions["floatlib"],
        "mathlib": revisions["mathlib"],
        "Lean": toolchain,
    },
    "files": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in sorted(tracked) if not name.startswith("results/")
    },
}
(root / "results" / "source-sha256.json").write_text(json.dumps(record, indent=2) + "\n")
print(f"Recorded {len(record['files'])} source hashes")
