"""Fetch every manifest revision explicitly before Lake loads dependencies."""
import json
import pathlib
import subprocess

root = pathlib.Path(__file__).resolve().parent.parent
manifest = json.loads((root / "lake-manifest.json").read_text())
for package in manifest["packages"]:
    if package["type"] != "git":
        continue
    destination = root / manifest["packagesDir"] / package["name"]
    if not (destination / ".git").exists():
        destination.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "init", "--quiet", str(destination)], check=True)
        subprocess.run(["git", "-C", str(destination), "remote", "add", "origin", package["url"]], check=True)
    revision = package["rev"]
    result = subprocess.run(["git", "-C", str(destination), "cat-file", "-e", revision + "^{commit}"],
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if result.returncode:
        subprocess.run(["git", "-C", str(destination), "fetch", "--depth=1", "origin", revision], check=True)
    subprocess.run(["git", "-C", str(destination), "checkout", "--quiet", "--detach", revision], check=True)
    print(f"Pinned {package['name']}: {revision}", flush=True)
