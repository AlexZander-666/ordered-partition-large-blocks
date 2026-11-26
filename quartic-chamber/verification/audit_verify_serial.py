"""Cold verification entry point for the frozen original entire cubic chamber source package."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

base = Path(__file__).resolve().parent
jobs = int(sys.argv[2]) if len(sys.argv) > 2 else 2
if jobs < 1:
    raise ValueError("Replay worker count must be positive")
packages = Path(sys.argv[1]).resolve(strict=True)
os.chdir(base)
for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
    os.environ.pop(key, None)
os.environ["LEAN_NUM_THREADS"] = "1"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def output(*cmd):
    return subprocess.check_output(cmd, text=True, stderr=subprocess.STDOUT)


entries = Path("SOURCE-SHA256SUMS").read_text().splitlines()
for entry in entries:
    sha, name = entry.split("  ", 1)
    if digest(Path(name)) != sha:
        raise ValueError(f"source digest mismatch: {name}")
mods = Path("modules.txt").read_text().splitlines()
seen = set()
blocked = re.compile(r"\b(sorry|sorryAx|admit|native_decide|axiom|unsafe|implemented_by|extern|ofReduceBool|trustCompiler|run_tac)\b")
for mod in mods:
    path = Path(mod.replace(".", "/") + ".lean")
    source = path.read_text()
    if blocked.search(source):
        raise ValueError(f"forbidden proof construct in {path}")
    children = set(re.findall(r"^import (OrderedPartitions\.[\w.]+)$", source, re.M))
    if not children.issubset(seen) or mod in seen:
        raise ValueError(f"incomplete or unordered closure: {mod}")
    seen.add(mod)
actual = {str(p.with_suffix("")).replace("/", ".") for p in Path("OrderedPartitions").rglob("*.lean")}
if seen != actual or mods[-1] != "OrderedPartitions.CubicChamberVerified":
    raise ValueError("local module manifest disagrees with source")
for dep in json.loads(Path("lake-manifest.json").read_text())["packages"]:
    repo = packages / dep["name"]
    sha = output("git", "-C", repo, "rev-parse", "HEAD").strip()
    if sha != dep["rev"] or output("git", "-C", repo, "status", "--porcelain", "--untracked-files=no").strip():
        raise ValueError(f"dependency mismatch: {repo}")
    print("locked-dependency", dep["name"], sha, flush=True)
Path(".lake").mkdir(exist_ok=False)
Path(".lake/packages").symlink_to(packages, target_is_directory=True)
version = output("lean", "--version").strip()
if "version 4.33.1" not in version or "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" not in version:
    raise ValueError("Unexpected Lean release")
print(version, flush=True)
print("Initial project objects: 0", flush=True)
build_env = dict(os.environ, LEAN_NUM_THREADS=str(min(jobs, 4)))
for build_module in mods:
    print("serial_build_target=" + build_module, flush=True)
    subprocess.run(["lake", "--no-ansi", "--quiet", "--wfail", "build", "+" + build_module],
                   check=True, env=build_env)
    print("serial_build_exit=0 " + build_module, flush=True)
print("strict_build_exit=0", flush=True)

allowed = {"propext", "Classical.choice", "Quot.sound"}
def replay(mod):
    path = Path(mod.replace(".", "/") + ".lean")
    expected = re.findall(r"^#print axioms\s+(\S+)\s*$", path.read_text(), re.M)
    result = output("lake", "env", "lean", "-DwarningAsError=true", str(path)) if expected else ""
    found = re.findall(r"^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\s*$",
                       result, re.M)
    if len(found) != len(expected):
        raise ValueError(f"incomplete axiom output in {mod}")
    for requested, (name, axioms) in zip(expected, found):
        if name != requested and not name.endswith("." + requested):
            raise ValueError(f"expected {requested}, found {name}")
        actual_axioms = {a.strip() for a in axioms.split(",") if a.strip()}
        if not actual_axioms.issubset(allowed):
            raise ValueError(f"unexpected axioms for {name}: {actual_axioms}")
    checker = output("lake", "env", "leanchecker", "--verbose", mod)
    obj = Path(".lake/build/lib/lean") / path.with_suffix(".olean")
    line = "kernel_replay_exit=0 " + mod + " source_sha256=" + digest(path) + " object_sha256=" + digest(obj)
    return result + checker + line + "\n", len(found)


axiom_prints = 0
with ThreadPoolExecutor(max_workers=jobs) as workers:
    for log, count in workers.map(replay, mods):
        axiom_prints += count
        print(log, end="", flush=True)

expected = [f"OrderedPartitions.CubicFinite.cutoff{j:02}" for j in range(2, 64)]
extra = Path("AuditCutoffs.lean")
extra.write_text("import OrderedPartitions.CubicChamberVerified\n" + "".join(
    "#print axioms " + name + "\n" for name in expected))
results = output("lake", "env", "lean", "-DwarningAsError=true", str(extra))
found = re.findall(r"^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\s*$",results,re.M)
assert len(found)==len(expected)
for name,(actual,deps) in zip(expected,found,strict=True):
    assert name==actual
    assert {s.strip() for s in deps.split(",") if s.strip()} <= allowed
print(results, end="", flush=True)
print("PASS 62 standalone cubic finite-cutoff axiom reports", flush=True)
for entry in entries:
    sha, name = entry.split("  ", 1)
    if digest(Path(name)) != sha:
        raise ValueError(f"source changed during verification: {name}")
print(f"PASS {len(mods)} cold project modules, {len(mods)} independent kernel replays, "
      f"{axiom_prints} transitive axiom printouts", flush=True)
