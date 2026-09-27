#!/bin/sh
set -eu

source_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build_dir=${HTN_LEAN_BUILD_DIR:-"${XDG_CACHE_HOME:-$HOME/Library/Caches}/heavy-tailed-noise-lean4/project"}
if [ "$#" -eq 0 ]; then
  set -- HeavyTailedNoise
fi
PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
export PATH
lean_threads=${LEAN_NUM_THREADS:-1}

mkdir -p "$build_dir"
python3 - "$source_dir" "$build_dir" <<'PY'
from pathlib import Path
import shutil
import sys

source_dir, build_dir = map(Path, sys.argv[1:])
inputs = [source_dir / name for name in
          ("HeavyTailedNoise.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json")]
inputs += sorted((source_dir / "HeavyTailedNoise").rglob("*.lean"))
expected = {source.relative_to(source_dir) for source in inputs}
# Project sources in this generated cache have exactly one authoritative owner.
for cached_source in (build_dir / "HeavyTailedNoise").rglob("*.lean"):
    if cached_source.relative_to(build_dir) not in expected:
        cached_source.unlink()
for source in inputs:
    destination = build_dir / source.relative_to(source_dir)
    destination.parent.mkdir(parents=True, exist_ok=True)
    if not destination.exists() or destination.read_bytes() != source.read_bytes():
        shutil.copy2(source, destination)
print(f"Prepared {sum(p.suffix == '.lean' for p in inputs)} modules with canonical configuration")
PY

cd "$build_dir"
if [ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]; then
  env -u LEAN_PATH -u LEAN_SRC_PATH LEAN_NUM_THREADS="$lean_threads" \
    lake --reconfigure exe cache get
fi
exec env -u LEAN_PATH -u LEAN_SRC_PATH LEAN_NUM_THREADS="$lean_threads" \
  lake --reconfigure build "$@"
