#!/usr/bin/env bash
# Point this project's dependencies at an existing, already-built checkout of
# leanprover-community/riemann-hypothesis (package `tree`), so that nothing is rebuilt.
#
#   1. git clone https://github.com/leanprover-community/riemann-hypothesis.git ARCHIVE
#      git -C ARCHIVE checkout 23aebbb302010b292314d406aa97f7901d698634
#   2. in ARCHIVE, follow its README:  lake exe cache get && lake build --no-build
#   3. bash scripts/link-archive-cache.sh ARCHIVE
#
# The archive's .lake/build is about 100 GB, so we symlink instead of copying.
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")/.." && pwd)
archive=$(realpath -- "${1:?usage: link-archive-cache.sh ARCHIVE_DIR}")

python3 - "$here/lake-manifest.json" "$archive" <<'PY'
import json, subprocess, sys
manifest, archive = sys.argv[1], sys.argv[2]
for p in json.load(open(manifest))["packages"]:
    d = archive if p["name"] == "tree" else f"{archive}/.lake/packages/{p['name']}"
    rev = subprocess.run(["git", "-C", d, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    if rev != p["rev"]:
        sys.exit(f"revision mismatch for {p['name']}: archive has {rev or 'nothing'}, manifest wants {p['rev']}")
print("all dependency revisions match the manifest")
PY

mkdir -p "$here/.lake/packages"
ln -sfn "$archive" "$here/.lake/packages/tree"
for d in "$archive"/.lake/packages/*/; do
  name=$(basename "$d")
  ln -sfn "$archive/.lake/packages/$name" "$here/.lake/packages/$name"
done
echo "linked .lake/packages -> $archive"
