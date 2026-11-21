#!/usr/bin/env bash
# Full independent check of the K₄ₘ(ℤ) bound against Mathlib and the RH archive.
#
#   bash run.sh            # all stages: tools, challenge, solution, judge
#   bash run.sh STAGE      # one of: tools challenge solution judge conleche
#
# Environment:
#   WORK=...           working directory (default: ./work next to this script)
#   ARCHIVE=...        existing checkout of the RH archive at the pinned commit (optional;
#                      default: cloned into $WORK/archive)
#   FROM_SOURCE=1      build the archive's proof closure from source instead of downloading
#                      its community cache (days of CPU; the judge re-checks proofs anyway)
#
# Requirements: elan, git, curl, about 100 GB RAM and 200 GB disk (archive cache ~100 GB,
# solution export ~60 GB). Mirrors the archive's own procedure
# (github.com/leanprover-community/riemann-hypothesis, README "Checking it") and
# https://math.mit.edu/~drew/grh/.
set -euo pipefail

HERE=$(cd -- "$(dirname -- "$0")" && pwd)
REPO=$(dirname -- "$HERE")
WORK=${WORK:-$HERE/work}
ARCHIVE=${ARCHIVE:-$WORK/archive}
ARCHIVE_URL=https://github.com/leanprover-community/riemann-hypothesis.git
ARCHIVE_REV=23aebbb302010b292314d406aa97f7901d698634
CORGK=Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.CorGKOf
LEAN_BUILD=leanprover/lean4:v4.33.1      # builds and exports (the archive's toolchain)
LEAN_JUDGE=leanprover/lean4:v4.36.0      # lake comparator and its kernels
LEAN4EXPORT_TAG=v4.33.0                  # 15f6055e, built with Lean v4.33.1
LEAN4EXPORT=$WORK/tools/lean4export/.lake/build/bin/lean4export

export LEAN_ABORT_ON_PANIC=1
export MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4

mkdir -p "$WORK"
log() { printf '\n=== %s ===\n' "$*"; }

# A fresh copy of this repository at HEAD (committed state only).
fresh_copy() {
  rm -rf "$1"; mkdir -p "$1"
  git -C "$REPO" archive HEAD | tar -x -C "$1"
}

stage_tools() {
  log "tools: lean4export $LEAN4EXPORT_TAG built with $LEAN_BUILD"
  local d=$WORK/tools/lean4export
  if [[ ! -d $d ]]; then
    git clone https://github.com/leanprover/lean4export "$d"
  fi
  git -C "$d" checkout -q "$LEAN4EXPORT_TAG"
  echo "$LEAN_BUILD" > "$d/lean-toolchain"   # must match the .olean files it reads
  (cd "$d" && lake build)
  elan toolchain install "$LEAN_JUDGE"
}

stage_challenge() {
  log "challenge: clean copy, NO archive cache; the archive's definitions are compiled from source"
  fresh_copy "$WORK/clean"
  cd "$WORK/clean/archiveplusfolder"
  export LAKE_ARTIFACT_CACHE=false
  lake exe mathlib/cache get        # clones dependencies per manifest; Mathlib oleans only
  lake build Challenge              # ~2,100 archive modules from source, plus our files
  lake env "$LEAN4EXPORT" Challenge -- $(cat export-targets.txt) > "$WORK/challenge.export"
  sha256sum "$WORK/challenge.export" | tee "$WORK/challenge.export.sha256"
}

stage_solution() {
  log "solution: archive at $ARCHIVE_REV"
  if [[ ! -d $ARCHIVE ]]; then
    git clone "$ARCHIVE_URL" "$ARCHIVE"
  fi
  git -C "$ARCHIVE" checkout -q "$ARCHIVE_REV"
  (
    cd "$ARCHIVE"
    if [[ ${FROM_SOURCE:-0} == 1 ]]; then
      export LAKE_ARTIFACT_CACHE=false
      lake exe mathlib/cache get
      lake build "$CORGK"
    else
      lake exe cache get              # archive's community cache (untrusted; re-checked by the judge)
      lake build --no-build "$CORGK"
    fi
  )
  fresh_copy "$WORK/solution"
  bash "$WORK/solution/scripts/link-archive-cache.sh" "$ARCHIVE" "$WORK/solution/archiveplusfolder"
  cd "$WORK/solution/archiveplusfolder"
  # Recommended: run this stage without network access (compiling runs the submission's code).
  lake build Solution 2>&1 | tee "$WORK/solution-build.log"   # loads ~86 GB of .olean files
  lake env "$LEAN4EXPORT" Solution -- $(cat export-targets.txt) > "$WORK/solution.export"
  sha256sum "$WORK/solution.export" | tee "$WORK/solution.export.sha256"
}

stage_judge() {
  log "judge: lake comparator on $LEAN_JUDGE"
  local bin=${ELAN_HOME:-$HOME/.elan}/toolchains/$(echo "$LEAN_JUDGE" | sed 's|/|--|; s|:|---|')/bin
  for tool in lake leanchecker-paranoid nanoda_bin; do
    command -v "$bin/$tool" >/dev/null || command -v "$tool" >/dev/null ||
      echo "WARNING: $tool not found in $bin or PATH (needed by comparator.json)"
  done
  mkdir -p "$WORK/judge"; cd "$WORK/judge"    # an empty directory, as the archive README requires
  PATH="$bin:$PATH" "$bin/lake" comparator --config "$HERE/comparator.json" \
    --challenge-from-export "$WORK/challenge.export" \
    --solution-from-export "$WORK/solution.export" 2>&1 | tee "$WORK/comparator.log"
}

# Optional fast independent checker (https://math.mit.edu/~drew/grh/): ~50 GB RAM.
stage_conleche() {
  log "con-leche --compare"
  local d=$WORK/tools/con-leche
  [[ -d $d ]] || git clone https://github.com/leanprover/con-leche "$d"
  git -C "$d" checkout -q compare
  (cd "$d" && lake build con-leche)
  "$d/.lake/build/bin/con-leche" --compare "$WORK/challenge.export" "$WORK/solution.export" \
    2>&1 | tee "$WORK/con-leche.log"
}

case "${1:-all}" in
  tools) stage_tools ;;
  challenge) stage_challenge ;;
  solution) stage_solution ;;
  judge) stage_judge ;;
  conleche) stage_conleche ;;
  all) stage_tools; stage_challenge; stage_solution; stage_judge ;;
  *) echo "unknown stage: $1" >&2; exit 2 ;;
esac
