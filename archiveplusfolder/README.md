# Full independent check (for machines with a lot of compute)

The main project proves the bound from **one** archive theorem, restated with `sorry`
(`KTheoryBound/ArchiveInput.lean`) to avoid an 86 GB import. This folder checks it **without**
that `sorry`, against Mathlib and the RH archive, with independent kernels. It uses the same
procedure the archive's maintainers use for RH itself (Comparator).

## Why this is needed

The existing independent checks of the RH archive (its Comparator run and
<https://math.mit.edu/~drew/grh/>) export only the dependency closure of the five RH theorems.
The archive theorem we use, `UpperTheory.V.SmallClassNumbers.bound`, is referenced only in
`CorGKOf.lean`, which is pulled into `Main` by an import alone
(`Supplements/Kernels/MainTheoremsAll.lean`). No proof the RH theorems depend on uses it,
so those checks almost certainly do **not** cover it. This run does.

## What is checked

| Piece | File | Built from |
|---|---|---|
| **Challenge**: the three final statements, `sorry` proofs | `Challenge.lean` | a clean copy with **no** archive cache: the archive *definitions* the statements mention (~2,100 modules) are compiled from source |
| **Solution**: the same statements proved from the archive's real `bound` (no `sorry`) | `Solution.lean` | the archive's ~170,000-module proof closure. The community cache is fine here because the judge re-checks every proof |
| **Judge** | `comparator.json` | `lake comparator` on Lean v4.36.0: checks that the statements and definitions match, that only `propext`, `Quot.sound` and `Classical.choice` are used, and replays every declaration with the Lean kernel, `leanchecker-paranoid` and `nanoda` |

The three theorems (`KTheoryBoundCheck.selmer_product_bound`, `.log_card_le`,
`.comparisonHypotheses_consistent`) are verbatim the statements of `../KTheoryBound.lean`.

## Requirements

* Linux, `elan`, `git`, `curl`
* about **100 GB RAM** for the judge and **200 GB disk** (archive cache ~100 GB, solution export
  ~60 GB, by analogy with the RH export at <https://math.mit.edu/~drew/grh/>)
* hours of wall time. Building the archive from source instead of using its cache takes days.

## Running

```bash
bash run.sh              # everything; or one stage at a time:
bash run.sh tools        # lean4export v4.33.0 (built with Lean 4.33.1) + Lean v4.36.0
bash run.sh challenge    # clean build of Challenge, export → work/challenge.export
bash run.sh solution     # archive + its cache, build Solution, export → work/solution.export
bash run.sh judge        # lake comparator → work/comparator.log
bash run.sh conleche     # optional fast extra checker (~50 GB RAM)
```

Options: `WORK=/big/disk/work`, `ARCHIVE=/path/to/existing/archive/checkout` (pinned commit
`23aebbb302010b292314d406aa97f7901d698634`, cache already fetched), `FROM_SOURCE=1`.

Recommended, as in the archive's procedure: run the `solution` stage without network access,
since compiling Lean code runs it.

## What to send back

`work/comparator.log`, `work/solution-build.log` (its `#print axioms` lines should read
`[propext, Classical.choice, Quot.sound]`), `work/*.sha256`, and the `lean --version` /
machine details.

**A pass means:** given Mathlib's and the archive's definitions, and the K-theory comparison
hypotheses (still a hypothesis; see `../KTheoryBound.lean`), the bound is proved from the
standard axioms, and independent kernels agree.

## Tested here, and not tested

On a 22 GB machine: `Challenge` builds; `Solution`'s proof terms typecheck when `bound` is
swapped for its signature-checked restatement (identical type); `lean4export` v4.33.0 builds and
exports the Challenge (190 MB, Lean 4.33.1 githash `819816b2`). **Not run here:** the real
`Solution` build (it needs the 86 GB import), its export, and the judge.
