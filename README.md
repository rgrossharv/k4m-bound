# A log-polynomial bound for |K₄ₘ(ℤ)| in Lean

**Main statement** (`KTheoryBound.lean`): there are constants `C`, `A` such that for every
`m ≥ 1`,

    log |K₄ₘ(ℤ)| ≤ C · (m + 1)^A,

stated for any family of abelian groups `K n` satisfying the K-theory comparison hypotheses
(`ComparisonHypotheses`, published theorems not formalized here). The file also proves
`selmer_product_bound`, an **unconditional** bound on the product of the underlying Galois
Selmer group orders, and `comparisonHypotheses_consistent`, which shows the hypotheses are satisfiable.

On the log log scale this is exponentially stronger than the best published bounds for
K_n(ℤ): Soulé 2003, Prop. 4 iv) gives log log |K_n(ℤ)_tors| ≤ 8n⁴ log n; de la Torre Durán,
arXiv 2611.06300, gives e^{O(n² log n)}. Both hold only up to small torsion. See
`docs/RESEARCH_NOTES.md`, §7. The constants here are not explicit.

## Trust: read this first

* The one Lean input from outside Mathlib is `UpperTheory.V.SmallClassNumbers.bound` from
  [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
  at commit `23aebbb302010b292314d406aa97f7901d698634`. That development claims a proof of RH
  (announced 2026-11-20) and **has not been independently verified**. This result is only as
  reliable as it is.
* That theorem is **restated with `sorry`** as `KTheoryBound.archive_bound`
  (`KTheoryBound/ArchiveInput.lean`), so its 170k-module / 86 GB proof closure is never
  imported. The statement is the archive's own `Bound` definition, and
  `scripts/check-archive-signature.lean` checks against the archive's compiled
  `CorGKOf.olean` that the two statements are identical. The checker has been mutation-tested:
  it rejects a modified statement. So `sorryAx` in the axiom output stands for exactly that
  archive theorem. Everything else is kernel-checked here, and the `_of` theorems in
  `Statement.lean` (which take `Bound` as a hypothesis) use only
  `[propext, Classical.choice, Quot.sound]`.
* The community verification (Comparator) of the archive checks only the dependency closure
  of its five RH theorems (`comparator.json`). It is not yet known whether that closure
  contains `bound`, and as of 2026-11-21 that verification has not finished.
* `ComparisonHypotheses` is an explicit hypothesis. Mathlib has no Quillen K-theory. The
  docstring of `KTheoryBound.lean` lists the published theorems that supply each field for
  K₄ₘ(ℤ). Check these when auditing.

## Layout

| File | Role |
|---|---|
| `KTheoryBound.lean` | **The file to audit.** Final statements, one-line proofs from `archive_bound`, axiom printout. |
| `KTheoryBound/Statement.lean` | Same theorems with `Bound` as an explicit argument, `rfl` checks unfolding every definition, and the definition of `ComparisonHypotheses`. |
| `KTheoryBound/ArchiveInput.lean` | The archive's `bound`, restated with `sorry` (the only `sorry` in the project). |
| `scripts/check-archive-signature.lean` | Checks that the restatement is identical to the archive's compiled theorem. |
| `KTheoryBound/ArchiveSpecialization.lean` | Specializes the archive's Selmer groups to ℤ_p-coefficients, twist −2m, over ℚ. |
| `KTheoryBound/OrderFromLengths.lean`, `PadicLength.lean` | Elementary lemmas (orders from prime-power lengths). |
| `archiveplusfolder/` | **Full independent check without the `sorry`** (Comparator, for machines with ~100 GB RAM). See its README. |
| `docs/RESEARCH_NOTES.md` | Mathematical notes: what a *polynomial* bound would need (open), archive survey, literature comparison. |

## Building

The archive cannot reasonably be built from scratch here (its build is about 100 GB). Use its cache:

```bash
# 1. a checkout of the archive at the pinned commit, with its cache
git clone https://github.com/leanprover-community/riemann-hypothesis.git ARCHIVE
git -C ARCHIVE checkout 23aebbb302010b292314d406aa97f7901d698634
(cd ARCHIVE && lake exe cache get && lake build --no-build)

# 2. point this project's dependencies at it (symlinks; checks every revision)
bash scripts/link-archive-cache.sh ARCHIVE

# 3. build (about 1 min; only the archive's definitions, about 2,100 modules, are loaded)
lake build

# 4. check the sorried restatement against the archive's compiled theorem (about 30 s)
lake env lean --run scripts/check-archive-signature.lean
```

Expected axiom output: `[propext, sorryAx, Classical.choice, Quot.sound]` for the final theorems,
where `sorryAx` is `archive_bound`, and `[propext, Classical.choice, Quot.sound]` for the `_of`
theorems. The archive cache is still needed for the definitions' compiled files. Only the
`ClassNumberThree` closure (1.4 GB) is used, although `link-archive-cache.sh` links the full checkout.
