# SelmerComparison: the archive's `ShaU` is the classical Selmer group

`lake build SelmerComparison` (light imports only; about 30 s once the archive cache is linked).
No `sorry`. The main theorems depend only on `[propext, Classical.choice, Quot.sound]`.

## What is proved

* `Basic.lean`, `shaU_eq_classicalSelmer`: for any `G_ℚ`-module `M` and `n ≠ 0`, the archive's
  `ShaU ρ n ⊤` equals the textbook group: continuous `H¹(G_ℚ, M)` (Krull topology, checked by
  `rfl`), unramified at every prime, and locally trivial at the primes dividing `n`. Places are
  given by one chosen valuation subring of `ℚ̄` above each prime, and the result holds for every
  such choice (`classicalSelmer_indep`). The archive imposes its conditions at *all* valuation
  subrings, including conjugates and the trivial one. The proof uses three facts:
  1. vanishing is invariant under conjugation (cocycle computation);
  2. places above `p` are conjugate (the archive's `placesQ`);
  3. every nontrivial valuation subring lies over a prime (proved here), and the trivial one has
     trivial inertia (the archive's `places`).
* `KTheorySpecialization.lean`:
  * `integralSelmer m p = S_{p,2m}`, the classical group for `ℚ_p/ℤ_p(−2m)` with local
    triviality at {2, p}. This is equation (1) of Aki Salmons' note.
  * `comparisonHypotheses_iff_classical`: `ComparisonHypotheses` is equivalent to the same
    statement about the textbook group.
  * `log_card_le_of_classical`: the main bound, stated with the textbook group.

* `LocalGalois.lean`: the local conditions are conditions in local Galois cohomology.
  * `exists_localGalois`: for a place `A` of `ℚ̄` above `q`, the decomposition group is
    isomorphic *as a topological group* to `Gal(ℚ̄_q/ℚ_q)`, and the isomorphism carries inertia
    onto local inertia. The input is the archive's `DecEquiv`. The archive proves it from global
    Artin reciprocity, local Tate duality and the local Euler characteristic (`core`, no sorry).
    We pin the local field down to `ℚ_q` itself using `e·f = 1` over ℚ.
  * `resDec_eq_zero_iff`, `resIne_eq_zero_iff`, `localCocycle_mem`: a global class vanishes on
    `D_q` (resp. `I_q`) iff its transported continuous cocycle is a coboundary on
    `Gal(ℚ̄_q/ℚ_q)` (resp. on local inertia).
  * `mem_classicalSelmer_iff_local`: the Selmer group with its conditions stated entirely in
    `H¹(ℚ_q, –)` and `H¹(I_{ℚ_q}, –)`. This is the form of Salmons' eq. (1).
  * Imports: about 1,200 extra archive modules (peak about 8 GB RAM to build). This is not the
    170,000-module `CorGKOf` closure.

## What remains a hypothesis

The eligible-prime clause, `|K₄ₘ(ℤ){p}| ≤ |S_{p,2m}|`, holds with equality by
Quillen–Lichtenbaum plus Poitou–Tate (Salmons, Theorem 1.1). It is not formalized, because
neither Mathlib nor the archive defines the algebraic K-groups of ℤ, and neither has
Poitou–Tate duality for `ℚ`. The three clauses of `ClassicalComparisonHypotheses` and their
classical proofs, all in Salmons §3:

| clause | statement | Salmons |
|---|---|---|
| finiteness | `K₄ₘ(ℤ)` is finite | §3.2 (Soulé; finiteness of the étale groups) |
| eligible primes | `|K₄ₘ(ℤ){p}| ≤ |S_{p,2m}|` (in fact `=`) | §3.1–3.2, Theorem 1.1, eq. (2): Poitou–Tate (8) plus Quillen–Lichtenbaum (9) |
| excluded primes | `K₄ₘ(ℤ){p} = 0` when `p − 1 ∣ 4m` | §3.3 (resonant primes, eq. (10)) and §3.4 (quadratic class number bound; `p = 2` by Rognes–Weibel) |

## References

* A. Salmons, *Uniform Selmer lengths and integral K-theory: an exact dictionary and
  conditional bounds* (21 November 2026), github.com/akisalmons/selmer-k-theory-note, §3
  ("Proof of the classical dictionary"). Equation (1) defines `S_{ℓ,e}`, which
  `KTheorySpecialization.lean` identifies with the archive's group.
* L. Alpöge, announcement and `remark.pdf` (item 17, footnote 6), and the Lean archive
  `leanprover-community/riemann-hypothesis` at commit `23aebbb3`. This folder closes only the gap between the
archive's Lean encoding and the textbook definition.
