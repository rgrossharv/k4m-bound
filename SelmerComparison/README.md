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

## What remains a hypothesis

The eligible-prime clause, `|K₄ₘ(ℤ){p}| ≤ |S_{p,2m}|`, holds with equality by
Quillen–Lichtenbaum plus Poitou–Tate (Salmons, Theorem 1.1). It is not formalized, because
Mathlib has no K-theory and no Poitou–Tate duality. This folder closes only the gap between the
archive's Lean encoding and the textbook definition.
