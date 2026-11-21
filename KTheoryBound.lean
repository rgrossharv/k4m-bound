import KTheoryBound.Statement
import KTheoryBound.ArchiveInput

/-!
# A log-polynomial bound for |K₄ₘ(ℤ)|: final statements

This is the file to audit. It states the final theorems in full and proves each one by
supplying `archive_bound : Bound` to the corresponding theorem of `KTheoryBound/Statement.lean`.
`archive_bound` (in `KTheoryBound/ArchiveInput.lean`) is the archive's theorem
`UpperTheory.V.SmallClassNumbers.bound`, restated with `sorry` to avoid importing its 86 GB
proof closure. `scripts/check-archive-signature.lean` checks that its statement is identical
to the archive's. So the `sorryAx` in the axiom output below stands for exactly that one
archive theorem.

The definitions the statements mention are:
* `integralSelmer m p` (in `KTheoryBound/ArchiveSpecialization.lean`, unfolded by `rfl` in
  `Statement.lean`). This is continuous H¹ of Gal(ℚ̄/ℚ) with coefficients ℚ_p/ℤ_p(−2m)
  (discrete topology): the classes that are trivial on all inertia groups and on the
  decomposition groups at the places above 2 and p.
* `ComparisonHypotheses K` (in `Statement.lean`): the three K-theory inputs, written inline.

**Build cost.** Only the archive's definitions are imported (about 2,100 modules), so
the whole project builds in about a minute against the archive cache.

## What is proved, and what is not

* **Proved in Lean, modulo the archive.** The only external Lean input is
  `archive_bound`, i.e. `UpperTheory.V.SmallClassNumbers.bound` from
  `leanprover-community/riemann-hypothesis` at commit `23aebbb3` (the claimed RH formalization
  announced on 2026-11-20, **not independently verified**; the community Comparator run checks
  only the closure of the five RH theorems).
* **Not proved in Lean: `ComparisonHypotheses` for the actual groups K_n(ℤ).** Mathlib has
  no Quillen K-theory. For K₄ₘ(ℤ) the three fields are published theorems:
  - finiteness: Quillen (finite generation) and Borel (rank 0 in degrees 4m);
  - eligible primes (p ≥ 5, p − 1 ∤ 4m): Quillen–Lichtenbaum (Rost–Voevodsky) gives
    K₄ₘ(ℤ){p} ≅ H²(ℤ[1/p], ℤ_p(2m+1)). Poitou–Tate duality makes this dual to the strict
    Selmer group of ℚ_p/ℤ_p(−2m) (unramified everywhere, trivial at p). At 2 the unramified
    H¹ vanishes because Frobenius acts by 2^{−2m} ≠ 1, so the dual is `integralSelmer m p`
    (Weibel, *Algebraic K-theory of rings of integers in local and global fields*, Thm 70).
    The hypothesis is only the inequality |K₄ₘ(ℤ){p}| ≤ |`integralSelmer m p`|, so it suffices
    that the classical Selmer group is no larger than the archive's `ShaU`;
  - excluded primes (p − 1 ∣ 4m, always including 2 and 3): Rognes–Weibel at p = 2
    (Weibel, Cor. 86). For odd p, K₄ₘ(ℤ)/p is an even eigenspace of Cl(ℚ(ζ_p))/p that comes from
    ℚ or a real quadratic field and vanishes (Weibel, Thm 105 and its proof).
* **C and A are not explicit.** The archive's `bound` is existential.
-/

namespace KTheoryBound

open KTheoryGrowth

/-- **Unconditional.** For every m ≥ 1, the orders of the Selmer groups at the eligible
primes are the prime-power parts of a single positive integer `N`, prime to all excluded
primes, with `log N ≤ C (m+1)^A`. -/
theorem selmer_product_bound :
    ∃ C A : ℕ, ∀ m > 0, ∃ N : ℕ, 0 < N ∧
      (∀ p : Nat.Primes, 5 ≤ (p : ℕ) → ¬ ((p : ℕ) - 1) ∣ 4 * m →
        (p : ℕ) ^ N.factorization p = Nat.card (integralSelmer m p)) ∧
      (∀ p : Nat.Primes, ((p : ℕ) - 1) ∣ 4 * m → ¬ (p : ℕ) ∣ N) ∧
      Real.log N ≤ C * ((m : ℝ) + 1) ^ A :=
  selmer_product_bound_of archive_bound

/-- **Main theorem.** For any family of abelian groups satisfying the comparison
hypotheses (intended: K_n(ℤ)), `log |K (4m)| ≤ C (m+1)^A` for all m ≥ 1. -/
theorem log_card_le (K : ℕ → Type*) [∀ n, AddCommGroup (K n)] (hK : ComparisonHypotheses K) :
    ∃ C A : ℕ, ∀ m > 0, Real.log (Nat.card (K (4 * m))) ≤ C * ((m : ℝ) + 1) ^ A :=
  log_card_le_of archive_bound K hK

/-- **Non-vacuity.** The comparison hypotheses are satisfiable, by `K n = ℤ/N n`. -/
theorem comparisonHypotheses_consistent :
    ∃ N : ℕ → ℕ, (∀ n, 0 < N n) ∧ ComparisonHypotheses (fun n => ZMod (N n)) :=
  comparisonHypotheses_consistent_of archive_bound

end KTheoryBound

/-! ## Axiom audit

Expect `[propext, sorryAx, Classical.choice, Quot.sound]` for the three final theorems, where
`sorryAx` is only `archive_bound`. The `_of` versions in `Statement.lean`, which take `Bound` as a
hypothesis, print exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms KTheoryBound.archive_bound
#print axioms KTheoryBound.log_card_le_of
#print axioms KTheoryBound.selmer_product_bound
#print axioms KTheoryBound.log_card_le
#print axioms KTheoryBound.comparisonHypotheses_consistent
