import KTheoryBound.Statement

/-!
# Challenge: the statements to be checked, with `sorry` proofs

Imports only `KTheoryBound.Statement`, i.e. our definitions plus the RH archive's *definitions*
(module `ClassNumberThree` and its ~2,100-module closure); none of the archive's proof of
`bound` is imported. Comparator checks that `Solution` proves exactly these statements, with
the same definitions, using only `propext`, `Quot.sound` and `Classical.choice`.

`K : ℕ → Type` is monomorphic here so that the statement has no universe parameters.
-/

namespace KTheoryBoundCheck

open KTheoryGrowth KTheoryBound

/-- **Unconditional.** Selmer group orders at the eligible primes multiply to an integer
`N` with `log N ≤ C (m+1)^A`. -/
theorem selmer_product_bound :
    ∃ C A : ℕ, ∀ m > 0, ∃ N : ℕ, 0 < N ∧
      (∀ p : Nat.Primes, 5 ≤ (p : ℕ) → ¬ ((p : ℕ) - 1) ∣ 4 * m →
        (p : ℕ) ^ N.factorization p = Nat.card (integralSelmer m p)) ∧
      (∀ p : Nat.Primes, ((p : ℕ) - 1) ∣ 4 * m → ¬ (p : ℕ) ∣ N) ∧
      Real.log N ≤ C * ((m : ℝ) + 1) ^ A := by
  sorry

/-- **Main theorem.** Under the comparison hypotheses, `log |K (4m)| ≤ C (m+1)^A`. -/
theorem log_card_le (K : ℕ → Type) [∀ n, AddCommGroup (K n)] (hK : ComparisonHypotheses K) :
    ∃ C A : ℕ, ∀ m > 0, Real.log (Nat.card (K (4 * m))) ≤ C * ((m : ℝ) + 1) ^ A := by
  sorry

/-- **Non-vacuity.** The comparison hypotheses are satisfiable. -/
theorem comparisonHypotheses_consistent :
    ∃ N : ℕ → ℕ, (∀ n, 0 < N n) ∧ ComparisonHypotheses (fun n => ZMod (N n)) := by
  sorry

end KTheoryBoundCheck
