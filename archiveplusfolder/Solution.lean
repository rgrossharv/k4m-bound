import KTheoryBound.Statement
import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.CorGKOf

/-!
# Solution: the same statements, proved from the archive's actual theorem

`UpperTheory.V.SmallClassNumbers.bound` is the archive's proved theorem (no `sorry`), imported
from `CorGKOf`, which loads ~170,000 archive modules (~86 GB of .olean files). Nothing here
imports `KTheoryBound.ArchiveInput`, the sorried restatement used by the light build.
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
  exact selmer_product_bound_of UpperTheory.V.SmallClassNumbers.bound

/-- **Main theorem.** Under the comparison hypotheses, `log |K (4m)| ≤ C (m+1)^A`. -/
theorem log_card_le (K : ℕ → Type) [∀ n, AddCommGroup (K n)] (hK : ComparisonHypotheses K) :
    ∃ C A : ℕ, ∀ m > 0, Real.log (Nat.card (K (4 * m))) ≤ C * ((m : ℝ) + 1) ^ A := by
  exact log_card_le_of UpperTheory.V.SmallClassNumbers.bound K hK

/-- **Non-vacuity.** The comparison hypotheses are satisfiable. -/
theorem comparisonHypotheses_consistent :
    ∃ N : ℕ → ℕ, (∀ n, 0 < N n) ∧ ComparisonHypotheses (fun n => ZMod (N n)) := by
  exact comparisonHypotheses_consistent_of UpperTheory.V.SmallClassNumbers.bound

end KTheoryBoundCheck

#print axioms KTheoryBoundCheck.selmer_product_bound
#print axioms KTheoryBoundCheck.log_card_le
#print axioms KTheoryBoundCheck.comparisonHypotheses_consistent
