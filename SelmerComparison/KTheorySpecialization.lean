import SelmerComparison.Basic
import KTheoryBound.Statement

/-!
# The comparison hypotheses in classical form

`KTheoryBound.ComparisonHypotheses` compares `K₄ₘ(ℤ){p}` with the archive's group
`integralSelmer m p = ShaU(ℚ_p/ℤ_p(−2m), 2p, G_ℚ)`. By `SelmerComparison.shaU_eq_classicalSelmer`
that group *is* the classical Selmer group

  `S_{p,2m} = ker( H¹_cont(G_ℚ, ℚ_p/ℤ_p(−2m)) → ∏_q H¹(I_q, –) × ∏_{q ∈ {2,p}} H¹(G_{ℚ_q}, – ) )`,

which is equation (1) of Aki Salmons' note (github.com/akisalmons/selmer-k-theory-note).
So `ComparisonHypotheses` is equivalent to `ClassicalComparisonHypotheses`, which mentions
only the textbook group. Its eligible-prime clause, `|K₄ₘ(ℤ){p}| ≤ |S_{p,2m}|`, holds with
equality by the classical dictionary `S_{p,e}^∨ ≅ K_{2e}(ℤ){p}` (Quillen–Lichtenbaum plus
Poitou–Tate; Salmons, Theorem 1.1). Mathlib does not have that dictionary, so it stays a
hypothesis here. What this file removes is the gap between the archive's encoding and the
textbook definition.
-/

noncomputable section

open ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base Formalism.ConjugateSelfDual
open KTheoryGrowth

namespace SelmerComparison

/-- The representation `ℚ_p/ℤ_p(−2m)` of `G_ℚ`, in the archive's encoding. -/
abbrev selmerRep (m : ℕ) (p : Nat.Primes) :=
  twist₂ (p : ℕ) (chiO ℚ (AlgebraicClosure ℚ) (p : ℕ) (integralCoeff p).O ^ (-((2 * m : ℕ) : ℤ)))

/-- The textbook Selmer group `S_{p,2m}`, for a choice `B` of places of `ℚ̄`. -/
abbrev classicalSelmerGroup (B : Nat.Primes → ValuationSubring (AlgebraicClosure ℚ))
    (m : ℕ) (p : Nat.Primes) :=
  classicalSelmer (selmerRep m p) B ((p : ℕ) * 2)

/-- The primes where the classical group is required to be locally trivial are exactly 2 and p. -/
theorem dvd_two_mul_iff (p q : Nat.Primes) : (q : ℕ) ∣ (p : ℕ) * 2 ↔ (q : ℕ) = 2 ∨ q = p := by
  rw [Nat.Prime.dvd_mul q.2, Nat.prime_dvd_prime_iff_eq q.2 p.2,
    Nat.prime_dvd_prime_iff_eq q.2 Nat.prime_two]
  have : (q : ℕ) = p ↔ q = p := ⟨fun h => Subtype.ext h, fun h => h ▸ rfl⟩
  rw [this]
  tauto

/-- **The archive's Selmer group is the textbook one.** -/
theorem integralSelmer_eq_classical (B : Nat.Primes → ValuationSubring (AlgebraicClosure ℚ))
    (hB : ∀ q : Nat.Primes, (B q).valuation (q : AlgebraicClosure ℚ) < 1) (m : ℕ) (p : Nat.Primes) :
    integralSelmer m p = classicalSelmerGroup B m p :=
  shaU_eq_classicalSelmer _ _ (Nat.mul_ne_zero p.2.ne_zero two_ne_zero) B hB

/-- `ComparisonHypotheses`, with the archive's group replaced by the textbook group.

The three clauses are classical theorems about `K n = K_n(ℤ)`, proved in Salmons §3:
finiteness (§3.2), `|K₄ₘ(ℤ){p}| = |S_{p,2m}|` at eligible primes (§3.1–3.2, Theorem 1.1:
Poitou–Tate plus Quillen–Lichtenbaum), and vanishing at excluded primes (§3.3–3.4,
Rognes–Weibel at `p = 2`). They stay hypotheses because neither Mathlib nor the archive
defines algebraic K-groups. -/
def ClassicalComparisonHypotheses (K : ℕ → Type*) [∀ n, AddCommGroup (K n)]
    (B : Nat.Primes → ValuationSubring (AlgebraicClosure ℚ)) : Prop :=
  (∀ m > 0, Finite (K (4 * m))) ∧
  (∀ m > 0, ∀ p : Nat.Primes, 5 ≤ (p : ℕ) → ¬ ((p : ℕ) - 1) ∣ 4 * m →
    Nat.card (AddCommGroup.primaryComponent (K (4 * m)) (p : ℕ)) ≤
      Nat.card (classicalSelmerGroup B m p)) ∧
  (∀ m > 0, ∀ p : Nat.Primes, ((p : ℕ) - 1) ∣ 4 * m →
    Nat.card (AddCommGroup.primaryComponent (K (4 * m)) (p : ℕ)) = 1)

/-- The two forms of the hypotheses are equivalent, for any choice of places. -/
theorem comparisonHypotheses_iff_classical (K : ℕ → Type*) [∀ n, AddCommGroup (K n)]
    (B : Nat.Primes → ValuationSubring (AlgebraicClosure ℚ))
    (hB : ∀ q : Nat.Primes, (B q).valuation (q : AlgebraicClosure ℚ) < 1) :
    KTheoryBound.ComparisonHypotheses K ↔ ClassicalComparisonHypotheses K B := by
  unfold KTheoryBound.ComparisonHypotheses ClassicalComparisonHypotheses
  simp only [← integralSelmer_eq_classical B hB]

/-- **Main theorem, classical form.** If `K₄ₘ(ℤ)` is finite, its p-part is at most the
textbook Selmer group `S_{p,2m}` at eligible primes, and it is trivial at excluded primes,
then `log |K₄ₘ(ℤ)| ≤ C (m+1)^A`. The hypothesis `Bound` is the archive's theorem. -/
theorem log_card_le_of_classical (hbound : UpperTheory.V.SmallClassNumbers.Bound)
    (K : ℕ → Type*) [∀ n, AddCommGroup (K n)]
    (B : Nat.Primes → ValuationSubring (AlgebraicClosure ℚ))
    (hB : ∀ q : Nat.Primes, (B q).valuation (q : AlgebraicClosure ℚ) < 1)
    (hK : ClassicalComparisonHypotheses K B) :
    ∃ C A : ℕ, ∀ m > 0, Real.log (Nat.card (K (4 * m))) ≤ C * ((m : ℝ) + 1) ^ A :=
  KTheoryBound.log_card_le_of hbound K ((comparisonHypotheses_iff_classical K B hB).2 hK)

end SelmerComparison

#print axioms SelmerComparison.shaU_eq_classicalSelmer
#print axioms SelmerComparison.integralSelmer_eq_classical
#print axioms SelmerComparison.log_card_le_of_classical

/-
Provenance note. The derivation `Bound + comparison ⇒ log |K₄ₘ(ℤ)| ≤ C (m+1)^A`, including
the specialization of the archive's `ShaU` to ℚ_p/ℤ_p(−2m) and the comparison stated as an
explicit hypothesis (`KTheoryComparison` in the working file `ArchiveSelmer.lean`, and
`KTheoryGrowth.lean`), was written independently of Salmons' note, in local working files dated
17:00 UTC on 21 November 2026. Salmons posted the observation publicly first (Zulip, 17:26 UTC),
and this repository's first commit is later (19:08 UTC). The identification with the classical
Selmer group and the citations of §3 above follow Salmons' note. The file timestamps are local
modification times, not a public record.
-/
