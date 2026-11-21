import KTheoryBound.ArchiveSpecialization

/-!
# Statements (light file: imports only the archive's *definitions*)

Everything here is proved from an explicit hypothesis `hbound : Bound`, the archive's
estimate. The import closure is about 2,100 archive modules (1.4 GB), so this file compiles
and opens quickly. `KTheoryBound.lean` discharges `hbound` with the archive's proof
`UpperTheory.V.SmallClassNumbers.bound`, which needs that proof's full closure
(about 170,000 modules, 86 GB).

See `KTheoryBound.lean` for the final statements and for what is and is not proved.
-/

namespace KTheoryBound

open KTheoryGrowth
open Formalism.ConjugateSelfDual Formalism.GaloisCohomology ReciprocityTheory.Gal
open UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.SmallClassNumbers

/-! ## The objects, unfolded (each `example` is checked by `rfl`) -/

/-- The Selmer group is the archive's `ShaU` for the representation ℚ_p/ℤ_p(−2m). -/
example (m : ℕ) (p : Nat.Primes) :
    integralSelmer m p =
      ShaU (twist₂ (p : ℕ) (chiO ℚ (AlgebraicClosure ℚ) (p : ℕ) (integralCoeff p).O ^
        (-((2 * m : ℕ) : ℤ)))) ((p : ℕ) * 2) ⊤ := rfl

/-- Its length is the archive's `len`, which is what the archive's `Bound` controls. -/
example (m : ℕ) (p : Nat.Primes) :
    integralSelmerLength m p = len (AlgebraicClosure ℚ) (p : ℕ) (integralCoeff p) (2 * m) := rfl

/-- The archive's statement that we use, verbatim. -/
example : Bound = ∃ C A : ℕ, ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (e : ℕ),
    1 ≤ e → Even e → ∀ (c : ∀ l : Nat.Primes, Coef l) (Ls : Finset Nat.Primes),
      (∀ l ∈ Ls, 5 ≤ (l : ℕ) ∧ ¬ (l : ℕ) - 1 ∣ 2 * e) →
      (∀ l ∈ Ls, len Ω l (c l) e ≠ ⊤) ∧
      ∑ l ∈ Ls, Real.log (l : ℕ) * (((len Ω l (c l) e).toNat : ℝ) / ((eO l (c l).O).toNat : ℝ))
        ≤ C * ((e : ℝ) + 1) ^ A := rfl

/-- The coefficient module is ℚ_p/ℤ_p, and the action is the cyclotomic character to the power −2m. -/
example (m : ℕ) (p : Nat.Primes) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : QO (p : ℕ) (integralCoeff p).O) :
    integralCoeffQuotientEquiv p
      (twist₂ (p : ℕ) (chiO ℚ (AlgebraicClosure ℚ) (p : ℕ) (integralCoeff p).O ^
        (-((2 * m : ℕ) : ℤ))) g x) =
      (cycZ ℚ (AlgebraicClosure ℚ) (p : ℕ) g ^ (-((2 * m : ℕ) : ℤ))) •
        integralCoeffQuotientEquiv p x :=
  integralCoeffQuotientEquiv_twist p _ g x

/-! ## 1. The unconditional Selmer statement -/

/-- **Unconditional.** The orders of the Selmer groups at the eligible primes multiply to
an integer `N` with `log N ≤ C (m+1)^A`. -/
theorem selmer_product_bound_of (hbound : Bound) :
    ∃ C A : ℕ, ∀ m > 0, ∃ N : ℕ, 0 < N ∧
      (∀ p : Nat.Primes, 5 ≤ (p : ℕ) → ¬ ((p : ℕ) - 1) ∣ 4 * m →
        (p : ℕ) ^ N.factorization p = Nat.card (integralSelmer m p)) ∧
      (∀ p : Nat.Primes, ((p : ℕ) - 1) ∣ 4 * m → ¬ (p : ℕ) ∣ N) ∧
      Real.log N ≤ C * ((m : ℝ) + 1) ^ A := by
  obtain ⟨C, A, h⟩ := selmerLengthBound_of_archive hbound
  refine ⟨C * 2 ^ A, A, fun m hm => ?_⟩
  obtain ⟨N, hN, hfac, hvan, hlog⟩ := exists_selmer_order_le h hm
  refine ⟨N, hN, fun p hp5 hp => ?_, fun p hp => ?_, ?_⟩
  · have he : Eligible m p := ⟨hp5, hp⟩
    have hfin : integralSelmerLength m p ≠ ⊤ := (h m hm {p} (by simpa using he)).1 p (by simp)
    rw [card_integralSelmer hfin, ← hfac p he, ENat.toNat_natCast]
  · exact hvan p fun he => he.2 hp
  · calc Real.log N ≤ C * (2 * (m : ℝ) + 1) ^ A := hlog
      _ ≤ C * (2 * ((m : ℝ) + 1)) ^ A := by gcongr; linarith
      _ = ((C * 2 ^ A : ℕ) : ℝ) * ((m : ℝ) + 1) ^ A := by push_cast; rw [mul_pow]; ring

/-! ## 2. The K-theory comparison hypotheses -/

/-- The three published K-theory inputs, for a family of abelian groups `K n`
(intended: `K n = K_n(ℤ)`). Only the degrees `4m`, m ≥ 1, are involved. -/
def ComparisonHypotheses (K : ℕ → Type*) [∀ n, AddCommGroup (K n)] : Prop :=
  -- K₄ₘ(ℤ) is finite
  (∀ m > 0, Finite (K (4 * m))) ∧
  -- at an eligible prime, the p-primary part is no larger than the Selmer group
  -- (only this direction is needed: |K₄ₘ(ℤ){p}| = |classical Selmer| ≤ |archive ShaU|)
  (∀ m > 0, ∀ p : Nat.Primes, 5 ≤ (p : ℕ) → ¬ ((p : ℕ) - 1) ∣ 4 * m →
    Nat.card (AddCommGroup.primaryComponent (K (4 * m)) (p : ℕ)) ≤ Nat.card (integralSelmer m p)) ∧
  -- at an excluded prime (p - 1 ∣ 4m, including p = 2, 3), the p-primary part is trivial
  (∀ m > 0, ∀ p : Nat.Primes, ((p : ℕ) - 1) ∣ 4 * m →
    Nat.card (AddCommGroup.primaryComponent (K (4 * m)) (p : ℕ)) = 1)

/-! ## 3. The bound -/

/-- **Main theorem.** Under the comparison hypotheses, `log |K (4m)| ≤ C (m+1)^A` for all
m ≥ 1, with `C` and `A` independent of m. -/
theorem log_card_le_of (hbound : Bound) (K : ℕ → Type*) [∀ n, AddCommGroup (K n)]
    (hK : ComparisonHypotheses K) :
    ∃ C A : ℕ, ∀ m > 0, Real.log (Nat.card (K (4 * m))) ≤ C * ((m : ℝ) + 1) ^ A := by
  obtain ⟨hfin, helig, hexcl⟩ := hK
  obtain ⟨C, A, hsel⟩ := selmer_product_bound_of hbound
  refine ⟨C, A, fun m hm => ?_⟩
  obtain ⟨N, hN, hcard, hvan, hlog⟩ := hsel m hm
  have := hfin m hm
  have hK0 : Nat.card (K (4 * m)) ≠ 0 := Nat.card_pos.ne'
  -- |K (4m)| divides N, prime by prime
  have hdvd : Nat.card (K (4 * m)) ∣ N := by
    rw [← Nat.factorization_le_iff_dvd hK0 hN.ne']
    intro q
    by_cases hq : q.Prime
    · let p : Nat.Primes := ⟨q, hq⟩
      have : Fact q.Prime := ⟨hq⟩
      have hprim := card_primaryComponent (K (4 * m)) q
      by_cases he : 5 ≤ q ∧ ¬ (q - 1) ∣ 4 * m
      · have h1 : q ^ (Nat.card (K (4 * m))).factorization q ≤ q ^ N.factorization q :=
          hprim.symm.le.trans ((helig m hm p he.1 he.2).trans (hcard p he.1 he.2).symm.le)
        exact (Nat.pow_le_pow_iff_right hq.two_le).mp h1
      · have hexc : (q - 1) ∣ 4 * m := (not_eligible_iff hq).mp he
        have h1 : q ^ (Nat.card (K (4 * m))).factorization q = q ^ 0 := by
          rw [← hprim, pow_zero]; exact hexcl m hm p hexc
        rw [Nat.pow_right_injective hq.two_le h1]
        exact Nat.zero_le _
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  have hle : (Nat.card (K (4 * m)) : ℝ) ≤ N := by exact_mod_cast Nat.le_of_dvd hN hdvd
  have hpos : (0 : ℝ) < Nat.card (K (4 * m)) := by exact_mod_cast Nat.pos_of_ne_zero hK0
  exact (Real.log_le_log hpos hle).trans hlog

/-! ## 4. The hypotheses are satisfiable -/

private theorem exists_model (hbound : Bound) :
    ∃ f : ℕ → ℕ, ∀ m > 0, 0 < f (4 * m) ∧
      (∀ p : Nat.Primes, 5 ≤ (p : ℕ) → ¬ ((p : ℕ) - 1) ∣ 4 * m →
        (p : ℕ) ^ (f (4 * m)).factorization p = Nat.card (integralSelmer m p)) ∧
      (∀ p : Nat.Primes, ((p : ℕ) - 1) ∣ 4 * m → ¬ (p : ℕ) ∣ f (4 * m)) := by
  classical
  obtain ⟨C, A, hsel⟩ := selmer_product_bound_of hbound
  let f : ℕ → ℕ := fun n => if h : 0 < n / 4 then Classical.choose (hsel (n / 4) h) else 1
  refine ⟨f, fun m hm => ?_⟩
  have h4 : 0 < 4 * m / 4 := by omega
  have hspec := Classical.choose_spec (hsel (4 * m / 4) h4)
  have hf : f (4 * m) = Classical.choose (hsel (4 * m / 4) h4) := dif_pos h4
  rw [← hf, show 4 * m / 4 = m by omega] at hspec
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.1⟩

/-- **Non-vacuity.** Some family of finite abelian groups satisfies `ComparisonHypotheses`,
namely `K (4m) = ℤ/N_m` with `N_m` from `selmer_product_bound_of`. -/
theorem comparisonHypotheses_consistent_of (hbound : Bound) :
    ∃ N : ℕ → ℕ, (∀ n, 0 < N n) ∧ ComparisonHypotheses (fun n => ZMod (N n)) := by
  classical
  obtain ⟨f, hf⟩ := exists_model hbound
  let N : ℕ → ℕ := fun n => if 0 < f n then f n else 1
  have hNpos (n : ℕ) : 0 < N n := by simp only [N]; split <;> omega
  have hN4 (m : ℕ) (hm : 0 < m) : N (4 * m) = f (4 * m) := if_pos (hf m hm).1
  have (n : ℕ) : NeZero (N n) := ⟨(hNpos n).ne'⟩
  refine ⟨N, hNpos, ?_⟩
  have hcard (m : ℕ) (q : ℕ) [Fact q.Prime] :
      Nat.card (AddCommGroup.primaryComponent (ZMod (N (4 * m))) q) =
        q ^ (N (4 * m)).factorization q := by
    rw [card_primaryComponent, Nat.card_zmod]
  refine ⟨fun m _ => inferInstance, fun m hm p hp5 hp => ?_, fun m hm p hp => ?_⟩
  · have : Fact (p : ℕ).Prime := ⟨p.2⟩
    rw [hcard, hN4 m hm]
    exact ((hf m hm).2.1 p hp5 hp).le
  · have : Fact (p : ℕ).Prime := ⟨p.2⟩
    rw [hcard, hN4 m hm, Nat.factorization_eq_zero_of_not_dvd ((hf m hm).2.2 p hp), pow_zero]

end KTheoryBound

#print axioms KTheoryBound.selmer_product_bound_of
#print axioms KTheoryBound.log_card_le_of
#print axioms KTheoryBound.comparisonHypotheses_consistent_of
