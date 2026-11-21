import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.LocalRing.Length

/-! # Orders of finite-length modules over (copies of) the p-adic integers -/

namespace KTheoryGrowth

open IsLocalRing Module Submodule

/-- The cardinality of a finite-length module over a local ring, in terms of the
residue-field cardinality. Here `Nat.card` returns zero for infinite types. -/
theorem card_eq_residueCard_pow_length {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : length R M ≠ ⊤) :
    Nat.card M = Nat.card (ResidueField R) ^ (length R M).toNat := by
  obtain ⟨s, hbot, htop⟩ :=
    isFiniteLength_iff_exists_compositionSeries.mp (Module.length_ne_top_iff.mp hM)
  have hcard : ∀ i : Fin (s.length + 1),
      Nat.card (s i) = Nat.card (ResidueField R) ^ (i : ℕ) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [← RelSeries.head, hbot, Fin.val_zero, pow_zero]
      exact Nat.card_unique
    | succ i ih =>
      have hcov := s.step i
      let f : s i.castSucc →ₗ[R] s i.succ := inclusion hcov.le
      have hsimple : IsSimpleModule R (s i.succ ⧸ f.range) := by
        rwa [range_inclusion, ← covBy_iff_quot_is_simple hcov.le]
      obtain ⟨𝔪, h𝔪, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
      rw [eq_maximalIdeal h𝔪] at e
      rw [f.range.card_eq_card_quotient_mul_card, Nat.card_congr e.toEquiv,
        ← Nat.card_congr (LinearEquiv.ofInjective f (inclusion_injective _)).toEquiv,
        ih, Fin.val_succ, pow_succ]
      rfl
  have hlast := hcard (Fin.last s.length)
  rw [← RelSeries.last, htop, Nat.card_congr (topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M).toEquiv,
    Fin.val_last] at hlast
  simpa [← length_compositionSeries s hbot htop] using hlast

/-- Over the p-adic integers the length gives the entire p-power order. -/
theorem card_eq_prime_pow_length {p : ℕ} [Fact p.Prime] {M : Type*}
    [AddCommGroup M] [Module ℤ_[p] M] (hM : length ℤ_[p] M ≠ ⊤) :
    Nat.card M = p ^ (length ℤ_[p] M).toNat := by
  rw [card_eq_residueCard_pow_length hM, Nat.card_congr PadicInt.residueField.toEquiv,
    Nat.card_zmod]

/-- Over the p-adic integers, the quotient by p has length one. -/
theorem length_padicInt_quotient_prime (p : ℕ) [Fact p.Prime] :
    length ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) = 1 := by
  rw [← PadicInt.maximalIdeal_eq_span_p, Module.length_eq_one_iff]
  exact isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal ℤ_[p]))

/-- The coefficient ring may be presented as an isomorphic copy of the p-adic integers. -/
theorem length_quotient_prime_of_padicIntEquiv {p : ℕ} [Fact p.Prime]
    {R : Type*} [CommRing R] [IsLocalRing R] (e : ℤ_[p] ≃+* R) :
    length R (R ⧸ Ideal.span {(p : R)}) = 1 := by
  have h : Ideal.span {(p : R)} = maximalIdeal R := by
    simpa [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span] using map_ringEquiv_maximalIdeal e
  rw [h, Module.length_eq_one_iff]
  exact isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal R))

/-- The entire p-power order over a coefficient ring isomorphic to the p-adic integers. -/
theorem card_eq_prime_pow_length_of_padicIntEquiv {p : ℕ} [Fact p.Prime]
    {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    (e : ℤ_[p] ≃+* R) (hM : length R M ≠ ⊤) :
    Nat.card M = p ^ (length R M).toNat := by
  rw [card_eq_residueCard_pow_length hM,
    Nat.card_congr (ResidueField.mapEquiv e).symm.toEquiv,
    Nat.card_congr PadicInt.residueField.toEquiv, Nat.card_zmod]


end KTheoryGrowth
