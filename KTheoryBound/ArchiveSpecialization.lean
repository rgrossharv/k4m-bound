import KTheoryBound.OrderFromLengths
import KTheoryBound.PadicLength
import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.ClassNumberThree

/-!
# Specializing the archive's Selmer groups to ℤ_p-coefficients over ℚ

The archive's `len Ω l c e` is the length of a Selmer group `ShaU` with coefficients
in a ring `c.O` (a finite DVR over ℤ_l inside an algebraic closure of ℚ_l). Here we fix

* `Ω = AlgebraicClosure ℚ`,
* `c = integralCoeff p`, the copy `⊥ ≅ ℤ_p` inside the archive's `PadicAlgCl p`,
* twist `e = 2m`,

and record that the archive's normalization `eO` is then 1, that the coefficient module is
ℚ_p/ℤ_p with the cyclotomic character to the power `-2m`, and that the order of the Selmer
group is `p ^ length`.
-/

namespace KTheoryGrowth

noncomputable section

open Formalism.ConjugateSelfDual Formalism.GaloisCohomology ReciprocityTheory.Gal
open UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.SmallClassNumbers

/-- `⊥` (the image of ℤ_p) inside the archive's p-adic algebraic closure is ℤ_p. -/
def padicBotEquiv (p : Nat.Primes) :
    ↥(⊥ : Subalgebra ℤ_[(p : ℕ)] (PadicAlgCl (p : ℕ))) ≃ₐ[ℤ_[(p : ℕ)]] ℤ_[(p : ℕ)] :=
  Algebra.botEquivOfInjective (by
    rw [IsScalarTower.algebraMap_eq ℤ_[(p : ℕ)] ℚ_[(p : ℕ)] (PadicAlgCl (p : ℕ))]
    exact (algebraMap ℚ_[(p : ℕ)] (PadicAlgCl (p : ℕ))).injective.comp
      (IsFractionRing.injective ℤ_[(p : ℕ)] ℚ_[(p : ℕ)]))

/-- The copy of the p-adic integers inside the archive's p-adic algebraic closure,
as an archive coefficient ring. -/
def integralCoeff (p : Nat.Primes) : Coef (p : ℕ) :=
  ⟨⊥, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (padicBotEquiv p).symm,
    Module.Finite.equiv (padicBotEquiv p).symm.toLinearEquiv⟩

/-- The archive's normalization is trivial for ℤ_p-coefficients. -/
theorem integralCoeff_eO (p : Nat.Primes) : eO (p : ℕ) (integralCoeff p).O = 1 :=
  length_quotient_prime_of_padicIntEquiv (padicBotEquiv p).symm.toRingEquiv

/-- The archive's coefficient module `O ⊗ ℚ_p/ℤ_p` is ℚ_p/ℤ_p. -/
def integralCoeffQuotientEquiv (p : Nat.Primes) :
    QO (p : ℕ) (integralCoeff p).O ≃ₗ[ℤ_[(p : ℕ)]] QZ (p : ℕ) :=
  (TensorProduct.congr (padicBotEquiv p).toLinearEquiv
    (LinearEquiv.refl ℤ_[(p : ℕ)] (QZ (p : ℕ)))).trans (TensorProduct.lid _ _)

/-- Under that identification, the archive's Galois action is the `e`-th power of the
p-adic cyclotomic character. -/
theorem integralCoeffQuotientEquiv_twist (p : Nat.Primes) (e : ℤ)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : QO (p : ℕ) (integralCoeff p).O) :
    integralCoeffQuotientEquiv p
      (twist₂ (p : ℕ) (chiO ℚ (AlgebraicClosure ℚ) (p : ℕ) (integralCoeff p).O ^ e) g x) =
        (cycZ ℚ (AlgebraicClosure ℚ) (p : ℕ) g ^ e) • integralCoeffQuotientEquiv p x := by
  let O := (integralCoeff p).O
  let χ := cycZ ℚ (AlgebraicClosure ℚ) (p : ℕ)
  have h : (((chiO ℚ (AlgebraicClosure ℚ) (p : ℕ) O ^ e) g : Oˣ) : O) =
      algebraMap ℤ_[(p : ℕ)] O ((χ g ^ e : ℤ_[(p : ℕ)]ˣ) : ℤ_[(p : ℕ)]) := by
    rw [MonoidHom.zpow_apply, chiO, MonoidHom.comp_apply, ← map_zpow]
    rfl
  rw [scalRep_apply, h, algebraMap_smul, map_smul]
  rfl

/-- **The Selmer group.** Continuous H¹ of Gal(ℚ̄/ℚ) with coefficients ℚ_p/ℤ_p(−2m)
(discrete topology), consisting of classes that vanish on every inertia group and on the
decomposition groups of the places above `2p` (i.e. above 2 and above p). -/
abbrev integralSelmer (m : ℕ) (p : Nat.Primes) :=
  ShaU (twist₂ (p : ℕ) (chiO ℚ (AlgebraicClosure ℚ) (p : ℕ) (integralCoeff p).O ^
    (-((2 * m : ℕ) : ℤ)))) ((p : ℕ) * 2) ⊤

/-- Its length, exactly the archive's `len` at these parameters. -/
def integralSelmerLength (m : ℕ) (p : Nat.Primes) : ℕ∞ :=
  len (AlgebraicClosure ℚ) (p : ℕ) (integralCoeff p) (2 * m)

/-- A finite-length Selmer group has order `p ^ length`. -/
theorem card_integralSelmer {m : ℕ} {p : Nat.Primes} (hfinite : integralSelmerLength m p ≠ ⊤) :
    Nat.card (integralSelmer m p) = (p : ℕ) ^ (integralSelmerLength m p).toNat :=
  card_eq_prime_pow_length_of_padicIntEquiv (padicBotEquiv p).symm.toRingEquiv hfinite

/-- The archive's `Bound`, specialized: weighted Selmer lengths over any finite set of
eligible primes are at most `C (2m+1)^A`. -/
theorem selmerLengthBound_of_archive (hbound : Bound) : SelmerLengthBound integralSelmerLength := by
  obtain ⟨C, A, h⟩ := hbound
  refine ⟨C, A, fun m hm s hs => ?_⟩
  have : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.instIsAlgClosure ℚ
    all_goals try rfl
  have he : Even (2 * m) := ⟨m, by omega⟩
  obtain ⟨hfinite, hsum⟩ := h (AlgebraicClosure ℚ) (2 * m) (by omega) he integralCoeff s
    (fun p hp => by
      rw [show 2 * (2 * m) = 4 * m by omega]
      exact hs p hp)
  refine ⟨hfinite, ?_⟩
  simpa only [integralSelmerLength, integralCoeff_eO, ENat.toNat_one,
    Nat.cast_one, div_one, Nat.cast_mul, Nat.cast_ofNat] using hsum

end

end KTheoryGrowth
