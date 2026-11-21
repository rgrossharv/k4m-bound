import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.ClassNumberThree

/-!
# The archive's `ShaU` is the classical Selmer group

This file proves in Lean that the archive's Selmer group `ShaU ρ n ⊤` equals the classical
Selmer group defined with the textbook local conditions. `ShaU` is the group whose lengths the
archive's `Bound` controls.

**Classical group.** Choose one place `B q` of `Ω = ℚ̄` above each rational prime `q`. The
classical group consists of the classes in continuous `H¹(G_ℚ, M)` that

* restrict to zero on the inertia group `I_{B q}` at every prime `q` (unramified everywhere), and
* restrict to zero on the decomposition group `D_{B q}` at every prime `q ∣ n` (locally trivial
  at the primes dividing `n`).

**Archive's group.** `ShaU ρ n ⊤` imposes the same two conditions at *every* valuation subring of
`Ω`, all conjugates included, together with the trivial valuation.

The theorem `shaU_eq_classicalSelmer` says the two groups agree for every choice of places. The
proof uses three facts:

1. A class that vanishes on a subgroup also vanishes on each of its conjugates
   (`resU_eq_zero_of_conj`, proved here at the cocycle level).
2. All places of `Ω` above `p` are Galois-conjugate, and so are their decomposition and inertia
   groups. This is the archive's `placesQ`, which lies in the light import closure.
3. A valuation subring that is not `⊤` lies above some rational prime (`exists_prime_of_ne_top`,
   proved here), and the trivial valuation has trivial inertia (the archive's `places`).

For the K-theory application, `n = 2p` and `M = ℚ_p/ℤ_p(−2m)`. The classical group is then
Aki Salmons' `S_{p,2m}` (note, eq. (1)), which is dual to `K_{4m}(ℤ){p}`. So clause 2 of
`ComparisonHypotheses` holds with equality (see `KTheorySpecialization.lean`).
-/

noncomputable section

open ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base Formalism.ConjugateSelfDual

namespace SelmerComparison

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-! ## The cohomology is continuous cohomology for the Krull topology -/

/-- The topology on `G_ℚ = Gal(Ω/ℚ)` is Mathlib's Krull topology. -/
example : (inferInstance : TopologicalSpace (G ℚ Ω)) = krullTopology ℚ Ω := rfl

/-- The cocycles behind `H1U` are the *continuous* 1-cocycles. -/
example (ρ : Representation R (G ℚ Ω) M) (U : Subgroup (G ℚ Ω)) (f : U → M) :
    f ∈ Z1U ρ U ↔ Continuous f ∧ ∀ g h, f (g * h) = f g + ρ g (f h) :=
  mem_Z1_iff_cocycle _ f

/-! ## The classical Selmer group -/

/-- The textbook family of local conditions for a choice `B` of one place above each prime:
inertia at every prime, decomposition at the primes dividing `n`. -/
def classicalFam (B : Nat.Primes → ValuationSubring Ω) (n : ℕ) : Set (Subgroup (G ℚ Ω)) :=
  {D | (∃ q, D = Ine (F := ℚ) (B q)) ∨ ∃ q : Nat.Primes, (q : ℕ) ∣ n ∧ D = Dec (F := ℚ) (B q)}

/-- The classical Selmer group: classes in continuous `H¹(G_ℚ, M)` that are unramified at every
prime and locally trivial at the primes dividing `n`. -/
def classicalSelmer (ρ : Representation R (G ℚ Ω) M) (B : Nat.Primes → ValuationSubring Ω)
    (n : ℕ) : Submodule R (H1U ρ ⊤) :=
  LocSel ρ ⊤ (classicalFam B n)

/-- A choice of places exists: every rational prime has a place of `Ω` above it. -/
theorem exists_places :
    ∃ B : Nat.Primes → ValuationSubring Ω, ∀ q : Nat.Primes, (B q).valuation (q : Ω) < 1 :=
  ⟨fun q => ((UpperTheory.V.Chr.placesQ Ω).1 q q.2).choose,
    fun q => ((UpperTheory.V.Chr.placesQ Ω).1 q q.2).choose_spec⟩

/-! ## Cocycle lemmas -/

omit [IsAlgClosure ℚ Ω] in
/-- If a class vanishes on `D'` and `u⁻¹ D u ≤ D'`, it vanishes on `D`. -/
theorem resU_eq_zero_of_conj (ρ : Representation R (G ℚ Ω) M) {D D' : Subgroup (G ℚ Ω)}
    (u : G ℚ Ω) (hu : ∀ x ∈ D, u⁻¹ * x * u ∈ D') (x : H1U ρ ⊤)
    (hx : resU ρ (inf_le_left : (⊤ : Subgroup (G ℚ Ω)) ⊓ D' ≤ ⊤) x = 0) :
    resU ρ (inf_le_left : (⊤ : Subgroup (G ℚ Ω)) ⊓ D ≤ ⊤) x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [resU_mk_eq_zero] at hx ⊢
  obtain ⟨m', hm'⟩ := hx
  have hcoc := ((mem_Z1_iff_cocycle _ _).1 z.2).2
  let t : (⊤ : Subgroup (G ℚ Ω)) → (⊤ : Subgroup (G ℚ Ω)) := id
  let w : G ℚ Ω → (⊤ : Subgroup (G ℚ Ω)) := fun g => ⟨g, Subgroup.mem_top g⟩
  refine ⟨ρ u m' - z.1 (w u), fun d => ?_⟩
  have hd' : u⁻¹ * d.1 * u ∈ (⊤ : Subgroup (G ℚ Ω)) ⊓ D' :=
    ⟨Subgroup.mem_top _, hu _ d.2.2⟩
  have h1 := hm' ⟨_, hd'⟩
  have e : w u * w (u⁻¹ * d.1 * u) = w d.1 * w u := by
    apply Subtype.ext; simp [w, mul_assoc]
  have h2 := hcoc (w u) (w (u⁻¹ * d.1 * u))
  have h3 := hcoc (w d.1) (w u)
  rw [e, h3] at h2
  have hρ : ρ u (ρ (u⁻¹ * d.1 * u) m') = ρ d.1 (ρ u m') := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2; group
  change z.1 (w d.1) = ρ d.1 (ρ u m' - z.1 (w u)) - (ρ u m' - z.1 (w u))
  change z.1 (w (u⁻¹ * d.1 * u)) = ρ (u⁻¹ * d.1 * u) m' - m' at h1
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype] at h2
  change z.1 (w d.1) + ρ d.1 (z.1 (w u)) = z.1 (w u) + ρ u (z.1 (w (u⁻¹ * d.1 * u))) at h2
  rw [h1, map_sub, hρ] at h2
  rw [map_sub, ← sub_eq_zero]
  rw [← sub_eq_zero] at h2
  convert h2 using 1
  abel

omit [IsAlgClosure ℚ Ω] in
/-- Every class vanishes on the trivial subgroup. -/
theorem resU_bot_eq_zero (ρ : Representation R (G ℚ Ω) M) (x : H1U ρ ⊤) :
    resU ρ (inf_le_left : (⊤ : Subgroup (G ℚ Ω)) ⊓ ⊥ ≤ ⊤) x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [resU_mk_eq_zero]
  refine ⟨0, fun d => ?_⟩
  have hd : d.1 = 1 := Subgroup.mem_bot.1 d.2.2
  have hz1 : z.1 1 = 0 := by
    have h := ((mem_Z1_iff_cocycle _ _).1 z.2).2 1 1
    simp only [mul_one, map_one, Module.End.one_apply] at h
    exact add_eq_left.1 h.symm
  simp only [map_zero, sub_zero]
  convert hz1 using 2
  exact Subtype.ext hd

/-! ## Places -/

/-- A valuation subring of `Ω` other than `⊤` lies above some rational prime. -/
theorem exists_prime_of_ne_top (A : ValuationSubring Ω) (hA : A ≠ ⊤) :
    ∃ p : ℕ, p.Prime ∧ A.valuation (p : Ω) < 1 := by
  by_contra hcon
  push Not at hcon
  apply hA
  -- every nonzero natural number is a unit of `A`
  have hnat : ∀ n : ℕ, n ≠ 0 → A.valuation (n : Ω) = 1 := by
    intro n hn
    refine le_antisymm ((A.valuation_le_one_iff _).2 (natCast_mem A n)) (not_lt.1 fun h => ?_)
    obtain ⟨p, hp, hpA⟩ := ((UpperTheory.V.Chr.placesQ Ω).2.1 A n hn).1 h
    exact (not_lt.2 (hcon p (Nat.prime_of_mem_primeFactors hp))) hpA
  have hint : ∀ z : Ω, IsIntegral ℤ z → A.valuation z ≤ 1 := by
    intro z hz
    obtain ⟨y, rfl⟩ :=
      (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp (hz.tower_top (A := A))
    exact A.valuation_le_one y
  ext x
  simp only [ValuationSubring.mem_top, iff_true]
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (C := Ω)).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy, hyx⟩ := halg.exists_integral_multiple
  have h1 := hint _ hyx
  rw [zsmul_eq_mul, map_mul] at h1
  have hy1 : A.valuation (y : Ω) = 1 := by
    rcases Int.natAbs_eq y with h | h
    · rw [h, Int.cast_natCast]; exact hnat _ (Int.natAbs_ne_zero.2 hy)
    · rw [h, Int.cast_neg, Int.cast_natCast, Valuation.map_neg]
      exact hnat _ (Int.natAbs_ne_zero.2 hy)
  rw [hy1, one_mul] at h1
  exact (A.valuation_le_one_iff x).1 h1

/-! ## The comparison -/

omit [IsAlgClosure ℚ Ω] in
/-- Unfolded membership in the archive's group. -/
theorem mem_shaU (ρ : Representation R (G ℚ Ω) M) (n : ℕ) (x : H1U ρ ⊤) :
    x ∈ ShaU ρ n ⊤ ↔ ∀ D ∈ shaFam ℚ Ω n, resU ρ (inf_le_left : (⊤ : Subgroup (G ℚ Ω)) ⊓ D ≤ ⊤) x = 0 :=
  mem_locSel

/-- **The archive's `ShaU ρ n ⊤` is the classical Selmer group**, for every choice of one place
above each prime: continuous `H¹(G_ℚ, M)`, unramified everywhere, locally trivial at the primes
dividing `n`. -/
theorem shaU_eq_classicalSelmer (ρ : Representation R (G ℚ Ω) M) (n : ℕ) (hn : n ≠ 0)
    (B : Nat.Primes → ValuationSubring Ω) (hB : ∀ q : Nat.Primes, (B q).valuation (q : Ω) < 1) :
    ShaU ρ n ⊤ = classicalSelmer ρ B n := by
  have hP := UpperTheory.V.Chr.placesQ Ω
  ext x
  rw [mem_shaU, classicalSelmer, mem_locSel]
  constructor
  · -- archive ⊆ classical: the classical conditions are among the archive's
    rintro h D (⟨q, rfl⟩ | ⟨q, hqn, rfl⟩)
    · exact h _ (Or.inr ⟨B q, rfl⟩)
    · refine h _ (Or.inl ⟨B q, ?_, rfl⟩)
      exact (hP.2.1 (B q) n hn).2 ⟨q, Nat.mem_primeFactors.2 ⟨q.2, hqn, hn⟩, hB q⟩
  · -- classical ⊆ archive: each archive condition is conjugate to a classical one, or trivial
    rintro h D (⟨A, hA, rfl⟩ | ⟨A, rfl⟩)
    · obtain ⟨p, hp, hpA⟩ := (hP.2.1 A n hn).1 hA
      have hpp := Nat.prime_of_mem_primeFactors hp
      obtain ⟨u, hu, -⟩ := hP.2.2 p A (B ⟨p, hpp⟩) hpp hpA (hB ⟨p, hpp⟩)
      exact resU_eq_zero_of_conj ρ u hu x
        (h _ (Or.inr ⟨⟨p, hpp⟩, Nat.dvd_of_mem_primeFactors hp, rfl⟩))
    · by_cases htop : A = ⊤
      · subst htop
        have hbot : Ine (F := ℚ) (⊤ : ValuationSubring Ω) = ⊥ :=
          ((UpperTheory.V.Base.places ℚ Ω 2 ⊤).2.1 rfl).1
        rw [hbot]
        exact resU_bot_eq_zero ρ x
      · obtain ⟨p, hpp, hpA⟩ := exists_prime_of_ne_top A htop
        obtain ⟨u, -, hu⟩ := hP.2.2 p A (B ⟨p, hpp⟩) hpp hpA (hB ⟨p, hpp⟩)
        exact resU_eq_zero_of_conj ρ u hu x (h _ (Or.inl ⟨⟨p, hpp⟩, rfl⟩))

/-- In particular the classical group does not depend on the choice of places. -/
theorem classicalSelmer_indep (ρ : Representation R (G ℚ Ω) M) (n : ℕ) (hn : n ≠ 0)
    (B B' : Nat.Primes → ValuationSubring Ω) (hB : ∀ q : Nat.Primes, (B q).valuation (q : Ω) < 1)
    (hB' : ∀ q : Nat.Primes, (B' q).valuation (q : Ω) < 1) :
    classicalSelmer ρ B n = classicalSelmer ρ B' n := by
  rw [← shaU_eq_classicalSelmer ρ n hn B hB, shaU_eq_classicalSelmer ρ n hn B' hB']

end SelmerComparison
