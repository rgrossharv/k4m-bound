import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Torsion

/-!
# Logarithmic growth from a bound on Selmer lengths

The order sequence can be instantiated with the orders of the torsion subgroups
of the higher algebraic K-groups of ℤ. The arithmetic comparison is an explicit
hypothesis, since the Quillen–Lichtenbaum comparison is external to this file.
-/

namespace KTheoryGrowth

/-- The primes covered by the archive's bound at twist `e = 2 * m`. -/
def Eligible (m p : ℕ) : Prop :=
  5 ≤ p ∧ ¬ (p - 1) ∣ 4 * m

/-- The small primes omitted by the archive already satisfy the divisibility exception. -/
theorem not_eligible_iff {m p : ℕ} (hp : p.Prime) :
    ¬ Eligible m p ↔ (p - 1) ∣ 4 * m := by
  classical
  constructor
  · intro h
    by_contra hdvd
    have hp5 : 5 ≤ p := by
      have hp2 := hp.two_le
      rcases hp.eq_two_or_odd with rfl | hodd
      · exact (hdvd (by simp)).elim
      · by_contra hsmall
        have hp3 : p = 3 := by omega
        subst p
        exact hdvd ⟨2 * m, by omega⟩
    exact h ⟨hp5, hdvd⟩
  · intro h h'
    exact h'.2 h

/-- The torsion order of a degree-indexed family of additive groups. -/
noncomputable def torsionOrder (K : ℕ → Type*) [∀ n, AddCommGroup (K n)] (n : ℕ) : ℕ :=
  Nat.card (AddCommGroup.torsion (K n))

/-- The p-primary subgroup has order `p ^ v_p(N)` in a finite abelian group of order N. -/
theorem card_primaryComponent (G : Type*) [AddCommGroup G] [Finite G]
    (p : ℕ) [Fact p.Prime] :
    Nat.card (AddCommGroup.primaryComponent G p) = p ^ (Nat.card G).factorization p := by
  change Nat.card (CommGroup.primaryComponent (Multiplicative G) p) = _
  let P : Sylow p (Multiplicative G) := Classical.choice inferInstance
  have hP : CommGroup.primaryComponent (Multiplicative G) p = P.1 := by
    refine le_antisymm (CommGroup.primaryComponent.isPGroup.le_sylow_of_normal P) ?_
    intro g hg
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  rw [hP]
  exact P.card_eq_multiplicity

/-- Triviality of the primary component excludes the prime from the order. -/
theorem not_dvd_card_of_subsingleton_primaryComponent (G : Type*) [AddCommGroup G] [Finite G]
    (p : ℕ) [hp : Fact p.Prime] [Subsingleton (AddCommGroup.primaryComponent G p)] :
    ¬ p ∣ Nat.card G := by
  have hc := card_primaryComponent G p
  rw [Nat.card_unique, ← pow_zero (a := p)] at hc
  have hzero := (Nat.pow_right_injective hp.out.two_le hc).symm
  simpa [Nat.factorization_eq_zero_iff, hp.out, Nat.card_pos.ne'] using hzero

/-- The weighted sum of Selmer lengths on any finite set of eligible primes. -/
def SelmerLengthBoundedBy (selmerLength : ℕ → Nat.Primes → ℕ∞) (bound : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ s : Finset Nat.Primes,
    (∀ p ∈ s, Eligible m p) →
    (∀ p ∈ s, selmerLength m p ≠ ⊤) ∧
    ∑ p ∈ s, Real.log (p : ℕ) * ((selmerLength m p).toNat : ℝ) ≤ bound m

/-- The polynomial version of the weighted bound, with ramification index one. -/
def SelmerLengthBound (selmerLength : ℕ → Nat.Primes → ℕ∞) : Prop :=
  ∃ C A : ℕ, SelmerLengthBoundedBy selmerLength (fun m => C * (2 * (m : ℝ) + 1) ^ A)

/-- The prime factorization formula for the logarithm of a positive order. -/
theorem log_eq_sum_primeFactors {N : ℕ} (hN : N ≠ 0) :
    Real.log (N : ℝ) = ∑ p ∈ N.primeFactors, Real.log (p : ℝ) * (N.factorization p : ℝ) := by
  classical
  have hfactor : ∏ p ∈ N.primeFactors, p ^ N.factorization p = N :=
    Nat.prod_factorization_pow_eq_self hN
  have hcast : ∏ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p = (N : ℝ) := by
    exact_mod_cast hfactor
  rw [← hcast, Real.log_prod]
  · exact Finset.sum_congr rfl fun p _ => by rw [Real.log_pow, mul_comm]
  · intro p hp
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)

/-- The weighted Selmer lengths over the prime support recover the logarithm of the order. -/
theorem log_order_eq_sum_selmer_lengths
    {selmerLength : ℕ → Nat.Primes → ℕ∞} {m N : ℕ} (hN : N ≠ 0)
    (hs : ∀ p : Nat.Primes, (p : ℕ) ∈ N.primeFactors → Eligible m p)
    (hcompare : ∀ p : Nat.Primes, Eligible m p →
      (N.factorization p : ℕ∞) = selmerLength m p) :
    Real.log (N : ℝ) = ∑ p ∈ N.primeFactors.subtype Nat.Prime,
      Real.log (p : ℕ) * ((selmerLength m p).toNat : ℝ) := by
  rw [log_eq_sum_primeFactors hN, ← Finset.sum_subtype_of_mem _
    (fun _ hp => Nat.prime_of_mem_primeFactors hp)]
  exact Finset.sum_congr rfl fun p hp => by
    rw [← hcompare p (hs p (Finset.mem_subtype.mp hp)), ENat.toNat_natCast]

/-- Control of an order whose prime-power exponents are Selmer lengths. -/
theorem log_order_le_of_weighted_bound
    {selmerLength : ℕ → Nat.Primes → ℕ∞} {bound : ℕ → ℝ} {m N : ℕ}
    (hbound : SelmerLengthBoundedBy selmerLength bound)
    (hm : 0 < m) (hN : N ≠ 0)
    (hcompare : ∀ p : Nat.Primes, Eligible m p →
      (N.factorization p : ℕ∞) = selmerLength m p)
    (hvanish : ∀ p : Nat.Primes, ¬ Eligible m p → ¬ (p : ℕ) ∣ N) :
    Real.log (N : ℝ) ≤ bound m := by
  have hs (p : Nat.Primes) (hp : (p : ℕ) ∈ N.primeFactors) : Eligible m p := by
    by_contra h
    exact hvanish p h (Nat.dvd_of_mem_primeFactors hp)
  rw [log_order_eq_sum_selmer_lengths hN hs hcompare]
  exact (hbound m hm _ fun p hp => hs p (Finset.mem_subtype.mp hp)).2

/-- A nonzero integer witness controlling the eligible lengths is divisible by the order. -/
theorem order_dvd_of_selmer_factorization
    {selmerLength : ℕ → Nat.Primes → ℕ∞} {m N d : ℕ}
    (hN : N ≠ 0) (hd : d ≠ 0)
    (hcompare : ∀ p : Nat.Primes, Eligible m p →
      (N.factorization p : ℕ∞) = selmerLength m p)
    (hvanish : ∀ p : Nat.Primes, ¬ Eligible m p → ¬ (p : ℕ) ∣ N)
    (hcontrol : ∀ p : Nat.Primes, Eligible m p →
      selmerLength m p ≤ (d.factorization p : ℕ∞)) :
    N ∣ d := by
  apply (Nat.factorization_le_iff_dvd hN hd).mp
  intro p
  by_cases hp : p.Prime
  · by_cases he : Eligible m p
    · exact ENat.natCast_le_natCast.mp ((hcompare ⟨p, hp⟩ he).le.trans (hcontrol ⟨p, hp⟩ he))
    · simp only [Nat.factorization_eq_zero_of_not_dvd (hvanish ⟨p, hp⟩ he), zero_le]
  · simp only [Nat.factorization_eq_zero_of_not_prime N hp, zero_le]

/-- A logarithmic bound with coefficient `A` gives a power bound of exponent `A`. -/
theorem order_le_pow_of_log_le {N m A : ℕ} (hN : 0 < N)
    (h : Real.log (N : ℝ) ≤ A * Real.log ((m : ℝ) + 1)) :
    N ≤ (m + 1) ^ A := by
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [← Real.log_pow] at h
  exact_mod_cast (Real.log_le_log_iff (Nat.cast_pos.mpr hN) (pow_pos hpos A)).mp h

/-- The product of orders on eligible primes is finite and obeys the original bound. -/
theorem exists_selmer_order_le
    {selmerLength : ℕ → Nat.Primes → ℕ∞} {bound : ℕ → ℝ} {m : ℕ}
    (hbound : SelmerLengthBoundedBy selmerLength bound) (hm : 0 < m) :
    ∃ N : ℕ, 0 < N ∧
      (∀ p : Nat.Primes, Eligible m p → (N.factorization p : ℕ∞) = selmerLength m p) ∧
      (∀ p : Nat.Primes, ¬ Eligible m p → ¬ (p : ℕ) ∣ N) ∧
      Real.log (N : ℝ) ≤ bound m := by
  classical
  have singleton (p : Nat.Primes) (hp : Eligible m p) :
      selmerLength m p ≠ ⊤ ∧
        Real.log (p : ℕ) * ((selmerLength m p).toNat : ℝ) ≤ bound m := by
    have h := hbound m hm {p} (by simpa using hp)
    exact ⟨h.1 p (Finset.mem_singleton_self p), by simpa using h.2⟩
  let exponent (p : ℕ) : ℕ :=
    if hp : p.Prime then
      if Eligible m p then (selmerLength m ⟨p, hp⟩).toNat else 0
    else 0
  let s := Finset.range (⌊Real.exp (bound m)⌋₊ + 1)
  have hmem (p : ℕ) (hne : exponent p ≠ 0) : p ∈ s := by
    by_cases hp : p.Prime
    · by_cases he : Eligible m p
      · have h := singleton ⟨p, hp⟩ he
        have hn : 1 ≤ (selmerLength m ⟨p, hp⟩).toNat := by
          exact Nat.one_le_iff_ne_zero.mpr (by simpa [exponent, hp, he] using hne)
        have hmul := mul_le_mul_of_nonneg_left (Nat.one_le_cast.mpr hn)
          (Real.log_natCast_nonneg p)
        rw [mul_one] at hmul
        have hexp := (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hp.pos)).mp (hmul.trans h.2)
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hexp))
      · exact (hne (by simp [exponent, hp, he])).elim
    · exact (hne (by simp [exponent, hp])).elim
  let f : ℕ →₀ ℕ := Finsupp.onFinset s exponent hmem
  have hf (p : ℕ) (hp : p ∈ f.support) : p.Prime := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hp) (by simp [f, exponent, hn])
  let N := f.prod (· ^ ·)
  have hN : 0 < N := by
    unfold N Finsupp.prod
    exact Finset.prod_pos fun p hp => pow_pos (hf p hp).pos _
  have hfac : N.factorization = f := Nat.prod_pow_factorization_eq_self hf
  have hcompare (p : Nat.Primes) (hp : Eligible m p) :
      (N.factorization p : ℕ∞) = selmerLength m p := by
    rw [hfac]
    have he : exponent (p : ℕ) = (selmerLength m p).toNat := by
      simp only [exponent, dif_pos p.2, if_pos hp]
      cases p
      rfl
    exact (congrArg (fun n : ℕ => (n : ℕ∞)) he).trans
      (ENat.natCast_toNat (singleton p hp).1)
  have hvanish (p : Nat.Primes) (hp : ¬ Eligible m p) : ¬ (p : ℕ) ∣ N := by
    have hzero : N.factorization p = 0 := by rw [hfac]; simp [f, exponent, hp, p.2]
    simpa [Nat.factorization_eq_zero_iff, p.2, hN.ne'] using hzero
  exact ⟨N, hN, hcompare, hvanish,
    log_order_le_of_weighted_bound hbound hm hN.ne' hcompare hvanish⟩

/-- Conversion of a bound in the twist parameter `2 * m` to one in `m`. -/
theorem polynomial_bound_of_twice_bound {f : ℕ → ℝ} {C A : ℕ}
    (h : ∀ m > 0, f m ≤ C * (2 * (m : ℝ) + 1) ^ A) :
    ∃ D B : ℕ, 0 < D ∧ 0 < B ∧ ∀ m > 0, f m ≤ D * ((m : ℝ) + 1) ^ B := by
  refine ⟨C * 2 ^ A + 1, A + 1, by positivity, by omega, fun m hm => ?_⟩
  calc
    f m ≤ C * (2 * (m : ℝ) + 1) ^ A := h m hm
    _ ≤ (C : ℝ) * (2 * ((m : ℝ) + 1)) ^ A := by gcongr; linarith
    _ ≤ (↑(C * 2 ^ A + 1) : ℝ) * ((m : ℝ) + 1) ^ (A + 1) := by
      push_cast
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul (le_add_of_nonneg_right zero_le_one)
        (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) m]) (Nat.le_succ _))
        (by positivity) (by positivity)

end KTheoryGrowth

