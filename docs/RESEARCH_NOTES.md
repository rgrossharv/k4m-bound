# Research notes: what a polynomial bound for |K₄ₘ(ℤ)| requires

> Copied from the working `automath` directory. Lean files named here (`ArchiveSplit.lean`,
> `ArchiveCongruence.lean`, `ArchivePolynomial.lean`, …) live there, not in this repo. They
> concern the conditional *polynomial* bound; this repo contains only what the proven
> log-polynomial bound needs.

Status labels: **[Lean]** checked in this repository with only `propext`, `Classical.choice` and
`Quot.sound`; **[Thm]** published theorem, external to Lean; **[Computed]** our computation;
**[Heur]** heuristic only; **[Open]** no proof known. Citations marked *(verify)* are from memory
and should be checked before reuse.

## 0. Summary

The target is: there exist constants B and D such that |K₄ₘ(ℤ)| ≤ B(m+1)^D for every m ≥ 1. It splits into two
independent inputs, and the split is now formalized:

1. **Small primes (per-prime growth).** For each prime p below a cutoff, p^{v_p|K₄ₘ(ℤ)|} ≤ C(m+1)^E.
2. **Large primes (uniform vanishing).** The large-prime part of the gcd of the two archive
   witnesses is at most B(m+1)^D.

`card_four_mul_le_of_small_prime_powers` in `ArchiveSplit.lean` **[Lean]** proves that (1) and (2) imply the
polynomial bound (given `KTheoryComparison`). It needs neither vanishing below the cutoff nor the
regularity inputs at 7 and 11, and it contains the previous interim theorem as the case C = 1, E = 0
(`card_four_mul_le_of_large_prime_gcd_bound'`).

The findings below say what each input really demands. In short, input (2) is a uniform
Vandiver-type statement about even eigenspaces. Input (1) is automatic at every prime where Vandiver
holds; at a hypothetical Vandiver counterexample it reduces, via Ferrero–Washington (proved in the
archive), to a p-adic Diophantine property of Iwasawa zeros. Neither is within reach of known
techniques. The obstruction is mathematical, not a gap in the formalization.

## 1. Reformulation through the Lichtenbaum formula

**[Thm]** For n = 2m+1 ≥ 3, the Lichtenbaum conjecture for ℚ (known up to sign and powers of 2) gives

  ζ*(−2m) = ± (|K₄ₘ(ℤ)| / |K₄ₘ₊₁(ℤ)_tors|) · R_{2m+1},  with  ζ*(−2m) = ζ′(−2m) = (−1)^m (2m)! ζ(2m+1) / (2(2π)^{2m}),

where R_{2m+1} is the Borel regulator of the rank-one group K₄ₘ₊₁(ℤ) and |K₄ₘ₊₁(ℤ)_tors| ≤ 2
(Weibel's KZ survey, Lichtenbaum section; Rognes–Weibel; Huber–Kings *(verify normalization)*).

**Consequence.** Up to the powers of 2 already handled, |K₄ₘ(ℤ)| is the index of the Beilinson–Soulé
cyclotomic element in K₄ₘ₊₁(ℤ)/tors. So the polynomial bound is equivalent to the **regulator lower bound**

  R_{2m+1} ≥ (2m)! ζ(2m+1) / ((2π)^{2m} · poly(m)),

that is, the integral cyclotomic element is divisible by at most poly(m). **[Open]** This is a
Lehmer-type lower bound for higher regulators. GRH (claimed by the archive) does not help here: the
L-value ζ(2m+1) is known exactly, and the unknown quantity is the regulator.

## 2. The odd side cannot decide the question

**[Thm]** If p > 2m+3 and p divides |K₄ₘ(ℤ)|, then the ω^{−2m} eigenspace of the p-class group of ℚ(ζ_p) is nonzero
(K₄ₘ(ℤ)/p is that eigenspace; Weibel, Thm 105 area). Leopoldt reflection (Washington, Thm 10.9)
then makes the ω^{1+2m} eigenspace nonzero, and Herbrand–Ribet gives **p | B_{p−1−2m}**. Call
(p, p−1−2m) an *edge irregular pair* for m.

By Glaisher, for p > 2m+1 the condition p | B_{p−1−2m} is equivalent to H^{(2m)}_{p−1} ≡ 0 (mod p²). Our test uses the Voronoi
congruence with c = 2: p | B_{p−1−2m} ⇔ Σ_{a≤(p−1)/2} a^{−(2m+1)} ≡ 0 (mod p), whenever 2^{2m} ≢ 1 (mod p).

**[Computed]** For p < 40000 and m ≤ 6 (the cases with 2^{2m} ≢ 1 mod p), the edge pairs are

| m | primes p with p ∣ B_{p−1−2m} |
|---|---|
| 1 | 16843 (Wolstenholme prime) |
| 2 | 37 (the classical pair (37, 32)) |
| 4 | 67, 877 |
| 5 | 9311 |

For p < 4000 and m ≤ 30, the search also recovers (59,44), (101,68), (149,130) and (157,110), among
others. Reproduce with `python3 -I edge_irregular_pairs.py N M` (primes below N, m ≤ M). Cases with
2^{2m} ≡ 1 (mod p) are printed as `undecided`.

**Key observation.** K₄(ℤ) = 0 (Rognes) and K₈(ℤ) = 0 (Dutour Sikirić–Elbaz-Vincent–Kupers–Martinet
*(verify)*) are theorems. So 16843 and 37 satisfy the odd-side condition but do *not* divide the group.

**[Heur]** For fixed m the events p | B_{p−1−2m} behave like probability 1/p, and Σ 1/p diverges. So
infinitely many edge primes are expected for every fixed m, just as infinitely many Wolstenholme primes
are expected. **Hence no argument using only odd-side information (Bernoulli numbers, values of
L_p, or congruence data that is implied by them) can give a polynomial bound.** A proof must use
even-side information, the Vandiver side, which is exactly what is hard.

Relation to the archive witnesses: a prime that genuinely divides |K₄ₘ(ℤ)| divides the witness at
*every* admissible auxiliary prime. Adding auxiliary primes therefore cannot remove it, and
`local_trace_conditions_allow_large_residual` **[Lean]** shows that local trace data cannot rule out
spurious shared factors. The gcd route thus reduces to the same even-side question, with extra
spurious factors on top.

## 3. Input (1): per-prime growth via Iwasawa theory

Fix p ≥ 5 and a residue class of 2m mod p−1. Let X′ be the Galois group of the maximal abelian
unramified pro-p extension of ℚ(ζ_{p^∞}) in which the primes above p split, and let Y be its relevant
eigencomponent. Inflation–restriction together with the strict Selmer description in `ArchiveSelmer.lean` gives,
up to the twist convention and a bounded error,

  v_p|K₄ₘ(ℤ)| ≤ v_p |Y / (γ − u^{2m}) Y|.

**[Thm, in archive]** Ferrero–Washington (`UpperTheory.V.FW.ferreroWashington`) gives μ = 0, so Y is
finitely generated over ℤ_p of rank λ = λ_p. If α₁,…,α_λ are the eigenvalues of γ on Y and
s_i = log_p α_i / log_p u, then

  v_p|K₄ₘ(ℤ)| ≤ Σ_i v_p(u^{2m} − α_i) + c_p ≤ λ_p · (1 + max_i v_p(2m − s_i)) + c_p.

Finiteness of K₄ₘ(ℤ) guarantees 2m ≠ s_i. Consequences:

* **Vacuous where Vandiver holds.** Then Y vanishes in the even eigenspaces and v_p = 0 for all m.
  This is known for all p < 2³¹ (Hart–Harvey–Ong), so hypothesis `hsmall` in `ArchiveSplit.lean` holds with
  C = 1 and E = 0 for every cutoff up to 2³¹ (as an external input).
* **Bounded on average.** For each fixed p, the average of v_p(2m − s) over m ≤ X is O(1).
* **Polynomial growth at a counterexample prime is a Diophantine question.** At a prime where Vandiver fails,
  the bound p^{v_p} ≤ C(m+1)^E for all m is equivalent to: no zero s_i is p-adically Liouville with respect to
  the integers, i.e. v_p(2m − s_i) ≤ E′·log_p m + C′. That holds if s_i is algebraic (Kunrui Yu's p-adic
  Baker theory). **[Open]** Algebraicity of the zeros of the Kubota–Leopoldt p-adic L-function is not
  known. Without it, even a single Vandiver counterexample could violate a polynomial bound along a
  sparse sequence of m.

## 4. Heuristic plausibility

**[Heur]** Model "Vandiver fails in a given even eigenspace" as an event of probability about 1/p, and
"edge irregular" also as probability 1/p. The expected number of pairs (p, m) with p | |K₄ₘ(ℤ)|
and p > m^D is then about Σ_p p^{1/D}·p^{−2}, which converges for every D > 1. So the polynomial bound is
heuristically true, with exponents expected to be 1. It also predicts that bounds proved by
"typical" methods will be exponential-type, as the archive's log-polynomial bound is.

## 5. Where a proof could come from

Only three known techniques see even eigenspaces:

1. **Topology of GL_N(ℤ)** (Voronoi complexes): this proves K₄ = K₈ = 0, but its cost grows
   super-exponentially in m.
2. **Soulé's homology torsion bounds** via perfect forms: these give superpolynomial bounds.
3. **Lower bounds for the Borel regulator** (Section 1): no general results are known.

Concrete research problems, each of which would close the corresponding input:

* **R1 (closes the whole problem).** R_{2m+1} ≥ (2m)!/((2π)^{2m} poly(m)).
* **R2 (closes input 2).** For p > B(m+1)^D the ω^{−2m} eigenspace of Cl(ℚ(ζ_p))[p] vanishes.
  By Section 2 this cannot follow from Bernoulli data alone.
* **R3 (closes input 1 at a given p).** A p-adic Diophantine lower bound |2m − s_i|_p ≥ (m+1)^{−E′} for the
  Iwasawa zeros.

The Lean side is ready to receive any of these. `card_four_mul_le_of_small_prime_powers` takes (1)
and (2) as hypotheses, and `card_four_mul_le_of_polynomial_witness` (in `ArchiveSelmer.lean`) takes a
direct polynomial witness as produced by R1.

## 6. Archive survey (2026-11-21): is R1, R2 or R3 already in the RH archive?

**No.** I searched by name and by statement shape. Paths below are relative to
`.automath-cache/riemann-hypothesis/src/Development/AutomorphicArithmetic/AutomorphicVarieties/`
unless they start with another top-level folder.

| Looked for | What the archive has | Usable? |
|---|---|---|
| R1: Borel regulator / Beilinson elements | No Borel regulator, polylogarithm or Beilinson element. `BStar`/`BStarOdd` (`LiteratureResults/KTheoryStability/ReductionBoundsTorsion`) are Borel **rank** computations (statements over ℚ). The "regulator lower bound" in `ThetaCorrespondence/.../RegulatorLowerBound.lean` is an Arakelov-height statement, conditional on `PublishedHodgeBundleTheorems`. There are also Dirichlet unit-regulator bounds (h·R ≤ …) | No |
| R2: Vandiver / even eigenspaces | No Vandiver, reflection or Herbrand–Ribet ("Herbrand" means the Herbrand quotient). The Stickelberger results (`OddResidueBounds`, `GaloisLibrary/StickelbergerTheorem`) annihilate the **minus** part. `plusLen_le_of_cl` (`GaloisLibrary/KummerTheory/MinusLenLeOfCl.lean`) only *reduces* plus-side lengths to class-group eigenspace bounds in the cyclotomic tower | No |
| R3: p-adic Baker / transcendence | Nothing on p-adic linear forms in logarithms; the transcendence results concern complex periods | No |
| Any log-type Selmer bound (Σ log ℓ · len ≤ C log e) | Every bound found has the shape C·e^A: `Bound`, `CorGK`, `CorG` (explicit: disc⁵·N¹⁸·e⁷·(log p + log p′), but only ever used as a hypothesis, never proved), `VVplusLe` ((N t)^C + C·exp), and the per-prime `ColumnFamilyFiltrationProperties` (e⁷·log log ℓ) | Only log-polynomial |
| Discharging `KTheoryComparison` | The archive has plus-construction K-theory (`PublishedTheorems/KArith.lean`): `KFinGen`, `KBorelRank`, `KDwyerFriedlander`, `KLocalisation` and others are stated, but **only `KStability` is proved**. The rest are fields of `KPublished`/`HypothesesV` and are never instantiated | No |

Proved and possibly useful later: Ferrero–Washington (`UpperTheory.V.FW.ferreroWashington`, used in Section 3),
and homological stability for GL (`KStability`). Of the Selmer bounds, only `CorGK` (exponent A not explicit) is proved; the explicit e⁷ form `CorG` is not.

## 7. Comparison with the published literature (checked 2026-11-21)

Published bounds for K_n(ℤ) (all hold only *up to small torsion*, i.e. ignoring primes ≤ about n+2):

| Source | Bound for F = ℚ | Shape |
|---|---|---|
| Soulé, *A bound for the torsion in the K-theory of algebraic integers*, Doc. Math. Extra Vol. Kato (2003), Prop. 4 iv) | log log card K_n(ℤ)_tors ≤ 8 n⁴ log n for n ≥ 9 (explicit) | doubly exponential |
| Bayer-Fluckiger–Emery–Houriet (arXiv 1406.5953) | no improvement for ℚ ("[Soulé, Prop. 4 iv)] is still the best available general bound for K_n(ℤ)") | — |
| de la Torre Durán, arXiv 2611.06300 (v2, 19 Nov 2026), Thm 4.5 / Rem. 4.6 | log card K_m(ℤ)_tors ≤ e^{O(n² log n)}, n = 2m+1 (not explicit) | doubly exponential |

**Ours (archive-based):** `log_card_four_mul_le_of_archive` gives log |K₄ₘ(ℤ)| ≤ C(m+1)^A, i.e.
log log |K₄ₘ(ℤ)| ≤ A·log(m+1) + O(1), with **all** primes included. That is exponentially
stronger on the log log scale than anything published. `log_torsionOrder_le_of_archive` extends it to
all degrees, given `ClassicalOrderBounds` for the other degrees. This is new **only if** the archive's
`corGK` is correct; the archive is an unverified claimed RH proof. Further caveats: C and A are not
explicit (the explicit e⁷ form `CorG` is unproved), and the comparison inputs (`KTheoryComparison`:
Quillen–Lichtenbaum via Rost–Voevodsky, Poitou–Tate, Rognes–Weibel) are published theorems that are not
formalized here.
