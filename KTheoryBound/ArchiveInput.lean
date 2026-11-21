import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.ClassNumberThree

/-!
# The single input taken from the RH archive (stated, not re-proved here)

`UpperTheory.V.SmallClassNumbers.bound : Bound` is proved in the archive
(`.../SmallClassNumbers/CorGKOf.lean`, as `bound_of corGK`). Importing that proof loads about
170,000 archive modules (86 GB of compiled files), so we restate it with `sorry` instead.

* The type is the archive's own `Bound`, imported from its definitions module
  `ClassNumberThree` (about 2,100 modules), not a retyped copy.
* `scripts/check-archive-signature.lean` reads only `CorGKOf.olean`, without its imports, and checks
  that the archive's theorem `UpperTheory.V.SmallClassNumbers.bound` has exactly this type,
  `UpperTheory.V.SmallClassNumbers.Bound`, with no universe parameters.

Every `sorryAx` in `#print axioms` output in this project comes from this declaration
and nowhere else.
-/

/-- The archive's theorem, restated. Proof: `UpperTheory.V.SmallClassNumbers.bound` in
`leanprover-community/riemann-hypothesis` at commit `23aebbb3`. -/
theorem KTheoryBound.archive_bound : UpperTheory.V.SmallClassNumbers.Bound := by
  sorry
