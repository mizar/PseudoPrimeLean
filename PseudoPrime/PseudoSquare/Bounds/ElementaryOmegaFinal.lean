/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PseudoSquare.Bounds.ElementaryOmegaEnvelope
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaFiniteCertificates
import PseudoPrime.LLS.Theorem11S1GRH

/-!
# The Robin-free boxed bound under GRH

This is the public assembly point for the final bound.  The elementary envelope and finite
certificates are unconditional; the large-`n` branch uses the general LLS S1 theorem,
which is discharged from GRH by `llsTheorem11S1Character_of_grh`.  No Robin estimate is
used anywhere in this route.

The file also exports real-cutoff and fully expanded variants so users need not depend on the
internal `Arithmetic.greatestOddPrimeLE` or `elementaryRadius` wrappers.
-/

namespace PseudoPrime.PseudoSquare

/--
**The Robin-free boxed bound for every `B ≥ 3`, under GRH.**
No Robin machinery of any kind is used anywhere in this route.

The conclusion's right-hand side, `Arithmetic.greatestOddPrimeLE (elementaryRadius B)`, unfolds to:
the
greatest odd prime not exceeding

```
elementaryRadius B = (Real.log (4 * B) + (24 / 5) * Real.log (Real.log (4 * B)) + 3) ^ 2,
```

i.e. the boxed cutoff `(log(4B) + (24/5)·loglog(4B) + 3)²`. This bare form is used
rather than the `max`-wrapped `elementaryUpperBound B`: for `B ≥ 3`, `elementaryUpperBound_eq_of_le`
shows the `max 31 (...)` safety margin is redundant (`Arithmetic.greatestOddPrimeLE
(elementaryRadius B)`
is at least `31`, by `thirtyOne_le_greatestOddPrimeLE_elementaryRadius`).
Every admissible `n < 750` is covered by the unconditional finite
check `smallNegOneWitnessBound` (giving `≤ 31`, absorbed since `31` itself is below the bare
`Arithmetic.greatestOddPrimeLE (elementaryRadius B)`), and `750 ≤ n ≤ B` is handled by LLS via
`elementary_sq_le_radius`.
-/
theorem elementary_formula
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {B : ℕ}
    (hB : 3 ≤ B) :
    QNeOne B ≤ QNegOne B ∧
      QNegOne B ≤
        AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE (elementaryRadius B) := by
  apply And.intro (QNeOne_le_QNegOne B)
  rw [← elementaryUpperBound_eq_of_le hB]
  classical
  unfold QNegOne
  apply Finset.sup_induction (p := fun k : ℕ => k ≤ elementaryUpperBound B) (Nat.zero_le _)
  · intro a ha b hb
    exact max_le ha hb
  · intro n _
    have hadm := NumberTheory.mem_admissibleFinset_iff.mp n.property
    let hw :=
      NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hadm.odd
        hadm.not_isSquare
    by_cases hn750 : n.val < 750
    · exact
        (smallNegOneWitnessBound n.val hadm.odd hadm.not_isSquare hn750).trans
          (thirty_one_le_elementaryUpperBound B)
    · have hmem := NumberTheory.primeNegOneWitness_mem n.val hw
      have hLLS : LLS.llsTheorem11S1Character :=
        LLS.llsTheorem11S1Character_of_grh hGRH
      exact
        odd_prime_le_elementaryUpperBound hmem.1 hmem.2.1
          (primeNegOneWitness_cast_le_elementaryRadius hLLS
            AnalyticNumberTheory.Arithmetic.elementaryOmegaStatement hadm.odd
            hadm.not_isSquare hadm.le (Nat.le_of_not_gt hn750) hw)

/--
**The Robin-free boxed bound, real-cutoff form.**

Assuming GRH and `B ≥ 3`, this gives `QNeOne B ≤ QNegOne B` and
`(QNegOne B : ℝ) ≤ elementaryRadius B`.
The proof casts the natural-number bound from `elementary_formula` to the reals and applies
`PseudoPrime.AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE_cast_le` to the nonnegative
squared radius. The conclusion omits the odd-prime cutoff wrapper and supplies
`elementary_formula_explicit`.
-/
theorem elementary_formula_real
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {B : ℕ}
    (hB : 3 ≤ B) : QNeOne B ≤ QNegOne B ∧ (QNegOne B : ℝ) ≤ elementaryRadius B := by
  obtain ⟨hne, hneg⟩ := elementary_formula hGRH hB
  refine ⟨hne, ?_⟩
  have hR : (0 : ℝ) ≤ elementaryRadius B := by
    unfold elementaryRadius; positivity
  exact
    (Nat.cast_le.mpr hneg).trans
      (AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE_cast_le hR)

/--
**The Robin-free boxed bound, fully explicit form.**

Assuming GRH and `B ≥ 3`, this gives `QNeOne B ≤ QNegOne B` and
`(QNegOne B : ℝ) ≤ (log(4B) + (24/5)·loglog(4B) + 3)²`.
The proof unfolds `elementaryRadius` in `elementary_formula_real`.
This public form states the final bound without the radius or odd-prime cutoff wrappers.
-/
theorem elementary_formula_explicit
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {B : ℕ}
    (hB : 3 ≤ B) :
    QNeOne B ≤ QNegOne B ∧
      (QNegOne B : ℝ) ≤
        (Real.log (4 * (B : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (B : ℝ))) + 3) ^ 2 := by
  simpa only [elementaryRadius] using elementary_formula_real hGRH hB

end PseudoPrime.PseudoSquare
