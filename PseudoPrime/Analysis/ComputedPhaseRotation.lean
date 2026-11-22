/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalComputed
public import PseudoPrime.Analysis.IntegerIntervalPhaseTaylor
import Mathlib.Tactic.Ring

/-! # Computed angle doubling after a small Taylor certificate -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Compute outward rectangular bounds for a complex square at scale G.
The two squared coordinates and the mixed product use rounded multiplication,
so this operation needs no externally supplied product witnesses. -/
def roundedPhaseDouble (G : ℤ) (R I : IntegerInterval) : IntegerInterval × IntegerInterval :=
  let rr := roundedProduct G R R
  let ii := roundedProduct G I I
  let ri := roundedProduct G R I
  (rr.add ii.neg, ri.add ri)

/-- At positive scale, a certified phase rectangle yields a certified rectangle
for twice the angle. The rounded products discharge the squaring checks. -/
theorem rounded_phase_double_contains {G : ℤ} {R I : IntegerInterval} {x : ℝ} (hG : 0 < G)
    (hx : complexIntervalContains R I G (Complex.exp ((x : ℂ) * Complex.I))) :
    complexIntervalContains (roundedPhaseDouble G R I).1 (roundedPhaseDouble G R I).2 G
      (Complex.exp (((x + x : ℝ) : ℂ) * Complex.I)) := by
  exact
    phase_double_contains hx (roundedProduct_check G R R hG) (roundedProduct_check G I I hG)
      (roundedProduct_check G R I hG)

/-- A Taylor certificate at half of a rational angle and its analytic remainder
enclose the full phase after one computed square. This supports rotation angles
up to one half while retaining the quarter-angle Taylor certificate. -/
theorem rational_phase_double_contains {q : ℚ} {R I : IntegerInterval} {G r : ℤ} (hG : 0 < G)
    (hcheck : rationalPhaseTaylorCheck (q / 2) R I G = true)
    (hr : (1 / 2 ^ 120 : ℝ) ≤ (r : ℝ) / G) :
    complexIntervalContains (roundedPhaseDouble G (R.widen r) (I.widen r)).1
      (roundedPhaseDouble G (R.widen r) (I.widen r)).2 G (Complex.exp ((q : ℂ) * Complex.I)) := by
  have ht :
    complexIntervalContains (R.widen r) (I.widen r) G
      (Complex.exp (((((q / 2 : ℚ) : ℝ)) : ℂ) * Complex.I)) := by
    simpa only [Complex.ofReal_ratCast] using rational_phase_taylor_contains hcheck hr
  have hd := rounded_phase_double_contains hG ht
  have heq : ((q / 2 : ℚ) : ℝ) + ((q / 2 : ℚ) : ℝ) = (q : ℝ) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    ring
  simpa only [heq, Complex.ofReal_ratCast] using hd

end PseudoPrime.Analysis
