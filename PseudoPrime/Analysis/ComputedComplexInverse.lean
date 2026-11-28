/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ComputedComplexIntervals
public import PseudoPrime.Analysis.ComputedScalarPhase

/-! # Rectangular interval inverses and sixth powers -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Enclose the squared norm of a complex rectangle using its two real
squares. All operations use the original integer scale. -/
def complexNormSqInterval (G : ℤ) (Q : IntegerInterval × IntegerInterval) : IntegerInterval :=
  (roundedProduct G Q.1 Q.1).add (roundedProduct G Q.2 Q.2)

/-- Enclose a complex inverse by multiplying the conjugate rectangle by
the reciprocal of the squared norm. Its lower endpoint must be positive
for the enclosure to be valid. -/
def roundedComplexInv (G : ℤ) (Q : IntegerInterval × IntegerInterval) :
    IntegerInterval × IntegerInterval :=
  let D := reciprocalCandidate G (complexNormSqInterval G Q)
  (roundedProduct G Q.1 D, roundedProduct G Q.2.neg D)

/-- At positive scale a rectangle with positive squared norm lower endpoint
admits the computed inverse enclosure. -/
theorem roundedComplexInv_contains {G : ℤ} {Q : IntegerInterval × IntegerInterval} {z : ℂ}
    (hg : 0 < G) (hz : complexIntervalContains Q.1 Q.2 G z)
    (hd : 0 < (complexNormSqInterval G Q).lower) :
    complexIntervalContains (roundedComplexInv G Q).1 (roundedComplexInv G Q).2 G z⁻¹ := by
  have hn : (complexNormSqInterval G Q).Contains G (Complex.normSq z) := by
    rw [Complex.normSq_apply]
    exact
      IntegerInterval.add_contains (roundedProduct_contains hg hz.1 hz.1)
        (roundedProduct_contains hg hz.2 hz.2)
  have ho : (complexNormSqInterval G Q).lower ≤ (complexNormSqInterval G Q).upper := by
    exact_mod_cast ((div_le_div_iff_of_pos_right (Int.cast_pos.mpr hg)).mp (hn.1.trans hn.2))
  have hi := integerReciprocalCheck_sound (reciprocalCandidate_check hg hd ho) hn
  constructor
  · rw [Complex.inv_re, div_eq_mul_inv]
    exact roundedProduct_contains hg hz.1 hi
  · rw [Complex.inv_im, div_eq_mul_inv]
    exact roundedProduct_contains hg (IntegerInterval.neg_contains hz.2) hi

/-- Compute a sixth-power enclosure with three rounded products. Squaring
first avoids repeating the same multiplication. -/
def roundedComplexPow6 (G : ℤ) (Q : IntegerInterval × IntegerInterval) :
    IntegerInterval × IntegerInterval :=
  let Q2 := roundedComplexProduct G Q Q
  let Q4 := roundedComplexProduct G Q2 Q2
  roundedComplexProduct G Q4 Q2

/-- The computed sixth-power rectangle encloses the sixth power of every
point in the input rectangle at a positive scale. -/
theorem roundedComplexPow6_contains {G : ℤ} {Q : IntegerInterval × IntegerInterval} {z : ℂ}
    (hg : 0 < G) (hz : complexIntervalContains Q.1 Q.2 G z) :
    complexIntervalContains (roundedComplexPow6 G Q).1 (roundedComplexPow6 G Q).2 G (z ^ 6) := by
  have h2 := roundedComplexProduct_contains hg hz hz
  have h4 := roundedComplexProduct_contains hg h2 h2
  have h := roundedComplexProduct_contains hg h4 h2
  have he : ((z * z) * (z * z)) * (z * z) = z ^ 6 := by ring
  rw [he] at h
  exact h

end PseudoPrime.Analysis
