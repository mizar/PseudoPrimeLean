/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalComputed
public import PseudoPrime.Analysis.IntegerIntervalPhase

/-! # Computed rectangular complex interval products -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Compute an outward-rounded rectangle for a complex product at a common integer scale.
The two input pairs enclose real and imaginary coordinates. Four rounded real products and
exact interval addition produce the output used by finite complex-sum certificates. -/
def roundedComplexProduct (G : ℤ) (A B : IntegerInterval × IntegerInterval) :
    IntegerInterval × IntegerInterval :=
  let ac := roundedProduct G A.1 B.1
  let bd := roundedProduct G A.2 B.2
  let ad := roundedProduct G A.1 B.2
  let bc := roundedProduct G A.2 B.1
  (ac.add bd.neg, ad.add bc)

/-- At positive scale, computed rectangular multiplication encloses the product of any two
complex numbers in the input rectangles. The four computed real products satisfy the existing
integer checks, so their soundness gives this reusable finite-sum interface. -/
theorem roundedComplexProduct_contains {G : ℤ} {A B : IntegerInterval × IntegerInterval} {z w : ℂ}
    (hG : 0 < G) (hz : complexIntervalContains A.1 A.2 G z)
    (hw : complexIntervalContains B.1 B.2 G w) :
    complexIntervalContains (roundedComplexProduct G A B).1 (roundedComplexProduct G A B).2 G
      (z * w) := by
  exact
    complex_mul_contains hz hw (roundedProduct_check G A.1 B.1 hG)
      (roundedProduct_check G A.2 B.2 hG) (roundedProduct_check G A.1 B.2 hG)
      (roundedProduct_check G A.2 B.1 hG)

/-- Compute a rectangle for the ninth power using three squares followed by one multiplication.
The input rectangle and the positive common scale are shared by all four product steps. This
supplies the cutoff power in the initial power-of-two Euler–Maclaurin certificate. -/
def roundedComplexPow9 (G : ℤ) (Q : IntegerInterval × IntegerInterval) :
    IntegerInterval × IntegerInterval :=
  let Q2 := roundedComplexProduct G Q Q
  let Q4 := roundedComplexProduct G Q2 Q2
  let Q8 := roundedComplexProduct G Q4 Q4
  roundedComplexProduct G Q8 Q

/-- At positive scale, the computed ninth-power rectangle contains the ninth power of every
complex number in the input rectangle. Four applications of computed product containment prove
the result, with the exponent identity checked algebraically. -/
theorem roundedComplexPow9_contains {G : ℤ} {Q : IntegerInterval × IntegerInterval} {z : ℂ}
    (hG : 0 < G) (hq : complexIntervalContains Q.1 Q.2 G z) :
    complexIntervalContains (roundedComplexPow9 G Q).1 (roundedComplexPow9 G Q).2 G (z ^ 9) := by
  have h2 := roundedComplexProduct_contains hG hq hq
  have h4 := roundedComplexProduct_contains hG h2 h2
  have h8 := roundedComplexProduct_contains hG h4 h4
  have h9 := roundedComplexProduct_contains hG h8 hq
  have he : ((z * z) * (z * z)) * ((z * z) * (z * z)) * z = z ^ 9 := by ring
  rw [he] at h9
  exact h9

end PseudoPrime.Analysis
