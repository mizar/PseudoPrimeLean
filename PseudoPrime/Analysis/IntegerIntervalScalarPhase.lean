/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalPhase

/-! # Checked scalar critical-line phase quotients -/

public section

namespace PseudoPrime.Analysis

/-- Checked ordinate, trigonometric coordinates, products and positive reciprocal
bounds enclose the real critical-line phase quotient. The denominator and
numerator are composed internally, so the certificate cannot omit either term.
This is the per-ordinate soundness step for the signed scalar cell checker. -/
theorem scalar_phase_contains {A C S AA AS Q D O : IntegerInterval} {G : ℤ} {g v : ℝ}
    (hg : A.Contains G g)
    (hp : complexIntervalContains C S G (Complex.exp (((g * v : ℝ) : ℂ) * Complex.I)))
    (hq : Q.Contains G (1 / 4 : ℝ))
    (haa : integerProductCheck G A.lower A.upper A.lower A.upper AA.lower AA.upper = true)
    (has : integerProductCheck G A.lower A.upper S.lower S.upper AS.lower AS.upper = true)
    (hd : integerReciprocalCheck G (Q.add AA).lower (Q.add AA).upper D.lower D.upper = true)
    (ho :
      integerProductCheck G (C.add (AS.scale 2)).lower (C.add (AS.scale 2)).upper D.lower D.upper
          O.lower O.upper =
        true) :
    O.Contains G ((Real.cos (g * v) + 2 * g * Real.sin (g * v)) / ((1 / 4 : ℝ) + g ^ 2)) := by
  have hs : S.Contains G (Real.sin (g * v)) := by
    simpa only [Complex.exp_ofReal_mul_I_im] using hp.2
  have hc : C.Contains G (Real.cos (g * v)) := by
    simpa only [Complex.exp_ofReal_mul_I_re] using hp.1
  have hden := IntegerInterval.add_contains hq (IntegerInterval.product_contains haa hg hg)
  have hi := integerReciprocalCheck_sound hd hden
  have hnum : (C.add (AS.scale 2)).Contains G (Real.cos (g * v) + 2 * g * Real.sin (g * v)) := by
    simpa only [Int.cast_ofNat, mul_assoc] using
      IntegerInterval.add_contains hc
        (IntegerInterval.scale_contains (k := 2) (IntegerInterval.product_contains has hg hs))
  simpa only [pow_two, div_eq_mul_inv] using IntegerInterval.product_contains ho hnum hi

end PseudoPrime.Analysis
