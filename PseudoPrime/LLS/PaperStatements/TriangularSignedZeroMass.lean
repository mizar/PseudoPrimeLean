/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularFiniteZeroMass
public import PseudoPrime.LLS.TriangularArchimedeanBounds
public import PseudoPrime.Analysis.TriangularSignedZeroMass

/-! # Signed arithmetic formula for triangular absolute zero mass

Keep the character and inverse-character arithmetic sums on the left.
Only the two gamma integrals remain in addition to the conductor.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For every complex function, the alpha-18 reflected integral equals the
right-line integral. Substitute t with -t and use the even triangular transform.
No integrability premise is needed for this change of variables.
This preserves the arithmetic sign in the zero-mass formula. -/
theorem triangular18_reflectedIntegral_eq_right (f : ℂ → ℂ) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          f (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
            K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          f ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          f (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
            K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          f ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t))
  congr 1
  let F := fun t : ℝ ↦
    f ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
      K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have h (t : ℝ) :
    f (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) =
      F (-t) := by
    have hz : (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) = -(((9 / 16 : ℝ) : ℂ) + Complex.I * (-t)) := by
      simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    have hw :
      (((17 / 16 : ℝ) : ℂ) - Complex.I * t) = (((9 / 16 : ℝ) : ℂ) + Complex.I * (-t)) + 1 / 2 := by
      push_cast
      ring
    dsimp only [F]
    rw [hz, hw]
    simp only [Complex.ofReal_neg]
    exact
      congrArg (fun z : ℂ ↦ f ((((9 / 16 : ℝ) : ℂ) + Complex.I * (-t)) + 1 / 2) * z)
        (Analysis.triangularMellinFunction_neg (a := 18) (by norm_num only) _)
  calc
    _ = ∫ t : ℝ, F (-t) := MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h)
    _ = ∫ t : ℝ, F t := MeasureTheory.integral_neg_eq_self F MeasureTheory.volume
    _ = _ := by rfl

end PseudoPrime.LLS.PaperStatements
