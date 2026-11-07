/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleKernel

/-! # Sixth-pole kernel for the refined Miller--Rabin bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The admissible sixth-pole kernel with the parameters `a=25/54` and
`c=21/16`. Its normalization is the existing rational-pole family's, so the
paper's function is multiplied by `(27/25)^5`. This kernel supplies the
explicit sixth-pole high-range argument. -/
noncomputable def refinedSixPoleKernel : LLS.PaperStatements.MellinKernel :=
  LLS.PaperStatements.rationalPoleMellinKernel 3 (25 / 54) (21 / 16) (by norm_num only)
    (by norm_num only) (by norm_num only)

/-- The actual admissible function equals the paper's sixth-pole function
with the exact normalization factor `(27/25)^5`. Rewrite the general
shifted-power identity and evaluate the rational parameters. -/
theorem refined_six_pole_function (z : ℂ) :
    refinedSixPoleKernel.function z =
      ((27 / 25 : ℂ) ^ 5) * (Complex.exp ((21 / 8 : ℂ) * z) / (z + 27 / 25) ^ 6) := by
  change Analysis.rationalPoleFunction 3 (25 / 54) (21 / 16) z = _
  rw [Analysis.rationalPole_eq_shifted_power 3 (by norm_num only) (21 / 16) z]
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Nat.reduceMul]

/-- On every positive input and every line to the right of the sixth pole,
the inverse Mellin transform is the explicit nonnegative rational-pole
profile. This specializes the existing inversion theorem to the refined
parameters without changing its normalization. -/
theorem refined_six_pole_inversion {σ u : ℝ} (hσ : 0 < σ + 27 / 25) (hu : 0 < u) :
    Analysis.inverseMellin (refinedSixPoleKernel.function) σ u =
      (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) u : ℂ) := by
  change Analysis.inverseMellin (Analysis.rationalPoleFunction 3 (25 / 54) (21 / 16)) σ u = _
  apply Analysis.inverseMellin_rationalPole (m := 3) (by norm_num only) (by norm_num only) _ hu
  norm_num only at hσ ⊢
  exact hσ

/-- The refined sixth-pole profile is nonnegative at every real argument.
This specializes the sign property of the admissible rational-pole family. -/
theorem refined_six_pole_profile_nonneg (u : ℝ) :
    0 ≤ Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) u := by
  exact Analysis.rationalPoleProfile_nonneg 3 (by norm_num only) (21 / 16) u

/-- The refined sixth-pole profile vanishes beyond `exp(21/8)`. The
logarithmic support cutoff is exactly the one used by the paper's kernel. -/
theorem refined_six_pole_profile_zero {u : ℝ} (hu : Real.exp (21 / 8) < u) :
    Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) u = 0 := by
  have hl := Real.log_lt_log (Real.exp_pos (21 / 8 : ℝ)) hu
  rw [Real.log_exp] at hl
  unfold Analysis.rationalPoleProfile
  rw [ite_eq_right]
  intro h
  norm_num only at h
  linarith only [hl, h.2]

end PseudoPrime.PrimeTestBounds.MillerRabin
