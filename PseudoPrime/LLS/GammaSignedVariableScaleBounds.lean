/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaRefinedVariableScaleBounds
public import PseudoPrime.LLS.GammaSharpLeftMomentBounds
public import PseudoPrime.LLS.GammaArchimedeanSign

/-! # One-sided variable-scale Gamma remainder

Retain the nonpositive archimedean real contribution in the completed explicit formula.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal conductor data under GRH and scale at least two,
the real Gamma remainder is bounded by the pole cost and the sharp left cost.
The exact completed formula and the nonpositive archimedean integral remove
the positive 64/9 allowance from this one-sided bound. The complex norm
estimate remains a separate API. -/
theorem re_gamma_primitive_remainder_le_variable_scale_sharp {q m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 2 ≤ x) :
    ((∑' n : ℕ, gammaMellinKernel.summand χ x n) +
          (∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ)).re ≤
      ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Real.log m + 28) + 1) := by
  let S := ∑' n : ℕ, gammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ
  let P :=
    MellinKernel.weightedResidue gammaMellinKernel (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x
      (-1 / 2)
  let J :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))
  have hx1 : 1 ≤ x := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hx
  have hr : (S - (P - Z + J)).re ≤ 0 := by
    have h :=
      MellinKernel.tsum_summand_eq_completed_residue_formula gammaMellinKernel
        (by linarith only [hm] : 2 ≤ m) hGRH hp hne hinv (a := -9 / 16) (b := 9 / 16)
        (by norm_num only)
        (by
          change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
        (by
          change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) (by norm_num only) hx1 (by norm_num only) (by norm_num only)
    dsimp only at h
    dsimp only [S, P, Z, J]
    rw [h, add_sub_cancel_left]
    exact
      gamma_right_integral_re_nonpos χ (by norm_num only)
        (by
          change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) hx
  have hP0 := gamma_poleResidue_le_ambient hq hm hmq hp hne hGRH (zero_lt_one.trans_le hx1)
  have hP : ‖P‖ ≤ ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x := hP0
  have hJ : ‖J‖ ≤ x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Real.log m + 28) + 1) :=
    norm_gamma_left_integral_le_sharp_moments hp hne hinv (zero_lt_one.trans_le hx1)
  have he : S + Z = (S - (P - Z + J)) + P + J := by ring
  change (S + Z).re ≤ _
  rw [he]
  simp only [Complex.add_re]
  linarith only [hr, hP, hJ, Complex.re_le_norm P, Complex.re_le_norm J]

end PseudoPrime.LLS.PaperStatements
