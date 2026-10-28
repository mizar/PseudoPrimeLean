/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeNonOneBounds
public import PseudoPrime.Analysis.GammaNearSquareNumerics

/-! # Shared near-square Gamma comparison numerics -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At x=(2/5)L² and L ≥ 1000, the left, principal, ramp and pole costs
are at most 7/100, 1/4, 21/2 and 15/8. The actual ramp main term exceeds
(M+1/20)L. Use the logarithmic tangent, sqrt x ≥ 63L/100 and the certified
ramp mass. These inequalities hold on the full real half-line. -/
theorem nearSquare_gamma_error_budgets {L : ℝ} (hL : 1000 ≤ L) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    43 * x ^ (-9 / 16 : ℝ) ≤ 7 / 100 ∧
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤ 1 / 4 ∧
      ((135 / 20 : ℝ) * Real.sqrt x +
            86 * ((1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20)) /
          Real.sqrt x ≤
        21 / 2 ∧
      ((7 / 6 : ℝ) * L + 4) / Real.sqrt x ≤ 15 / 8 ∧
      ((11783423 / 25000000 : ℝ) + 1 / 20) * L <
        (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * Real.sqrt x := by
  dsimp only
  let x := (2 / 5 : ℝ) * L ^ 2
  have hL0 : 0 < L := by linarith only [hL]
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 1000)]
  have hx0 := zero_lt_one.trans_le hx
  have hs := Real.sqrt_pos.mpr hx0
  have hroot : (63 / 100 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx0.le).mpr
    dsimp only [x]
    nlinarith only [sq_nonneg L]
  have hc :=
    Real.log_le_log (mul_pos hx0 (by norm_num only : (0 : ℝ) < 99 / 40))
      (show x * (99 / 40 : ℝ) ≤ L ^ 2 by
        dsimp only [x]
        nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hc
  norm_num only [Nat.cast_ofNat] at hc
  have hl := Analysis.nearSquare_gamma_log_bound hL
  have hlogX : Real.log (x * (99 / 40 : ℝ)) ≤ (7 / 500 : ℝ) * L := by linarith only [hc, hl]
  have hlogx : Real.log x ≤ (7 / 500 : ℝ) * L :=
    (Real.log_le_log hx0 (by nlinarith only [hx] : x ≤ x * (99 / 40 : ℝ))).trans hlogX
  have hd :=
    rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 1) (by norm_num only)
      (by
        norm_num only; exact hx)
  simp only [one_mul] at hd
  have hleft := mul_le_mul_of_nonneg_left hd (by norm_num only : (0 : ℝ) ≤ 43)
  have hfrac : 43 * (1 / Real.sqrt x) ≤ (7 / 100 : ℝ) := by
    rw [mul_one_div, div_le_iff₀ hs]
    linarith only [hroot, hL]
  refine ⟨hleft.trans hfrac, ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hs]
    linarith only [hlogx, hroot, hL]
  · rw [div_le_iff₀ hs]
    linarith only [hlogX, hroot, hL]
  · rw [div_le_iff₀ hs]
    linarith only [hroot, hL]
  · have hm := mul_le_mul_of_nonneg_right Analysis.gamma_ramp_mass_lower (Real.sqrt_nonneg x)
    nlinarith only [hm, hroot, hL]

end PseudoPrime.LLS.PaperStatements
