/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaPairedNearSquareNumerics
public import PseudoPrime.LLS.GammaNearSquareNegativeBounds
public import PseudoPrime.LLS.PaperStatements.GammaNearSquareNegativeBounds

/-! # Negative witness comparison from log 700 using paired ramp jumps -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH at ambient level q at least 20000, scale x=(2/5)L squared,
L at least 700 and log q at most L+7/5, the primitive Gamma sum is at most
M log(conductor)+22. Keep the actual conductor and combine the certified
32-term zero-error prefix, pole cost and left cost.
This is the conductor-retaining upper input for the paired comparison. -/
theorem gammaCharSum_paired_conductor_GRH {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 700 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log χ.conductor + 22 := by
  let x := (2 / 5 : ℝ) * L ^ 2
  have hL0 : 0 < L := by linarith only [hL]
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 700)]
  have hx1 : 1 ≤ x := le_trans (by norm_num only) hx
  have hx0 := zero_lt_one.trans_le hx1
  have hs := Real.sqrt_pos.mpr hx0
  have hroot : (63 / 100 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx0.le).mpr
    dsimp only [x]
    nlinarith only [sq_nonneg L]
  have hd :=
    rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 1) (by norm_num only)
      (by
        norm_num only; exact hx1)
  simp only [one_mul] at hd
  have hleft : 43 * x ^ (-9 / 16 : ℝ) ≤ 1 / 10 := by
    have hm := mul_le_mul_of_nonneg_left hd (by norm_num only : (0 : ℝ) ≤ 43)
    have hh : 43 * (1 / Real.sqrt x) ≤ (1 / 10 : ℝ) := by
      rw [mul_one_div, div_le_iff₀ hs]
      linarith only [hroot, hL]
    exact hm.trans hh
  have hpole : ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x ≤ 2 := by
    rw [div_le_iff₀ hs]
    linarith only [hlogq, hroot, hL]
  have hu :=
    gammaCharacterSum_re_le_conductor_free_prefix hq χ hne hGRH hx 32
      Analysis.gammaResolvent_thirtyTwo_error_lt
  linarith only [hu, hleft, hpole]

end PseudoPrime.LLS.PaperStatements
