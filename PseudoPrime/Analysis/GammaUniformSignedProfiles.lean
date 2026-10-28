/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSignedShiftBounds
public import PseudoPrime.LLS.GammaUniformScaleExcessBounds

/-! # Concrete signed logarithmic corrections for coefficient four fifths

A positive constant correction lowers the logarithmic entrance to 34971.
A negative log-log correction gives a smaller pointwise cutoff from 50880.
Both proofs bound the actual nonunit loss on the entire stated half-line.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L > 0, log L ≤ L/10000+9. Apply log u ≤ u-1 at u=L/10000
and bound log 10000 by 10 using the certified logarithms of two and five.
This affine majorant controls the signed logarithmic correction on a half-line. -/
theorem log_le_linear_tenThousand {L : ℝ} (hL : 0 < L) : Real.log L ≤ L / 10000 + 9 := by
  have h10000 : Real.log (10000 : ℝ) < 10 := by
    rw [show (10000 : ℝ) = 10 ^ 4 by norm_num only, Real.log_pow,
      show (10 : ℝ) = 2 * 5 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (5 : ℝ) ≠ 0)]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have h := Real.log_le_sub_one_of_pos (div_pos hL (by norm_num only : (0 : ℝ) < 10000))
  rw [Real.log_div hL.ne' (by norm_num only : (10000 : ℝ) ≠ 0)] at h
  linarith only [h, h10000]

/-- For L ≥ 10000, log L ≤ L/1000. Apply the affine logarithm bound
and absorb its constant at the endpoint. This bounds the scale reduction relatively. -/
theorem log_le_one_thousandth {L : ℝ} (hL : 10000 ≤ L) : Real.log L ≤ L / 1000 := by
  have h := log_le_linear_tenThousand (show 0 < L by linarith only [hL])
  linarith only [h, hL]

/-- For L ≥ 32768, log L/L^(1/3) ≤ 1/3. Anchor the cube root at 32,
use log 32 < 32/9, and apply log u ≤ u-1 to the ratio of the cube roots.
This supplies a local budget below the old uniform logarithmic entrance. -/
theorem log_div_cuberoot_le_one_third_of_ge_32768 {L : ℝ} (hL : 32768 ≤ L) :
    Real.log L / L ^ (1 / 3 : ℝ) ≤ 1 / 3 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc :=
    Real.rpow_le_rpow (by norm_num only : (0 : ℝ) ≤ 32 ^ 3)
      (show (32 : ℝ) ^ 3 ≤ L by linarith only [hL]) (by norm_num only : (0 : ℝ) ≤ 1 / 3)
  have he : ((32 : ℝ) ^ 3) ^ (1 / 3 : ℝ) = 32 := by
    rw [← Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 32)]
    norm_num only [Real.rpow_one]
  rw [he] at hc
  have hu0 := Real.rpow_pos_of_pos hL0 (1 / 3 : ℝ)
  have ht := Real.log_le_sub_one_of_pos (div_pos hu0 (by norm_num only : (0 : ℝ) < 32))
  rw [Real.log_div hu0.ne' (by norm_num only : (32 : ℝ) ≠ 0), Real.log_rpow hL0] at ht
  have h32 : Real.log (32 : ℝ) < 32 / 9 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  rw [div_le_iff₀ hu0]
  linarith only [hc, ht, h32]

/-- For log q ≥ 34971, twice the normalized nonunit loss at T=log q+29
is at most 2750/213. Bound the cutoff by (log q)² and the root by (71/125)log q,
then apply the independent-scale split-prime budget.
This is the local allowance for the smaller-start profile. -/
theorem gamma_commonFactor_budget_log_plus_twentyNine {q : ℕ} [NeZero q] (hL : 34971 ≤ Real.log q) :
    let T := Real.log q + 29;
    let x := (32 / 99 : ℝ) * T ^ 2;
    2 *
        (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((4 / 5 : ℝ) * T ^ 2) q /
          Real.sqrt x) ≤
      2750 / 213 := by
  let L := Real.log q
  let T := L + 29
  let x := (32 / 99 : ℝ) * T ^ 2
  have hT0 : 0 < T := by
    dsimp only [T, L]; linarith only [hL]
  have hx0 : 0 < x := mul_pos (by norm_num only) (sq_pos_of_pos hT0)
  have hcut : 1 ≤ (4 / 5 : ℝ) * T ^ 2 := by
    dsimp only [T, L]
    nlinarith only [hL, sq_nonneg (Real.log q - 34971)]
  have hc : (4 / 5 : ℝ) * T ^ 2 ≤ L ^ 2 := by
    dsimp only [T, L]
    nlinarith only [hL, sq_nonneg (Real.log q - 34971)]
  have hlog := Real.log_le_log (zero_lt_one.trans_le hcut) hc
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hs := uniform_ramp_scale_sqrt_lower_71_div_125 hT0.le
  have hroot : (71 / 125 : ℝ) * L ≤ Real.sqrt x := by
    change (71 / 125 : ℝ) * (L + 29) ≤ Real.sqrt x at hs
    linarith only [hs]
  have h :=
    gamma_commonFactor_budget_of_scale_ratio_sqrt (by norm_num only : (0 : ℝ) < 71 / 125)
      (show 1 < Real.log q by linarith only [hL]) hx0 hcut hlog hroot
      (log_div_cuberoot_le_one_third_of_ge_32768 (show 32768 ≤ Real.log q by linarith only [hL]))
  norm_num only at h
  exact h

/-- For log q ≥ 44739, T=log q-log log q meets the common scale entrance,
has normalized nonunit loss at most 170560/13419, and scale excess at most 1/100.
Bound log log q relatively, compare the cutoff and root, and control the negative-power error.
These bounds hold on the whole half-line and support a negative log-log correction. -/
theorem gamma_log_minus_loglog_scale_bounds {q : ℕ} [NeZero q] (hL : 44739 ≤ Real.log q) :
    let L := Real.log q;
    let T := L - Real.log L;
    35000 ≤ T ∧
      2 *
          (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum ((32 / 99 : ℝ) * T ^ 2)
              ((4 / 5 : ℝ) * T ^ 2) q /
            Real.sqrt ((32 / 99 : ℝ) * T ^ 2)) ≤
        170560 / 13419 ∧
      LLS.PaperStatements.gammaScaleExcess L T ≤ 1 / 100 := by
  let L := Real.log q
  let T := L - Real.log L
  let x := (32 / 99 : ℝ) * T ^ 2
  have hL0 : 0 < L := by
    dsimp only [L]; linarith only [hL]
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (show 1 ≤ L by linarith only [hL])
  have hlog := log_le_one_thousandth (show 10000 ≤ L by linarith only [hL])
  have hT : 35000 ≤ T := by
    dsimp only [T]; linarith only [hL, hlog]
  have hT0 : 0 < T := by linarith only [hT]
  have hxlarge := common_nonOne_ramp_scale_large hT
  have hx : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ (17 / 5) ^ 16).trans hxlarge
  have hs0 := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  have hcut : 1 ≤ (4 / 5 : ℝ) * T ^ 2 := by nlinarith only [hT, sq_nonneg (T - 35000)]
  have hc : (4 / 5 : ℝ) * T ^ 2 ≤ L ^ 2 := by
    have he : T ≤ L := by
      dsimp only [T]; linarith only [hlog0]
    have ht := (sq_le_sq₀ hT0.le hL0.le).mpr he
    nlinarith only [ht, sq_nonneg T]
  have hcutlog := Real.log_le_log (zero_lt_one.trans_le hcut) hc
  rw [Real.log_pow] at hcutlog
  norm_num only [Nat.cast_ofNat] at hcutlog
  have hs := uniform_ramp_scale_sqrt_lower_71_div_125 hT0.le
  have hroot : (567 / 1000 : ℝ) * L ≤ Real.sqrt x := by
    change (71 / 125 : ℝ) * (L - Real.log L) ≤ Real.sqrt x at hs
    linarith only [hs, hlog, hL0]
  have hlocal :=
    gamma_commonFactor_budget_of_scale_ratio_sqrt (by norm_num only : (0 : ℝ) < 567 / 1000)
      (show 1 < Real.log q by linarith only [hL]) (zero_lt_one.trans_le hx) hcut hcutlog hroot
      (log_div_cuberoot_le_of_ge_44739 hL)
  norm_num only at hlocal
  refine ⟨hT, hlocal, ?_⟩
  let D := max 0 (L - T - 2)
  have hD0 : 0 ≤ D := le_max_left _ _
  have hD : D ≤ L / 1000 := by
    apply max_le (div_nonneg hL0.le (by norm_num only))
    dsimp only [T]
    linarith only [hlog]
  have hrpow : x ^ (-9 / 16 : ℝ) ≤ 1 / Real.sqrt x := by
    have h := Real.rpow_le_rpow_of_exponent_le hx (by norm_num only : (-9 / 16 : ℝ) ≤ -(1 / 2 : ℝ))
    rw [Real.rpow_neg (zero_lt_one.trans_le hx).le, ← Real.sqrt_eq_rpow, ← one_div] at h
    exact h
  have hcoef :
    (7 / 6 : ℝ) / Real.sqrt x + (16 / 5 : ℝ) * x ^ (-9 / 16 : ℝ) ≤
      (131 / 30 : ℝ) / Real.sqrt x := by
    have h := mul_le_mul_of_nonneg_left hrpow (by norm_num only : (0 : ℝ) ≤ 16 / 5)
    calc
      _ ≤ (7 / 6 : ℝ) / Real.sqrt x + (16 / 5 : ℝ) * (1 / Real.sqrt x) := add_le_add_right h _
      _ = _ := by ring
  have hexcess := mul_le_mul_of_nonneg_right hcoef hD0
  have hupper : ((131 / 30 : ℝ) / Real.sqrt x) * D ≤ 1 / 100 := by
    rw [show ((131 / 30 : ℝ) / Real.sqrt x) * D = ((131 / 30 : ℝ) * D) / Real.sqrt x by ring]
    apply (div_le_iff₀ hs0).mpr
    have h := mul_le_mul_of_nonneg_left hD (by norm_num only : (0 : ℝ) ≤ 131 / 30)
    nlinarith only [h, hroot, hL0]
  change ((7 / 6 : ℝ) / Real.sqrt x + (16 / 5 : ℝ) * x ^ (-9 / 16 : ℝ)) * D ≤ 1 / 100
  exact hexcess.trans hupper

end PseudoPrime.Analysis
