/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaCheckpoint50000

/-! # Asymmetric smoothed errors and a sharper Euler-prefix checkpoint -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: ordered positive cutoffs and one-sided smoothed-sum errors U and V.
Claim: the lower finite difference bounds psi(y) times log(y/x).
Proof: combine the two errors with positivity of the Mangoldt difference.
Role: retain asymmetric errors without replacing them by absolute-value bounds. -/
theorem psi_mul_log_lower_of_one_sided_errors {x y U V : ℝ} (hx : 0 < x) (hxy : x < y)
    (hU : AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x ≤ x + U)
    (hV : y - V ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum y) :
    y - x - U - V ≤ Chebyshev.psi y * Real.log (y / x) := by
  have h := (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum_difference_bounds hx hxy.le).2
  linarith only [hU, hV, h]

/-- Input: the same ordered cutoffs and one-sided errors.
Claim: the interval-length ratio replaces the logarithm in the lower comparison.
Proof: use log(y/x) <= (y-x)/x and nonnegativity of psi.
Role: expose a rational expression for quantitative checkpoint estimates. -/
theorem psi_mul_gap_lower_of_one_sided_errors {x y U V : ℝ} (hx : 0 < x) (hxy : x < y)
    (hU : AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x ≤ x + U)
    (hV : y - V ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum y) :
    y - x - U - V ≤ Chebyshev.psi y * (y - x) / x := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos (hx.trans hxy) hx)
  rw [div_sub_one hx.ne'] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog (Chebyshev.psi_nonneg y)
  rw [← mul_div_assoc] at hm
  exact (psi_mul_log_lower_of_one_sided_errors hx hxy hU hV).trans hm

/-- Input: positive ordered cutoffs, an upper error at x and a lower error at y.
Claim: psi(y) >= x-(U+V)x/(y-x), with no sign restrictions on U or V.
Proof: clear the positive interval length in the finite-difference comparison.
Role: avoid the unused sides of two absolute smoothed-error bounds. -/
theorem psi_lower_of_one_sided_errors {x y U V : ℝ} (hx : 0 < x) (hxy : x < y)
    (hU : AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x ≤ x + U)
    (hV : y - V ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum y) :
    x - (U + V) * x / (y - x) ≤ Chebyshev.psi y := by
  have hd := sub_pos.mpr hxy
  have h := psi_mul_gap_lower_of_one_sided_errors hx hxy hU hV
  have hc := (le_div_iff₀ hx).mp h
  apply (mul_le_mul_iff_left₀ hd).mp
  calc
    (x - (U + V) * x / (y - x)) * (y - x) = (y - x - U - V) * x := by
      simp only [sub_mul, div_mul_cancel₀ _ hd.ne']
      ring
    _ ≤ Chebyshev.psi y * (y - x) := hc

/-- Input: RH and 1 < x < y. Claim: the displayed asymmetric root/log error bounds psi(y).
Proof: use the sharp one-sided smoothed upper and lower formulas separately.
Role: keep the difference step free for later checkpoint optimization. -/
theorem psi_lower_of_asymmetric_rh_errors (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 < x)
    (hxy : x < y) :
    x -
        (Real.sqrt x / 20 + (Real.sqrt y / 20 + (1839 / 1000 : ℝ) * Real.log y + 21 / 20)) * x /
          (y - x) ≤
      Chebyshev.psi y := by
  apply
    psi_lower_of_one_sided_errors (zero_lt_one.trans hx) hxy
      (logWeightedMangoldtSum_le_add_sqrt_twentieth hRH hx)
  linarith only [logWeightedMangoldtSum_ge_rational_refined hRH (hx.trans hxy)]

/-- Input: RH. Claim: the smoothed Mangoldt sum at 50000 is at least 49967.
Proof: bound the square root by 224 and log(50000) by 16 log(2).
Role: retain the stronger lower error for the signed boundary product. -/
theorem smoothed50000_lower (hRH : RiemannHypothesis) :
    (49967 : ℝ) ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 50000 := by
  have h := logWeightedMangoldtSum_ge_rational_refined hRH (by norm_num only : (1 : ℝ) < 50000)
  have hs : Real.sqrt (50000 : ℝ) ≤ 224 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩
  have hl :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 50000) (by norm_num only : (50000 : ℝ) ≤ 2 ^ 16)
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [h, hs, hl, Real.log_two_lt_d9]

/-- Input: RH. Claim: psi(50000) is at least 47070.
Proof: use x=48500, upper error 56/5 and lower error 33 at y=50000.
Role: strengthen the negative Chebyshev boundary contribution analytically. -/
theorem psi50000_lower (hRH : RiemannHypothesis) : (47070 : ℝ) ≤ Chebyshev.psi 50000 := by
  have hs : Real.sqrt (48500 : ℝ) ≤ 224 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩
  have hu := logWeightedMangoldtSum_le_add_sqrt_twentieth hRH (by norm_num only : (1 : ℝ) < 48500)
  have hx :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 48500 ≤ 48500 + (56 / 5 : ℝ) := by
    linarith only [hu, hs]
  have h :=
    psi_lower_of_one_sided_errors (by norm_num only : (0 : ℝ) < 48500)
      (by norm_num only : (48500 : ℝ) < 50000) hx
      (show (50000 : ℝ) - 33 ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 50000 by
        norm_num only; exact smoothed50000_lower hRH)
  norm_num only at h
  linarith only [h]

/-- Input: RH. Claim: the Euler boundary tail at 50000 is at most 3293/500.
Proof: combine signed node bounds with the asymmetric arithmetic lower bounds.
Role: improve the prefix checkpoint without a new finite arithmetic payload. -/
theorem boundary50000_refined (hRH : RiemannHypothesis) :
    gammaEulerBoundaryTail 50000 ≤ (3293 / 500 : ℝ) := by
  have h :=
    gamma_euler_boundary_tail_upper (by norm_num only : (0 : ℝ) ≤ 6716 / 1000000000)
      gamma_center_cutoff_weight_lower (by norm_num only : (0 : ℝ) ≤ 47070) (psi50000_lower hRH)
      gamma_center_cutoff_slope_upper (by norm_num only) (by norm_num only : (0 : ℝ) ≤ 49967)
      (smoothed50000_lower hRH) gamma_center_cutoff_main_upper
  linarith only [h]

/-- Input: RH and b >= 50000. Claim: the full signed Euler prefix is at least 28493/5000.
Proof: transport the refined boundary checkpoint and use nonnegative prefix monotonicity.
Role: improve the old prefix constant by 7/500 at every later cutoff. -/
theorem gamma_prefix50000_lower_asymmetric (hRH : RiemannHypothesis) {b : ℝ} (hb : 50000 ≤ b) :
    (28493 / 5000 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have hp :=
    gamma_prefix_lower_of_checkpoint (U := 3293 / 500) hRH (le_refl (50000 : ℝ)) hb
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; exact boundary50000_refined hRH)
  norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] at hp
  linarith only [hp]

/-- Input: RH, b >= 50000 and an actual signed-dual cap D.
Claim: the refined checkpoint margin bounds the actual separation below.
Proof: apply the generic checkpoint transfer with the proved tail cap.
Role: remove the boundary-tail field from subsequent witness certificates. -/
theorem gamma_checkpoint50000_asymmetric_separation_le (hRH : RiemannHypothesis) {b L x D : ℝ}
    (hb : 50000 ≤ b) (hD : gammaScaleSignedDualBudget L x ≤ D) :
    gammaCheckpointSeparation L x D (3293 / 500) ≤ gammaFactorFreeSeparation L b x := by
  exact
    gamma_checkpoint_separation_le hRH (le_refl (50000 : ℝ)) hb
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; exact boundary50000_refined hRH)
      hD

/-- Input: arbitrary real L, x and D. Claim: the new scalar margin gains exactly 7/250.
Proof: the only changed term is twice the checkpoint tail cap.
Role: compare numerical certificates without claiming a new entrance theorem. -/
theorem gamma_checkpoint50000_asymmetric_margin_gain (L x D : ℝ) :
    gammaCheckpointSeparation L x D (3293 / 500) =
      gammaCheckpointSeparation L x D (33 / 5) + 7 / 250 := by
  unfold gammaCheckpointSeparation
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  ring

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: positive ordered cutoffs, an upper error at y and a lower error at x.
Claim: psi(x)<=y+(U+V)y/(y-x). Use the logarithmic finite difference and
nonnegativity of psi. Role: retain asymmetric errors for short Euler blocks. -/
theorem psi_upper_of_one_sided_errors {x y U V : ℝ} (hx : 0 < x) (hxy : x < y)
    (hU : AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum y ≤ y + U)
    (hV : x - V ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x) :
    Chebyshev.psi x ≤ y + (U + V) * y / (y - x) := by
  have hy := hx.trans hxy
  have hd := sub_pos.mpr hxy
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  rw [inv_div, one_sub_div hy.ne'] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog (Chebyshev.psi_nonneg x)
  have h := (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum_difference_bounds hx hxy.le).1
  have hu : Chebyshev.psi x * (y - x) / y ≤ y - x + U + V := by
    rw [mul_div_assoc]
    linarith only [hm, h, hU, hV]
  have hu' := (div_le_iff₀ hy).mp hu
  apply (mul_le_mul_iff_left₀ hd).mp
  calc
    Chebyshev.psi x * (y - x) ≤ (y - x + U + V) * y := hu'
    _ = (y + (U + V) * y / (y - x)) * (y - x) := by
      simp only [add_mul, div_mul_cancel₀ _ hd.ne']
      ring

/-- Input: RH and 1<x<y. Claim: the displayed asymmetric root/log error
bounds psi(x) above. Use only the lower formula at x and upper formula at y.
Role: complement the asymmetric lower estimate without absolute-value losses. -/
theorem psi_upper_of_asymmetric_rh_errors (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 < x)
    (hxy : x < y) :
    Chebyshev.psi x ≤
      y +
        (Real.sqrt y / 20 + (Real.sqrt x / 20 + (1839 / 1000 : ℝ) * Real.log x + 21 / 20)) * y /
          (y - x) := by
  apply
    psi_upper_of_one_sided_errors (zero_lt_one.trans hx) hxy
      (logWeightedMangoldtSum_le_add_sqrt_twentieth hRH (hx.trans hxy))
  linarith only [logWeightedMangoldtSum_ge_rational_refined hRH hx]

/-- Lower bound for the mass of a psi block from two asymmetric differences.
For 1<s<b and 1<a<t under RH, it bounds psi(b)-psi(a). The four real
endpoints remain independent. Role: expose a tunable analytic Euler-block budget. -/
noncomputable def psiAsymmetricBlockLower (a b s t : ℝ) : ℝ :=
  s -
    (Real.sqrt s / 20 + (Real.sqrt b / 20 + (1839 / 1000 : ℝ) * Real.log b + 21 / 20)) * s /
      (b - s) -
    (t +
      (Real.sqrt t / 20 + (Real.sqrt a / 20 + (1839 / 1000 : ℝ) * Real.log a + 21 / 20)) * t /
        (t - a))

/-- Input: RH, 1<s<b and 1<a<t. Claim: the explicit asymmetric block
bound is below psi(b)-psi(a). Subtract the one-sided estimates.
Role: quantify positive interval mass at arbitrary scales without enumerating primes. -/
theorem psi_sub_psi_ge_asymmetric_rh_bound (hRH : RiemannHypothesis) {a b s t : ℝ} (hs : 1 < s)
    (hsb : s < b) (ha : 1 < a) (hat : a < t) :
    psiAsymmetricBlockLower a b s t ≤ Chebyshev.psi b - Chebyshev.psi a := by
  have hl := psi_lower_of_asymmetric_rh_errors hRH hs hsb
  have hu := psi_upper_of_asymmetric_rh_errors hRH ha hat
  dsimp only [psiAsymmetricBlockLower]
  linarith only [hl, hu]

end PseudoPrime.LLS
