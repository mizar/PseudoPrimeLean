/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevScaleError
import PseudoPrime.Analysis.NumericalLogBounds

/-! # The numerical remainder in the Chebyshev bound -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Above 43, the logarithmic scale parameter `L/2 - log L` lies between
zero and `L/2`, and remains at most `L/2` after adding `log (2π)`. -/
theorem scale43_log_bounds {L : ℝ} (hL : 43 ≤ L) :
    0 ≤ L / 2 - Real.log L ∧
      L / 2 - Real.log L + Real.log (2 * Real.pi) ≤ L / 2 ∧ L / 2 - Real.log L ≤ L / 2 := by
  have hl : 0 < L := by linarith only [hL]
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith only [hL])
  have h2 : Real.log (2 : ℝ) < 1 := by linarith only [Real.log_two_lt_d9]
  have hloghalf := Real.log_le_sub_one_of_pos (show 0 < L / 2 by linarith only [hl])
  rw [Real.log_div hl.ne' (by norm_num only : (2 : ℝ) ≠ 0)] at hloghalf
  have hpi : (2 * Real.pi : ℝ) ≤ L := by linarith only [Real.pi_lt_four, hL]
  have hlogpi := Real.log_le_log (show 0 < 2 * Real.pi by positivity) hpi
  constructor
  · linarith only [hloghalf, h2]
  constructor
  · linarith only [hlogpi]
  · linarith only [hlog]

/-- Above 43, the exponential at half the logarithmic scale dominates four
times the cubic. Split at 20 and use the cubic exponential series term. -/
theorem exp_half_cubic {L : ℝ} (hL : 43 ≤ L) : 4 * L ^ 3 ≤ Real.exp (L / 2) := by
  have he20 : (1048576 : ℝ) ≤ Real.exp 20 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num only) Real.exp_one_gt_two.le 20
    rw [← Real.exp_nat_mul] at h
    norm_num only at h ⊢
    exact h
  have hu : 0 ≤ L / 2 - 20 := by linarith only [hL]
  have hp := Real.pow_div_factorial_le_exp (L / 2 - 20) hu 3
  norm_num only [Nat.factorial, Nat.cast_ofNat] at hp
  have heq : Real.exp (L / 2) = Real.exp 20 * Real.exp (L / 2 - 20) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hn : 0 ≤ (L / 2 - 20) ^ 3 / 6 := div_nonneg (pow_nonneg hu 3) (by norm_num only)
  have hm := mul_le_mul he20 hp hn (Real.exp_pos 20).le
  rw [heq]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hrel : L / 32 ≤ L / 2 - 20 := by linarith only [hL]
  have hpow := pow_le_pow_left₀ (show 0 ≤ L / 32 by positivity) hrel 3
  nlinarith only [hm, hpow, pow_nonneg hL0 3]

/-- For nonnegative `a ≤ L/2` and `z ≤ L/2`, bound the polynomial numerator
of the scale remainder by `L³/48 + 3`. The proof uses only `π > 3`. -/
theorem scale43_remainder_numerator {L a z : ℝ} (hL : 43 ≤ L) (ha : 0 ≤ a) (hau : a ≤ L / 2)
    (hzu : z ≤ L / 2) :
    L * a ^ 2 * Real.pi⁻¹ ^ 2 / 4 + L * Real.pi⁻¹ / 2 + L * z * Real.pi⁻¹ ^ 2 + 3 ≤
      L ^ 3 / 48 + 3 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hi0 : 0 ≤ Real.pi⁻¹ := inv_nonneg.mpr Real.pi_pos.le
  have hi : Real.pi⁻¹ ≤ (1 / 3 : ℝ) := by
    have h := (inv_le_inv₀ Real.pi_pos (by norm_num only : (0 : ℝ) < 3)).2 Real.pi_gt_three.le
    simpa only [one_div] using h
  have hi2 : Real.pi⁻¹ ^ 2 ≤ (1 / 9 : ℝ) := by nlinarith only [hi, hi0]
  have ha2 : a ^ 2 ≤ L ^ 2 / 4 := by nlinarith only [ha, hau, hL]
  have hmul := mul_le_mul ha2 hi2 (sq_nonneg _) (by positivity : 0 ≤ L ^ 2 / 4)
  have hmL := mul_le_mul_of_nonneg_left hmul hL0
  have hzmul := mul_le_mul_of_nonneg_right hzu (sq_nonneg Real.pi⁻¹)
  have hzL := mul_le_mul_of_nonneg_left hzmul hL0
  have hp2 := mul_le_mul_of_nonneg_left hi2 (show 0 ≤ L ^ 2 / 2 by positivity)
  have hp1 := mul_le_mul_of_nonneg_left hi hL0
  have hl2 : L / 6 ≤ L ^ 3 / 144 := by
    have hh := mul_nonneg hL0 (show 0 ≤ L ^ 2 - 24 by nlinarith only [hL])
    nlinarith only [hh]
  have hl3 : L ^ 2 / 18 ≤ L ^ 3 / 144 := by
    have hh := mul_nonneg (sq_nonneg L) (show 0 ≤ L - 8 by linarith only [hL])
    nlinarith only [hh]
  nlinarith only [hmL, hzL, hp2, hp1, hl2, hl3]

/-- For `L ≥ 43`, the explicit remainder in the normalized Chebyshev bound
is at most `1/100`. Bound its numerator by a cubic and compare that cubic
with the exponential lower bound. -/
theorem scale43_remainder_le {L : ℝ} (hL : 43 ≤ L) :
    let a := L / 2 - Real.log L
    let c := Real.log (2 * Real.pi)
    let δ := L / (Real.pi * Real.exp (L / 2))
    δ * a ^ 2 / (4 * Real.pi) + δ / 2 + δ * (a + c) / Real.pi + 3 / Real.exp (L / 2) ≤ 1 / 100 := by
  dsimp only
  have hlog := scale43_log_bounds hL
  have hn := scale43_remainder_numerator hL hlog.1 hlog.2.2 hlog.2.1
  have he := Real.exp_pos (L / 2)
  have heq :
    (L / (Real.pi * Real.exp (L / 2))) * (L / 2 - Real.log L) ^ 2 / (4 * Real.pi) +
        (L / (Real.pi * Real.exp (L / 2))) / 2 +
        (L / (Real.pi * Real.exp (L / 2))) * (L / 2 - Real.log L + Real.log (2 * Real.pi)) /
          Real.pi +
        3 / Real.exp (L / 2) =
      (L * (L / 2 - Real.log L) ^ 2 * Real.pi⁻¹ ^ 2 / 4 + L * Real.pi⁻¹ / 2 +
          L * (L / 2 - Real.log L + Real.log (2 * Real.pi)) * Real.pi⁻¹ ^ 2 +
          3) /
        Real.exp (L / 2) := by
    have he0 : Real.exp (L / 2) ≠ 0 := he.ne'
    field_simp
  rw [heq]
  have hdiv := div_le_div_of_nonneg_right hn he.le
  apply hdiv.trans
  apply (div_le_iff₀ he).2
  have hc := exp_half_cubic hL
  have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ 43 by norm_num only) hL 3
  norm_num only at hpow
  nlinarith only [hc, hpow]

/-- Under RH and the stated Rosser-type positive zero-count estimate, the
normalized Chebyshev error for `L ≥ 43` is bounded by the explicit main
term plus `101/100`. The count estimate remains an assumption. -/
theorem psi_error_main_43 (hRH : RiemannHypothesis) {L : ℝ} (hL : 43 ≤ L)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤
      ((L / 2 - Real.log L) ^ 2 + 2 * (L / 2 - Real.log L) + 2 * Real.log (2 * Real.pi) + L) /
          (2 * Real.pi) +
        101 / 100 := by
  have hm := psi_error_main_remainder hRH hL hQ
  have hr := scale43_remainder_le hL
  dsimp only at hm hr
  linarith only [hm, hr]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
