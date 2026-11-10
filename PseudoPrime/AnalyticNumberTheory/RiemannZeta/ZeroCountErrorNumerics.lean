/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.NumericalLogBounds

/-! # Simplifying the explicit zero-count error

A numerical comparison for the Rosser-type error above the Lee–Nosal cutoff.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `t ≥ 2πe`, the explicit Rosser-type error expression is at most
`log t`. Bound `log (log t)` by half of `log t`, and use `t ≥ 16` to
control the reciprocal term. This comparison does not prove the zero count. -/
theorem rosser_error_le_log {t : ℝ} (ht : 2 * Real.pi * Real.exp 1 ≤ t) :
    (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
        1 / (5 * t) ≤
      Real.log t := by
  have he : (8 / 3 : ℝ) < Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    norm_num only at h ⊢
    linarith only [h]
  have hp :=
    mul_le_mul Real.pi_gt_three.le he.le (by norm_num only : (0 : ℝ) ≤ 8 / 3)
      (show (0 : ℝ) ≤ Real.pi by exact Real.pi_pos.le)
  have ht16 : (16 : ℝ) ≤ t := by nlinarith only [ht, hp]
  have hl16 : (5 / 2 : ℝ) ≤ Real.log (16 : ℝ) := by
    have h := Real.log_two_gt_d9
    have heq : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      have h16 : (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num only
      rw [h16, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
    rw [heq]
    linarith only [h]
  have hl : (5 / 2 : ℝ) ≤ Real.log t := hl16.trans (Real.log_le_log (by norm_num only) ht16)
  have hu : 0 < Real.log t := by linarith only [hl]
  have hlog := Real.log_le_sub_one_of_pos (show 0 < Real.log t / 2 by linarith only [hu])
  rw [Real.log_div hu.ne' (by norm_num only : (2 : ℝ) ≠ 0)] at hlog
  have hl2 : Real.log (Real.log t) ≤ Real.log t / 2 := by linarith only [hlog, Real.log_two_lt_d9]
  have htpos : 0 < 5 * t := by linarith only [ht16]
  have hi : 1 / (5 * t) ≤ (1 / 80 : ℝ) := by
    apply (div_le_iff₀ htpos).2
    nlinarith only [ht16]
  linarith only [hl, hl2, hi]

/-- If a zero count and its main term satisfy the stated Rosser-type error
at `t ≥ 2πe`, then their difference is at most `log t`. The explicit zero
count remains a separate hypothesis of this implication. -/
theorem zero_count_error_of_rosser {N M t : ℝ} (ht : 2 * Real.pi * Real.exp 1 ≤ t)
    (h :
      |N - M| ≤
        (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
          1 / (5 * t)) :
    |N - M| ≤ Real.log t :=
  h.trans (rosser_error_le_log ht)

/-- For `t ≥ 1000`, the logarithmic residual in the zero-tail estimate is
absorbed by the difference between `log t` and `log (t / 2π) + 1`.
Use a tangent bound for the logarithm and explicit bounds on `π`. -/
theorem tail_absorb {t : ℝ} (ht : 1000 ≤ t) :
    Real.pi * (4 * Real.log t + 1) ≤ t * (Real.log (2 * Real.pi) - 1) := by
  have ht0 : 0 < t := by linarith only [ht]
  have hl1000 : Real.log (1000 : ℝ) < 10 := by
    have h :=
      Real.log_le_log (show (0 : ℝ) < 1000 by norm_num only)
        (show (1000 : ℝ) ≤ 2 ^ (10 : ℕ) by norm_num only)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h, Real.log_two_lt_d9]
  have hl := Real.log_le_sub_one_of_pos (show 0 < t / 1000 by positivity)
  rw [Real.log_div ht0.ne' (by norm_num only : (1000 : ℝ) ≠ 0)] at hl
  have hlog : Real.log t ≤ 9 + t / 1000 := by linarith only [hl, hl1000]
  have hp : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hx : 0 ≤ 4 * Real.log t + 1 := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ t by linarith only [ht])
    linarith only [hh]
  have hp' := mul_le_mul_of_nonneg_right hp hx
  have hc : (1 / 2 : ℝ) ≤ Real.log (2 * Real.pi) - 1 := by
    linarith only [Analysis.log_two_mul_pi_gt]
  have hc' := mul_le_mul_of_nonneg_left hc ht0.le
  nlinarith only [hp', hlog, hc', ht]

/-- If `B` satisfies the displayed preliminary zero-tail bound at `t ≥ 1000`,
then `B ≤ log t / (πt)`. The preliminary zero-tail bound remains an explicit
hypothesis and is not supplied by this numerical comparison. -/
theorem zero_tail_of_preliminary {t B : ℝ} (ht : 1000 ≤ t)
    (hB : B ≤ (Real.log (t / (2 * Real.pi)) + 1) / (Real.pi * t) + (4 * Real.log t + 1) / t ^ 2) :
    B ≤ Real.log t / (Real.pi * t) := by
  have ht0 : 0 < t := by linarith only [ht]
  have hpt : 0 < Real.pi * t := mul_pos Real.pi_pos ht0
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht0
  have h := tail_absorb ht
  have hh := mul_le_mul_of_nonneg_right h ht0.le
  have hdiv : (4 * Real.log t + 1) / t ^ 2 ≤ (Real.log (2 * Real.pi) - 1) / (Real.pi * t) := by
    apply (div_le_div_iff₀ ht2 hpt).2
    nlinarith only [hh]
  have htpi : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (by positivity)
  rw [Real.log_div ht0.ne' htpi] at hB
  have heq :
    (Real.log t - Real.log (2 * Real.pi) + 1) / (Real.pi * t) +
        (Real.log (2 * Real.pi) - 1) / (Real.pi * t) =
      Real.log t / (Real.pi * t) := by
    rw [← add_div]
    congr 1
    ring
  linarith only [hB, hdiv, heq]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
