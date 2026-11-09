/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.DecimalLogBounds
public import PseudoPrime.Analysis.ExponentialRampCutoff
public import PseudoPrime.Analysis.ExponentialFixedPointBounds
public import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Smoothed Gamma mass and the logarithmic cutoff 46000 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The positive 15-term Taylor sum certifies exp(-99/40) <= 84163/1000000.
Take reciprocals of the positive lower exponential bound.
This bounds the mass lost by smoothing the lower cutoff. -/
theorem gamma_ramp_exp_cutoff_le : Real.exp (-(99 / 40 : ℝ)) ≤ (84163 / 1000000 : ℝ) := by
  have ht :
    (1000000 / 84163 : ℝ) ≤ ∑ k ∈ Finset.range 15, (99 / 40 : ℝ) ^ k / (k.factorial : ℝ) := by
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  have he := ht.trans (Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) 15)
  have hi := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 1000000 / 84163) he
  rw [Real.exp_neg, ← one_div]
  norm_num only at hi
  exact hi

/-- The exponential width ratio at 1/200 is at most 200501/200000.
Bound the Taylor tail after four terms and clear the constant denominator.
This controls the exact smoothed mass rather than the old sharp-cutoff mass. -/
theorem gamma_ramp_exp_width_ratio_le :
    (Real.exp (1 / 200 : ℝ) - 1) / (1 / 200) ≤ (200501 / 200000 : ℝ) := by
  have h :=
    Analysis.exp_le_taylor_add_two_next (n := 4) (by norm_num only : (0 : ℝ) ≤ 1 / 200)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  linarith only [h]

/-- The exact ramp mass equals one minus exp(-99/40) times the width ratio.
Use the exponential addition formula and the endpoint difference 1/200.
This connects the computed integral to the rational exponential certificates. -/
theorem gamma_ramp_mass_factor :
    1 - (Real.exp (-(247 / 100 : ℝ)) - Real.exp (-(99 / 40 : ℝ))) / (1 / 200) =
      1 - Real.exp (-(99 / 40 : ℝ)) * ((Real.exp (1 / 200 : ℝ) - 1) / (1 / 200)) := by
  rw [show -(247 / 100 : ℝ) = -(99 / 40) + 1 / 200 by norm_num only, Real.exp_add]
  ring

/-- Twice the actual ramp integral minus one is at least 83125234337/10^11.
Combine the exact integral with the certified cutoff exponential and width ratio.
This supplies the denominator for the smoothed coefficient-0.8 comparison. -/
theorem gamma_ramp_mass_lower :
    (83125234337 / 100000000000 : ℝ) ≤
      2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1 := by
  rw [Analysis.exponentialRampWeight_integral, gamma_ramp_mass_factor]
  have hr : 0 ≤ (Real.exp (1 / 200 : ℝ) - 1) / (1 / 200) :=
    div_nonneg (sub_nonneg.mpr (Real.one_le_exp (by norm_num only))) (by norm_num only)
  have hm := mul_le_mul gamma_ramp_exp_cutoff_le gamma_ramp_exp_width_ratio_le hr (by norm_num only)
  linarith only [hm]

theorem gamma_gamma_ramp_main_term_gt_squared_gap :
    ((11783423 / 25000000 : ℝ) + 1 / 800) ^ 2 <
      (83125234337 / 100000000000 : ℝ) ^ 2 * (32 / 99) := by
  norm_num only

/-- For positive L, the actual smoothed main term exceeds (M+1/800)L,
where M=11783423/25000000. Multiply the squared coefficient gap by L and
use the actual ramp integral lower bound. This is the strict comparison used
when the analytic error budget has been connected. -/
theorem gamma_ramp_main_term_gt {L : ℝ} (hL : 0 < L) :
    ((11783423 / 25000000 : ℝ) + 1 / 800) * L <
      (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) *
        Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have hc :=
    mul_lt_mul_of_pos_right
      (Analysis.coefficient_lt_mul_sqrt_of_sq_lt
        (by norm_num only : (0 : ℝ) ≤ 83125234337 / 100000000000)
        (by norm_num only : (0 : ℝ) ≤ 32 / 99) gamma_gamma_ramp_main_term_gt_squared_gap)
      hL
  have hm :=
    mul_le_mul_of_nonneg_right gamma_ramp_mass_lower (Real.sqrt_nonneg ((32 / 99 : ℝ) * L ^ 2))
  rw [Real.sqrt_mul (by norm_num only : (0 : ℝ) ≤ 32 / 99), Real.sqrt_sq hL.le] at hm ⊢
  nlinarith only [hc, hm]

/-- For L >= 46000, the actual smoothed main term cannot be at most
M L + 4987/90. The proved main-term allowance exceeds the total error budget.
This is the final scalar contradiction, with the arithmetic comparison still
requiring the separate analytic principal, remainder and local estimates. -/
theorem gamma_ramp_inequality_false_of_log_ge {L : ℝ} (hL : 46000 ≤ L) :
    ¬((2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) *
          Real.sqrt ((32 / 99 : ℝ) * L ^ 2) ≤
        (11783423 / 25000000 : ℝ) * L + 4987 / 90) := by
  have hm := gamma_ramp_main_term_gt (by linarith only [hL] : 0 < L)
  linarith only [hm, hL]

/-- For a natural input n >= 10^20000, its logarithm is strictly greater than
46000. Apply logarithmic monotonicity to the cast power and log(10) > 23/10.
The proof avoids expanding the large natural power and supplies the public wrapper gate. -/
theorem log_nat_gt_46000_of_decimal {n : ℕ} (hn : 10 ^ 20000 ≤ n) : (46000 : ℝ) < Real.log n := by
  have hpos : 0 < (10 : ℝ) ^ (20000 : ℕ) := pow_pos (by norm_num only) _
  have hcast : (10 : ℝ) ^ (20000 : ℕ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog := Real.log_le_log hpos hcast
  rw [Real.log_pow] at hlog
  norm_num only at hlog
  linarith only [hlog, log_ten_gt_twenty_three_tenths]

/-- The logarithm of 46000 is below eleven. The lower bound exp(1)>=27/10
and its eleventh power give the exponential comparison. This anchors the uniform log bound. -/
theorem log_46000_lt_eleven : Real.log (46000 : ℝ) < 11 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num only : (0 : ℝ) < 46000)).mpr
  have he : (27 / 10 : ℝ) ≤ Real.exp 1 :=
    (by norm_num only : (27 / 10 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
  rw [show (11 : ℝ) = (11 : ℕ) * 1 by norm_num only, Real.exp_nat_mul]
  exact
    (by norm_num only : (46000 : ℝ) < (27 / 10 : ℝ) ^ (11 : ℕ)).trans_le
      (pow_le_pow_left₀ (by norm_num only) he 11)

/-- For L>=46000, log(L)<=L/4000. Apply log(t)<=t-1 to L/46000
and the certified anchor log(46000)<11. This extends the endpoint estimate to all large inputs. -/
theorem ramp_log_bound {L : ℝ} (hL : 46000 ≤ L) : Real.log L ≤ L / 4000 := by
  have hL0 : 0 < L := by linarith only [hL]
  have ht := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num only : (0 : ℝ) < 46000))
  rw [Real.log_div hL0.ne' (by norm_num only : (46000 : ℝ) ≠ 0)] at ht
  linarith only [ht, log_46000_lt_eleven, hL]

/-- For nonnegative L, sqrt((32/99)L^2)>=(9/16)L. Certify the rational
square-root coefficient and multiply by L. This bounds the normalized lower-sum error. -/
theorem ramp_scale_sqrt_lower {L : ℝ} (hL : 0 ≤ L) :
    (9 / 16 : ℝ) * L ≤ Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have hc : (9 / 16 : ℝ) ≤ Real.sqrt (32 / 99 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 32 / 99),
      Real.sqrt_nonneg (32 / 99 : ℝ)]
  rw [Real.sqrt_mul (by norm_num only : (0 : ℝ) ≤ 32 / 99), Real.sqrt_sq hL]
  exact mul_le_mul_of_nonneg_right hc hL

/-- For L>=46000, the fixed ramp scale (32/99)L^2 is at least one.
Check the quadratic inequality. This supplies the scaled arithmetic error's domain. -/
theorem ramp_scale_ge_one {L : ℝ} (hL : 46000 ≤ L) : (1 : ℝ) ≤ (32 / 99 : ℝ) * L ^ 2 := by
  nlinarith only [hL, sq_nonneg (L - 46000)]

/-- For L>=46000, the logarithm of the ramp endpoint (4/5)L^2 is at most
L/2000. Compare with L^2 and apply log(L)<=L/4000. This makes the error estimate uniform. -/
theorem ramp_endpoint_log_upper {L : ℝ} (hL : 46000 ≤ L) :
    Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) ≤ L / 2000 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc :=
    Real.log_le_log
      (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 32 / 99) (sq_pos_of_pos hL0))
        (by norm_num only : (0 : ℝ) < 99 / 40))
      (show ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) ≤ L ^ 2 by nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hc
  norm_num only at hc
  linarith only [hc, ramp_log_bound hL]

end PseudoPrime.LLS
