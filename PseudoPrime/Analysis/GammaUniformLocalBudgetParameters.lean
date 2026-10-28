/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneCommonNumerics
public import PseudoPrime.LLS.GammaUniformLocalBounds

/-! # Parameterized local budgets for the uniform Gamma subgroup bound

A positive lower coefficient for the scale root and an upper logarithmic ratio
control the normalized nonunit loss. Rational certificates give a tighter concrete
budget while keeping the coefficient-four-fifths kernel and character estimates.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The logarithm of 71/2 is less than 357/100. Use a six-term Taylor lower
bound for exp(57/100) and the certified lower bound for exp 1.
This supplies the cube-root anchor in the uniform local budget. -/
theorem log_thirtyFiveHalf_lt_357_div_100 : Real.log (71 / 2 : ℝ) < 357 / 100 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num only : (0 : ℝ) < 71 / 2)).mpr
  have he : (2718 / 1000 : ℝ) ≤ Real.exp 1 :=
    (by norm_num only : (2718 / 1000 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
  have ht := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 57 / 100) 6
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at ht
  have hm :=
    mul_le_mul (pow_le_pow_left₀ (by norm_num only) he 3) ht (by norm_num only)
      (pow_nonneg (Real.exp_pos 1).le 3)
  rw [show (357 / 100 : ℝ) = (3 : ℕ) * 1 + 57 / 100 by norm_num only, Real.exp_add,
    Real.exp_nat_mul]
  exact
    (by norm_num only : (71 / 2 : ℝ) < (2718 / 1000) ^ 3 * (707286097519 / 400000000000)).trans_le
      hm

/-- For L ≥ 0, the root of the ramp scale (32/99)L^2 is at least (71/125)L.
Check the squared rational coefficient and multiply the root identity by L.
This tightens the normalized nonunit-loss bound without changing the scale. -/
theorem uniform_ramp_scale_sqrt_lower_71_div_125 {L : ℝ} (hL : 0 ≤ L) :
    (71 / 125 : ℝ) * L ≤ Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have hc : (71 / 125 : ℝ) ≤ Real.sqrt (32 / 99 : ℝ) := by
    apply (Real.le_sqrt (by norm_num only) (by norm_num only)).mpr
    norm_num only
  rw [Real.sqrt_mul (by norm_num only : (0 : ℝ) ≤ 32 / 99), Real.sqrt_sq hL]
  exact mul_le_mul_of_nonneg_right hc hL

/-- For L ≥ 44739, log L / L^(1/3) is at most 1071/3550 on the full half-line.
Anchor the cube root at 71/2, use the certified logarithm and log u ≤ u-1.
This gives a tighter parameter for the uniform prime-support split. -/
theorem log_div_cuberoot_le_of_ge_44739 {L : ℝ} (hL : 44739 ≤ L) :
    Real.log L / L ^ (1 / 3 : ℝ) ≤ 1071 / 3550 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc :=
    Real.rpow_le_rpow (by norm_num only : (0 : ℝ) ≤ (71 / 2) ^ 3)
      (show (71 / 2 : ℝ) ^ 3 ≤ L by linarith only [hL]) (by norm_num only : (0 : ℝ) ≤ 1 / 3)
  have he : ((71 / 2 : ℝ) ^ 3) ^ (1 / 3 : ℝ) = 71 / 2 := by
    rw [← Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 71 / 2)]
    norm_num only [Real.rpow_one]
  rw [he] at hc
  have hu0 := Real.rpow_pos_of_pos hL0 (1 / 3 : ℝ)
  have ht := Real.log_le_sub_one_of_pos (div_pos hu0 (by norm_num only : (0 : ℝ) < 71 / 2))
  rw [Real.log_div hu0.ne' (by norm_num only : (71 / 2 : ℝ) ≠ 0), Real.log_rpow hL0] at ht
  rw [div_le_iff₀ hu0]
  linarith only [hc, ht, log_thirtyFiveHalf_lt_357_div_100]

/-- For nonzero q with log q > 1 and ramp cutoff at least one, suppose the
scale root is at least a*log q with a > 0 and the logarithmic cube-root ratio is
at most beta. Twice the normalized nonunit loss is at most (4/a)(beta+3/2).
Combine the split-prime estimate with these two scalar inputs.
This common interface supports every certified choice of the two parameters. -/
theorem gamma_commonFactor_budget_of_ratio_sqrt {q : ℕ} [NeZero q] {a beta : ℝ} (ha : 0 < a)
    (hL : 1 < Real.log q) (hcut : 1 ≤ (99 / 40 : ℝ) * ((32 / 99 : ℝ) * (Real.log q) ^ 2))
    (hroot : a * Real.log q ≤ Real.sqrt ((32 / 99 : ℝ) * (Real.log q) ^ 2))
    (hlog : Real.log (Real.log q) / (Real.log q) ^ (1 / 3 : ℝ) ≤ beta) :
    let L := Real.log q;
    let x := (32 / 99 : ℝ) * L ^ 2;
    2 *
        (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((99 / 40 : ℝ) * x) q /
          Real.sqrt x) ≤
      (4 / a) * (beta + 3 / 2) := by
  let L := Real.log q
  let x := (32 / 99 : ℝ) * L ^ 2
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hx0 : 0 < x := mul_pos (by norm_num only : (0 : ℝ) < 32 / 99) (sq_pos_of_pos hL0)
  have hs0 := Real.sqrt_pos.mpr hx0
  have hu0 := Real.rpow_pos_of_pos hL0 (1 / 3 : ℝ)
  have hlog0 := Real.log_pos hL
  have hp : L ^ (2 / 3 : ℝ) = L / L ^ (1 / 3 : ℝ) := by
    apply (eq_div_iff hu0.ne').mpr
    rw [← Real.rpow_add hL0]
    norm_num only [Real.rpow_one]
  have hc : Real.log ((99 / 40 : ℝ) * x) ≤ 2 * Real.log L := by
    have harg : (99 / 40 : ℝ) * x ≤ L ^ 2 := by
      dsimp only [x]
      nlinarith only [sq_nonneg L]
    have he := Real.log_le_log (zero_lt_one.trans_le hcut) harg
    rw [Real.log_pow] at he
    norm_num only at he
    exact he
  have hF0 : 0 ≤ L ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * L / Real.log L :=
    add_nonneg (Real.rpow_pos_of_pos hL0 _).le (div_nonneg (by linarith only [hL0]) hlog0.le)
  have hnum :=
    (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum_le_log_two_thirds (NeZero.ne q) hx0
          hcut hL).trans
      (mul_le_mul_of_nonneg_left hc hF0)
  have he :
    (L ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * L / Real.log L) * (2 * Real.log L) =
      2 * L * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) := by
    rw [hp]
    have hbcan : ((3 / 2 : ℝ) * L / Real.log L) * (2 * Real.log L) = 3 * L := by
      calc
        _ = 2 * ((3 / 2 : ℝ) * L / Real.log L * Real.log L) := by ring
        _ = 2 * ((3 / 2 : ℝ) * L) := by rw [div_mul_cancel₀ _ hlog0.ne']
        _ = 3 * L := by ring
    rw [add_mul, hbcan]
    ring
  change
    AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((99 / 40 : ℝ) * x) q ≤
      (L ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * L / Real.log L) * (2 * Real.log L) at hnum
  rw [he] at hnum
  have hB0 : 0 ≤ Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2 :=
    add_nonneg (div_nonneg hlog0.le hu0.le) (by norm_num only)
  have hr : L / Real.sqrt x ≤ 1 / a := by
    apply (div_le_div_iff₀ hs0 ha).mpr
    nlinarith only [hroot]
  have hm := mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hB0)
  have ht :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by norm_num only : (0 : ℝ) ≤ 2))
      (Real.sqrt_nonneg x)
  calc
    _ =
        2 * AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((99 / 40 : ℝ) * x) q /
          Real.sqrt x :=
      by ring
    _ ≤ 2 * (2 * L * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2)) / Real.sqrt x := ht
    _ = 4 * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) * (L / Real.sqrt x) := by ring
    _ ≤ 4 * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) * (1 / a) := hm
    _ = (4 / a) * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) := by ring
    _ ≤ (4 / a) * (beta + 3 / 2) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hlog (3 / 2 : ℝ))
        (div_nonneg (by norm_num only : (0 : ℝ) ≤ 4) ha.le)

/-- For nonzero q with log q ≥ 44739, twice the normalized nonunit loss
at the coefficient-four-fifths ramp cutoff is at most 63960/5041.
Instantiate the parameterized budget with a=71/125 and beta=1071/3550.
This is the tightened local allowance for every proper-subgroup index. -/
theorem gamma_commonFactor_budget_of_log_ge_44739 {q : ℕ} [NeZero q] (hL : 44739 ≤ Real.log q) :
    let L := Real.log q;
    let x := (32 / 99 : ℝ) * L ^ 2;
    2 *
        (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((99 / 40 : ℝ) * x) q /
          Real.sqrt x) ≤
      63960 / 5041 := by
  have h1 : 1 < Real.log q := by linarith only [hL]
  have hroot := uniform_ramp_scale_sqrt_lower_71_div_125 (zero_lt_one.trans h1).le
  have hx : 1 ≤ (32 / 99 : ℝ) * (Real.log q) ^ 2 := by
    nlinarith only [hL, sq_nonneg (Real.log q - 44739)]
  have hcut : 1 ≤ (99 / 40 : ℝ) * ((32 / 99 : ℝ) * (Real.log q) ^ 2) := by linarith only [hx]
  have ht :=
    gamma_commonFactor_budget_of_ratio_sqrt (by norm_num only : (0 : ℝ) < 71 / 125) h1 hcut hroot
      (log_div_cuberoot_le_of_ge_44739 hL)
  norm_num only at ht
  exact ht

/-- For L ≥ 45561, fixed error 40159/900 and local allowance 63960/5041
sum to less than L/795. Verify the rational endpoint margin.
This closes the uniform Gamma contradiction at the smaller logarithmic start. -/
theorem gamma_uniform_error_budget_of_ge_45561 {L : ℝ} (hL : 45561 ≤ L) :
    (40159 / 900 : ℝ) + 63960 / 5041 < L / 795 := by linarith only [hL]

end PseudoPrime.Analysis
