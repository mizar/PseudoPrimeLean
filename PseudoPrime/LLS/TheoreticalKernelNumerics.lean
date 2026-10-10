/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TheoreticalKernelProfiles

/-! # Rational certificates for the gamma-kernel parameter choices

Taylor lower bounds for the exponential verify the parameters of Section 6.3.
The coefficient comparisons use an explicit upper input for the kernel mass;
a numerical evaluation of the actual mass remains a separate analytic proof.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A nonnegative Taylor truncation bounding `1/b` certifies `exp(-a)≤b`
for `b>0`. The exponential series gives the lower bound before reciprocation.
This turns rational Taylor certificates into the gamma-parameter estimates. -/
theorem exp_neg_le_of_taylor {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (n : ℕ)
    (hs : 1 / b ≤ ∑ i ∈ Finset.range n, a ^ i / (Nat.factorial i : ℝ)) : Real.exp (-a) ≤ b := by
  rw [Real.exp_neg, ← one_div]
  have he := hs.trans (Real.sum_le_exp_of_nonneg ha n)
  have hi := one_div_le_one_div_of_le (one_div_pos.mpr hb) he
  simpa only [one_div_one_div] using hi

/-- At the Section 6.3 parameter `2.452` for index `2`,
the negative exponential is bounded by the displayed rational number.
Twelve nonnegative Taylor terms certify the reciprocal lower bound. -/
theorem gamma_two_exp_bound : Real.exp (-(1226 / 500 : ℝ)) ≤ 863 / 10000 := by
  apply exp_neg_le_of_taylor (by norm_num only) (by norm_num only) 12
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

/-- At the Section 6.3 parameter `2.025` for index `3`,
the negative exponential is bounded by the displayed rational number.
Twelve nonnegative Taylor terms certify the reciprocal lower bound. -/
theorem gamma_three_exp_bound : Real.exp (-(81 / 40 : ℝ)) ≤ 33 / 250 := by
  apply exp_neg_le_of_taylor (by norm_num only) (by norm_num only) 12
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

/-- At the Section 6.3 parameter `1.825` for index `4`,
the negative exponential is bounded by the displayed rational number.
Twelve nonnegative Taylor terms certify the reciprocal lower bound. -/
theorem gamma_four_exp_bound : Real.exp (-(73 / 40 : ℝ)) ≤ 81 / 500 := by
  apply exp_neg_le_of_taylor (by norm_num only) (by norm_num only) 12
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

/-- The index-two coefficient remains below `4/5` after inflating the mass
bound `471/1000` by `10001/10000`. The exponential certificate bounds the denominator.
This leaves a fixed positive epsilon for the Proposition 6.1 specialization. -/
theorem gamma_two_coefficient :
    (1226 / 500 : ℝ) * (4710471 / 10000000) ^ 2 <
      (4 / 5) * (1 - 2 * Real.exp (-(1226 / 500 : ℝ))) ^ 2 := by
  have he := gamma_two_exp_bound
  have hd : (8274 / 10000 : ℝ) ≤ 1 - 2 * Real.exp (-(1226 / 500 : ℝ)) := by linarith only [he]
  have hs := mul_self_le_mul_self (by norm_num only : (0 : ℝ) ≤ 8274 / 10000) hd
  nlinarith only [hs]

/-- The index-three coefficient remains below `7/10` after inflating the mass
bound `471/1000` by `10001/10000`. A rational denominator bound follows from
the Taylor exponential certificate. This allows fixed epsilon in Proposition 6.1. -/
theorem gamma_three_coefficient :
    (81 / 40 : ℝ) * (2 * (4710471 / 10000000)) ^ 2 <
      (7 / 10) * (2 - 3 * Real.exp (-(81 / 40 : ℝ))) ^ 2 := by
  have he := gamma_three_exp_bound
  have hd : (401 / 250 : ℝ) ≤ 2 - 3 * Real.exp (-(81 / 40 : ℝ)) := by linarith only [he]
  have hs := mul_self_le_mul_self (by norm_num only : (0 : ℝ) ≤ 401 / 250) hd
  nlinarith only [hs]

/-- The index-four gamma parameter gives coefficient strictly below `659/1000`
after inflating the mass bound by `10001/10000`. The exponential certificate
bounds the denominator from below; squaring it leaves a strict rational margin.
This sharper numerical input supports bounds after reducing the modulus. -/
theorem gamma_four_coefficient_659 :
    (73 / 40 : ℝ) * (3 * (4710471 / 10000000)) ^ 2 <
      (659 / 1000) * (3 - 4 * Real.exp (-(73 / 40 : ℝ))) ^ 2 := by
  have he := gamma_four_exp_bound
  have hd : (294 / 125 : ℝ) ≤ 3 - 4 * Real.exp (-(73 / 40 : ℝ)) := by linarith only [he]
  have hs := mul_self_le_mul_self (by norm_num only : (0 : ℝ) ≤ 294 / 125) hd
  nlinarith only [hs]

/-- For every real index at least four, the inflated gamma coefficient is below
`659/1000`. Cross-multiplication compares its ratio with the index-four ratio;
squaring and applying the sharper certificate gives the uniform strict margin.
This is the numerical input for the improved fixed-index gamma bound. -/
theorem gamma_large_index_coefficient_659 {h : ℝ} (hh : 4 ≤ h) :
    (73 / 40 : ℝ) * ((h - 1) * (4710471 / 10000000)) ^ 2 <
      (659 / 1000) * (h - 1 - h * Real.exp (-(73 / 40 : ℝ))) ^ 2 := by
  let e := Real.exp (-(73 / 40 : ℝ))
  have he : e ≤ 81 / 500 := gamma_four_exp_bound
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hd4 : 0 < 3 - 4 * e := by linarith only [he]
  have hsmall : 0 < 1 - e := by linarith only [he]
  have hprod := mul_nonneg (sub_nonneg.mpr hh) hsmall.le
  have hdh : 0 < h - 1 - h * e := by nlinarith only [hprod, hd4]
  have hcross : (3 - 4 * e) * (h - 1) ≤ 3 * (h - 1 - h * e) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hh) he0]
  have hs := mul_self_le_mul_self (mul_nonneg hd4.le (by linarith only [hh] : 0 ≤ h - 1)) hcross
  have hlower :=
    mul_le_mul_of_nonneg_left hs
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 73 / 40) (sq_nonneg (4710471 / 10000000 : ℝ)))
  have hupper := mul_lt_mul_of_pos_right gamma_four_coefficient_659 (sq_pos_of_pos hdh)
  change (73 / 40 : ℝ) * ((h - 1) * (4710471 / 10000000)) ^ 2 < (659 / 1000) * (h - 1 - h * e) ^ 2
  apply (mul_lt_mul_iff_of_pos_right (sq_pos_of_pos hd4)).mp
  nlinarith only [hlower, hupper]

/-- For every real index at least four, the sharper `659/1000` certificate
implies the paper's coefficient `33/50`. Monotonicity of multiplication by a
nonnegative square retains the strict inequality for the existing parameter API. -/
theorem gamma_large_index_coefficient {h : ℝ} (hh : 4 ≤ h) :
    (73 / 40 : ℝ) * ((h - 1) * (4710471 / 10000000)) ^ 2 <
      (33 / 50) * (h - 1 - h * Real.exp (-(73 / 40 : ℝ))) ^ 2 := by
  apply lt_of_lt_of_le (gamma_large_index_coefficient_659 hh)
  exact mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)

/-- Every integer index greater than one admits a positive gamma parameter
with positive denominator and coefficient below the paper's theoretical value.
Use the three certified parameters and the uniform index-four comparison.
The inflated mass leaves fixed positive slack for the analytic asymptotic estimate. -/
theorem gamma_parameters_for_index (h : ℕ) (hh : 1 < h) :
    ∃ lambda : ℝ,
      0 < lambda ∧
        0 < (h : ℝ) - 1 - h * Real.exp (-lambda) ∧
        lambda * (((h : ℝ) - 1) * (4710471 / 10000000)) ^ 2 <
          theoreticalCoefficient h * ((h : ℝ) - 1 - h * Real.exp (-lambda)) ^ 2 := by
  by_cases h2 : h = 2
  · subst h
    refine ⟨1226 / 500, by norm_num only, ?_, ?_⟩
    · have he := gamma_two_exp_bound
      norm_num only
      linarith only [he]
    · have hc := gamma_two_coefficient
      norm_num only [theoreticalCoefficient, ite_true, ite_false] at hc ⊢
      exact hc
  · by_cases h3 : h = 3
    · subst h
      refine ⟨81 / 40, by norm_num only, ?_, ?_⟩
      · have he := gamma_three_exp_bound
        norm_num only
        linarith only [he]
      · have hc := gamma_three_coefficient
        norm_num only [theoreticalCoefficient, ite_true, ite_false] at hc ⊢
        exact hc
    · have htwo : 2 ≤ h := Nat.succ_le_iff.mpr hh
      have hthree : 3 ≤ h := Nat.succ_le_iff.mpr (lt_of_le_of_ne htwo (fun he ↦ h2 he.symm))
      have hfour : 4 ≤ h := Nat.succ_le_iff.mpr (lt_of_le_of_ne hthree (fun he ↦ h3 he.symm))
      have hreal : (4 : ℝ) ≤ h := Nat.cast_le.mpr hfour
      refine ⟨73 / 40, by norm_num only, ?_, ?_⟩
      · have he := gamma_four_exp_bound
        have hprod :=
          mul_nonneg (sub_nonneg.mpr hreal)
            (by linarith only [he] : 0 ≤ 1 - Real.exp (-(73 / 40 : ℝ)))
        nlinarith only [hprod, he]
      · rw [theoreticalCoefficient, ite_eq_right h2, ite_eq_right h3]
        exact gamma_large_index_coefficient hreal

/-- The paper's three theoretical coefficients are strictly positive.
Case analysis on the definition reduces each branch to a rational inequality.
This ensures nonnegative cutoff radii in the least-prime comparison. -/
theorem theoreticalCoefficient_pos (h : ℕ) : 0 < theoreticalCoefficient h := by
  unfold theoreticalCoefficient
  split_ifs <;> norm_num only

end PseudoPrime.LLS.PaperStatements
