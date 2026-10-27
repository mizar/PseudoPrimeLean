/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaCriticalLine
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import PseudoPrime.Analysis.RealAxisDifferenceWeights

/-! # A global two-pole rational majorant for the critical-line Gamma norm -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Difference between the degree-ten even cosh lower polynomial, with pi>=157/50,
and the squared two-pole denominator times the upper endpoint pi<=22/7.
Its input is the squared height. Positivity on the nonnegative ray certifies
Gamma domination without a height grid or an input-integer certificate. -/
noncomputable def twoPoleGammaCoshPolynomial (z : ℝ) : ℝ :=
  1 + (157 / 50 : ℝ) ^ 2 / 2 * z + (157 / 50 : ℝ) ^ 4 / 24 * z ^ 2 +
      (157 / 50 : ℝ) ^ 6 / 720 * z ^ 3 +
      (157 / 50 : ℝ) ^ 8 / 40320 * z ^ 4 +
      (157 / 50 : ℝ) ^ 10 / 3628800 * z ^ 5 -
    (22 / 7 : ℝ) * (16 / 81 : ℝ) ^ 2 * (z + 9 / 16) ^ 2 * (z + 81 / 16) ^ 2

/-- For a squared-height parameter in [0,1], the certificate polynomial is positive.
Bound the negative quadratic and cubic monomials by the linear parameter, while
retaining the nonnegative higher powers. This handles the low-height part. -/
theorem twoPoleGammaCoshPolynomial_pos_of_le_one {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < twoPoleGammaCoshPolynomial z := by
  have hm := mul_nonneg hz (sub_nonneg.mpr hz1)
  have h2 : z ^ 2 ≤ z := by nlinarith only [hm]
  have h3 : z ^ 3 ≤ z := by
    have ht := mul_le_mul_of_nonneg_left h2 hz
    nlinarith only [ht, h2]
  unfold twoPoleGammaCoshPolynomial
  nlinarith only [hz, h2, h3, pow_nonneg hz 4, pow_nonneg hz 5]

/-- For a parameter at least one, the certificate polynomial is positive.
Shift the parameter by one; every coefficient is positive. Nonnegativity of
the shifted powers proves the high-height part without a numerical cutoff. -/
theorem twoPoleGammaCoshPolynomial_pos_of_one_le {z : ℝ} (hz : 1 ≤ z) :
    0 < twoPoleGammaCoshPolynomial z := by
  have hv : 0 ≤ z - 1 := sub_nonneg.mpr hz
  have hh : 0 < twoPoleGammaCoshPolynomial (1 + (z - 1)) := by
    unfold twoPoleGammaCoshPolynomial
    nlinarith only [hv, pow_nonneg hv 2, pow_nonneg hv 3, pow_nonneg hv 4, pow_nonneg hv 5]
  rw [show (1 : ℝ) + (z - 1) = z by ring] at hh
  exact hh

/-- The degree-ten cosh certificate is positive for every nonnegative squared
height. Join the two algebraic ranges at one. This is the global scalar input
to the two-pole Gamma majorant. -/
theorem twoPoleGammaCoshPolynomial_pos {z : ℝ} (hz : 0 ≤ z) : 0 < twoPoleGammaCoshPolynomial z := by
  by_cases h : z ≤ 1
  · exact twoPoleGammaCoshPolynomial_pos_of_le_one hz h
  · exact twoPoleGammaCoshPolynomial_pos_of_one_le (le_of_not_ge h)

/-- For any real argument and natural truncation length, the finite even Taylor
sum is at most cosh. Every omitted term of the absolutely convergent series is
nonnegative, including at negative arguments. This supports arbitrary finite
polynomial lower certificates without a restriction to a half-axis. -/
theorem even_cosh_partialSum_le (x : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, x ^ (2 * k) / ((2 * k).factorial : ℝ)) ≤ Real.cosh x := by
  have hn (k : ℕ) : 0 ≤ x ^ (2 * k) / ((2 * k).factorial : ℝ) := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg x) k
  exact
    (Real.hasSum_cosh x).tsum_eq ▸
      (Real.hasSum_cosh x).summable.sum_le_tsum (Finset.range n) (fun k _ ↦ hn k)

/-- At every real height, cosh(pi*t) dominates pi times the squared normalized
two-pole denominator. Use certified rational pi endpoints, the first six even
cosh terms and the global polynomial certificate. No floating-point estimate
or finite height grid is used. -/
theorem twoPole_cosh_dominates_denominator (t : ℝ) :
    Real.pi * (16 / 81 : ℝ) ^ 2 * (t ^ 2 + 9 / 16) ^ 2 * (t ^ 2 + 81 / 16) ^ 2 ≤
      Real.cosh (Real.pi * t) := by
  have hpLo : (157 / 50 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d20]
  have hpHi : Real.pi ≤ (22 / 7 : ℝ) := by linarith only [Real.pi_lt_d20]
  have hcos : Real.cosh ((157 / 50 : ℝ) * t) ≤ Real.cosh (Real.pi * t) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 157 / 50),
      abs_of_nonneg Real.pi_pos.le]
    exact mul_le_mul_of_nonneg_right hpLo (abs_nonneg t)
  have hs := even_cosh_partialSum_le ((157 / 50 : ℝ) * t) 6
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial] at hs
  have hP := twoPoleGammaCoshPolynomial_pos (sq_nonneg t)
  unfold twoPoleGammaCoshPolynomial at hP
  have hn :=
    mul_le_mul_of_nonneg_right hpHi
      (mul_nonneg (mul_nonneg (sq_nonneg (16 / 81 : ℝ)) (sq_nonneg (t ^ 2 + 9 / 16)))
        (sq_nonneg (t ^ 2 + 81 / 16)))
  nlinarith only [hcos, hs, hP, hn]

/-- At every real height, the critical-line Gamma norm is at most the closed
rational profile (81/16)/((t^2+9/16)*(t^2+81/16)). Use the exact squared Gamma
norm identity, the cosh denominator estimate and positive denominators.
This supplies a finite-scale alternative to the existing multi-node majorant. -/
theorem norm_Gamma_half_add_I_le_twoPole_closed (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤
      (81 / 16 : ℝ) / ((t ^ 2 + 9 / 16) * (t ^ 2 + 81 / 16)) := by
  have hA : 0 < t ^ 2 + 9 / 16 := add_pos_of_nonneg_of_pos (sq_nonneg t) (by norm_num only)
  have hB : 0 < t ^ 2 + 81 / 16 := add_pos_of_nonneg_of_pos (sq_nonneg t) (by norm_num only)
  have hd := mul_pos hA hB
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (by norm_num only) hd.le)).mp
  rw [norm_Gamma_half_add_I_sq, div_pow, div_le_div_iff₀ (Real.cosh_pos _) (pow_pos hd 2)]
  have h := twoPole_cosh_dominates_denominator t
  nlinarith only [h]

/-- The signed Poisson pair with scales 3/4,9/4 and coefficients 3/2,1/2 equals
the closed quartic-denominator profile. Combine the two fractions; their
quadratic numerator terms cancel. This connects Gamma domination to real-axis
nodes 5/4 and 11/4 in the retained Euler-difference interface. -/
theorem poissonDifferenceWeight_twoPole_eq_closed (t : ℝ) :
    poissonDifferenceWeight (3 / 4) (9 / 4) (3 / 2) (1 / 2) t =
      (81 / 16 : ℝ) / ((t ^ 2 + 9 / 16) * (t ^ 2 + 81 / 16)) := by
  have hA : 0 < t ^ 2 + 9 / 16 := add_pos_of_nonneg_of_pos (sq_nonneg t) (by norm_num only)
  have hB : 0 < t ^ 2 + 81 / 16 := add_pos_of_nonneg_of_pos (sq_nonneg t) (by norm_num only)
  norm_num only [poissonDifferenceWeight]
  rw [add_comm (9 / 16 : ℝ), add_comm (81 / 16 : ℝ), div_sub_div _ _ hA.ne' hB.ne']
  congr 1
  ring

/-- For every real height, the signed two-pole Poisson profile dominates the
critical-line Gamma norm. Rewrite the rational identity and apply the closed
majorant. This discharges the kernel-domination input to the zero-mass theorem. -/
theorem norm_Gamma_half_add_I_le_twoPole (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤
      poissonDifferenceWeight (3 / 4) (9 / 4) (3 / 2) (1 / 2) t := by
  rw [poissonDifferenceWeight_twoPole_eq_closed]
  exact norm_Gamma_half_add_I_le_twoPole_closed t

/-- A fourth-power comparison gives a rational lower bound for the quarter-power.
This supplies the denominator estimate in the principal Euler-ratio bound. -/
theorem two_neg_quarter_ge_four_fifths : (4 / 5 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have he : ((2 : ℝ) ^ (-(1 / 4 : ℝ))) ^ 4 = 1 / 2 := by
    rw [← Real.rpow_mul_natCast (by norm_num only : (0 : ℝ) ≤ 2)]
    norm_num only [Nat.cast_ofNat, Real.rpow_neg_one]
  apply
    (pow_le_pow_iff_left₀ (by norm_num only : (0 : ℝ) ≤ 4 / 5)
        (Real.rpow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) _) (by decide : (4 : ℕ) ≠ 0)).mp
  rw [he]
  norm_num only

end PseudoPrime.Analysis
