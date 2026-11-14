/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100TermBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CoeffBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FiniteArithmetic

/-! # Error of the rational Euler–Maclaurin approximation -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

private theorem norm_endpoint_sum (t : ℚ) (ht0 : 0 ≤ t) (ht100 : t ≤ 100) :
    ‖(∑ n ∈ Finset.Icc (1 : ℕ) 127,
          ((n : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I))) -
            Analysis.rationalComplexCast (endpointPowerApprox t (gridLogApprox n))))‖ ≤
      (127 : ℝ) * (51 / 100000000) := by
  calc
    _ ≤
        ∑ n ∈ Finset.Icc (1 : ℕ) 127,
          ‖(n : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I))) -
              Analysis.rationalComplexCast (endpointPowerApprox t (gridLogApprox n))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc (1 : ℕ) 127, (51 / 100000000 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact
        norm_endpoint_term_approx t ht0 ht100 n
          (Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp hn).1, Nat.le_trans (Finset.mem_Icc.mp hn).2 (by norm_num only)⟩)
    _ = _ := by norm_num only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.cast_ofNat]

private theorem norm_endpoint_sum_correction (A B C u v : ℂ)
    (h : ‖A - B‖ ≤ (127 : ℝ) * (51 / 100000000)) (hc : ‖C‖ ≤ 10)
    (huv : ‖u - v‖ ≤ (51 / 100000000 : ℝ)) : ‖(A + C * u) - (B + C * v)‖ ≤ (7 / 100000 : ℝ) := by
  have ht := norm_add_le (A - B) (C * (u - v))
  have hmul : ‖C * (u - v)‖ ≤ (10 : ℝ) * (51 / 100000000) := by
    rw [norm_mul]
    exact mul_le_mul hc huv (norm_nonneg _) (by norm_num only)
  have heq : (A + C * u) - (B + C * v) = (A - B) + C * (u - v) := by ring
  rw [heq]
  linarith only [h, hmul, ht]

/-- At a rational ordinate between 14 and 100, the computed rational finite approximation
differs from the analytic Euler–Maclaurin approximation by at most `7/100000`. The proof
adds the 127 uniform term errors and the correction term error. -/
theorem norm_endpoint_finite_approx (t : ℚ) (ht14 : 14 ≤ t) (ht100 : t ≤ 100) :
    ‖finiteEM8 (t : ℝ) - Analysis.rationalComplexCast (endpointFiniteApprox t)‖ ≤
      (7 / 100000 : ℝ) := by
  have ht0 : 0 ≤ t := by linarith only [ht14]
  have ht14R : (14 : ℝ) ≤ t := by exact_mod_cast ht14
  have ht100R : (t : ℝ) ≤ 100 := by exact_mod_cast ht100
  have hs := norm_endpoint_sum t ht0 ht100
  rw [Finset.sum_sub_distrib] at hs
  have hc := norm_finiteEM8_coefficient_le t ht14R ht100R
  have hu :=
    norm_endpoint_term_approx t ht0 ht100 128
      (Finset.mem_Icc.mpr ⟨by norm_num only, by norm_num only⟩)
  rw [finiteEM8_eq_grouped, endpointFiniteApprox, endpointFiniteCorrection,
    Analysis.rationalComplexCast_add, Analysis.rationalComplexCast_sum,
    Analysis.rationalComplexCast_mul, endpoint_coefficient_cast]
  exact norm_endpoint_sum_correction _ _ _ _ _ hs hc hu

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
