/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Explicit square-root cost for higher prime powers -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For x ≥ 1 and exponent u ≤ 1/2, psi(x^u) is at most 6sqrt x.
Combine the explicit Chebyshev bound with monotonicity of real powers.
This supplies each root term in the Costa-Pereira inequality. -/
theorem psi_rpow_le_six_sqrt {x u : ℝ} (hx : 1 ≤ x) (hu : u ≤ 1 / 2) :
    Chebyshev.psi (x ^ u) ≤ 6 * Real.sqrt x := by
  have hp := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg (zero_le_one.trans hx) u)
  have hr : x ^ u ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx hu
  have hl : Real.log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  have hm := mul_le_mul_of_nonneg_right hl (Real.rpow_nonneg (zero_le_one.trans hx) u)
  nlinarith only [hp, hr, hm]

/-- For x ≥ 1, higher prime powers have total Mangoldt mass at most 18sqrt x.
Apply Costa-Pereira and the three explicit root bounds. No RH is needed.
This is the arithmetic higher-power budget for the cubic kernel. -/
theorem psi_sub_theta_le_eighteen_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 18 * Real.sqrt x := by
  have h2 := psi_rpow_le_six_sqrt (u := (2 : ℝ)⁻¹) hx (by norm_num only)
  have h3 := psi_rpow_le_six_sqrt (u := (3 : ℝ)⁻¹) hx (by norm_num only)
  have h5 := psi_rpow_le_six_sqrt (u := (5 : ℝ)⁻¹) hx (by norm_num only)
  linarith only [Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x, h2, h3, h5]

/-- For x ≥ 1 and arbitrary real weights at most 1/3, twice the weighted
nonprime Mangoldt mass is at most 12sqrt x. Compare termwise and use the exact
psi-theta decomposition. This is the cubic higher-prime-power defect interface. -/
theorem composite_mangoldt_weight_le_twelve_sqrt {x : ℝ} (hx : 1 ≤ x) (w : ℕ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, w n ≤ 1 / 3) :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime),
        2 * ArithmeticFunction.vonMangoldt n * w n) ≤
      12 * Real.sqrt x := by
  have ht :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime),
        2 * ArithmeticFunction.vonMangoldt n * w n) ≤
      (2 / 3 : ℝ) *
        ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime), ArithmeticFunction.vonMangoldt n := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have h :=
      mul_le_mul_of_nonneg_left (hw n (Finset.mem_filter.mp hn).1)
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
          (ArithmeticFunction.vonMangoldt_nonneg (n := n)))
    nlinarith only [h]
  rw [← Chebyshev.psi_sub_theta_eq_sum_not_prime] at ht
  linarith only [ht, psi_sub_theta_le_eighteen_sqrt hx]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
