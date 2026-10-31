/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.DyadicResolventIntervals
public import PseudoPrime.Analysis.GeometricRatioBounds
public import PseudoPrime.Analysis.GammaDyadicIntervalBounds

/-! # Rational certificates for signed dyadic Euler costs -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Rational arithmetic bounds the full dyadic Euler cost by 9883/10000
and twice the odd-power cost by 545/400. All signed node contributions
remain in the finite sum. Kernel computation certifies both numerical margins. -/
theorem gamma_dyadic_euler_upper_checks :
    (AnalyticNumberTheory.Gamma.gammaResolventCoefficients.map
            (AnalyticNumberTheory.Gamma.gammaDyadicNodeUpper 1)).sum ≤
        (9883 / 10000 : ℚ) ∧
      2 *
          (AnalyticNumberTheory.Gamma.gammaResolventCoefficients.map
              (AnalyticNumberTheory.Gamma.gammaDyadicNodeUpper 2)).sum ≤
        (545 / 400 : ℚ) := by
  decide +kernel

/-- The actual signed dyadic Euler costs satisfy the finite rational bounds.
Sum the node inequalities and cast the kernel certificates into the reals.
These are unconditional bounds for the dyadic terms in both conductor parities. -/
theorem gamma_dyadic_euler_cost_bounds :
    Analysis.gammaPrimeEulerCost 2 ≤ (9883 / 10000 : ℝ) ∧
      2 * Analysis.gammaPrimeOddEulerCost 2 ≤ (545 / 400 : ℝ) := by
  have h1 :=
    List.sum_le_sum
      (fun ab hab ↦ AnalyticNumberTheory.Gamma.gamma_dyadic_node_le 1 (by norm_num only) ab hab)
  have h2 :=
    List.sum_le_sum
      (fun ab hab ↦ AnalyticNumberTheory.Gamma.gamma_dyadic_node_le 2 (by norm_num only) ab hab)
  simp only [pow_one] at h1
  change Analysis.gammaPrimeEulerCost 2 ≤ _ at h1
  change Analysis.gammaPrimeOddEulerCost 2 ≤ _ at h2
  have hc1 := (Rat.cast_le (K := ℝ)).mpr gamma_dyadic_euler_upper_checks.1
  have hc2 := (Rat.cast_le (K := ℝ)).mpr gamma_dyadic_euler_upper_checks.2
  norm_num only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div, Rat.cast_list_sum, List.map_map,
    Function.comp_def] at hc1 hc2
  constructor
  · linarith only [h1, hc1]
  · linarith only [h2, hc2]

/-- The weighted full dyadic Euler cost is at most 6851/10000. For the
odd-conductor minus-one branch, subtract the actual conductor difference
M log four, giving a weighted odd Euler cost at most 3/10. Certified log
two bounds and the signed ratio certificate prove both margins. -/
theorem gamma_dyadic_weighted_euler_bounds :
    Real.log 2 * Analysis.gammaPrimeEulerCost 2 ≤ (6851 / 10000 : ℝ) ∧
      2 * (Real.log 2 * Analysis.gammaPrimeOddEulerCost 2) -
          (11783423 / 25000000 : ℝ) * Real.log 4 ≤
        (3 / 10 : ℝ) := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have h1 := mul_le_mul_of_nonneg_left gamma_dyadic_euler_cost_bounds.1 hl
  have h2 := mul_le_mul_of_nonneg_left gamma_dyadic_euler_cost_bounds.2 hl
  have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num only [Nat.cast_ofNat] at h
    exact h
  constructor
  · nlinarith only [h1, Real.log_two_lt_d9]
  · rw [he]
    nlinarith only [h2, Real.log_two_lt_d9]

/-- For every scale at least 10000, the actual weighted minus-one dyadic
ramp series is at most 9/50. Bound the cutoff count by its logarithmic
quotient and use log two below one. The signed parity and cutoff tail
are retained by the existing actual-series bound. -/
theorem gamma_dyadic_minus_one_actual_ramp_le {x : ℝ} (hx : 10000 ≤ x) :
    Real.log 2 *
        ((∑' k : ℕ, Analysis.exponentialRampLocalCorrection (-1) ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x) ≤
      (9 / 50 : ℝ) := by
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hl1 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hr :=
    (Analysis.gamma_ramp_neg_one_series_le_count (by norm_num only : 1 < (2 : ℕ)) hx0).trans
      (div_le_div_of_nonneg_right
        (add_le_add (Analysis.gamma_ramp_count_le_log (by norm_num only : 1 < (2 : ℕ)) hx1) le_rfl)
        (Real.sqrt_nonneg x))
  have hw := mul_le_mul_of_nonneg_left hr hl0.le
  have he :
    Real.log 2 * ((Real.log ((99 / 40 : ℝ) * x) / Real.log 2 + 1) / Real.sqrt x) =
      (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x := by
    rw [← mul_div_assoc, mul_add, mul_one,
      mul_comm (Real.log 2) (Real.log ((99 / 40 : ℝ) * x) / Real.log 2), div_mul_cancel₀ _ hl0.ne']
  norm_num only [Nat.cast_ofNat] at hw
  rw [he] at hw
  exact
    hw.trans
      ((div_le_div_of_nonneg_right (add_le_add le_rfl hl1) (Real.sqrt_nonneg x)).trans
        (Analysis.gamma_small_prime_scale_ramp_bound hx))

/-- With character value minus one at two, the actual finite odd Euler
loss and full signed ramp loss, after subtracting M log four, total at
most 12/25 for every scale at least 10000. Apply both signed certificates.
This is the dyadic cost budget for the odd-conductor minus-one branch;
the arithmetic availability of the log-four gap is a separate conductor input. -/
theorem gamma_dyadic_minus_one_actual_cost_le {f : ℕ} (χ : DirichletCharacter ℂ f) (hχ : χ 2 = -1)
    (K : Finset ℕ) {x : ℝ} (hx : 10000 ≤ x) :
    (∑ k ∈ K,
            (1 - (χ (2 ^ (2 * k + 1))).re) *
              Analysis.gammaResolventMangoldtWeight (2 ^ (2 * k + 1))) +
          Real.log 2 *
            ((∑' k : ℕ,
                Analysis.exponentialRampLocalCorrection (-1) ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
              Real.sqrt x) -
        (11783423 / 25000000 : ℝ) * Real.log 4 ≤
      (12 / 25 : ℝ) := by
  have he := Analysis.gamma_minus_one_odd_prime_correction_le_cost χ Nat.prime_two hχ K
  have hr := gamma_dyadic_minus_one_actual_ramp_le hx
  have hc := gamma_dyadic_weighted_euler_bounds.2
  norm_num only [Nat.cast_ofNat] at he
  linarith only [he, hr, hc]

end PseudoPrime.LLS
