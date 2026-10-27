/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaFiniteEulerIntervals
public import PseudoPrime.Analysis.GammaPrimePowerCosts

/-! # Signed rational intervals for exact geometric prime Euler costs -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The geometric positive-power ratio is increasing below one.
Clear the two positive denominators and cancel the common product.
This transfers certified node intervals to exact prime Euler costs. -/
theorem gamma_geometric_ratio_mono {r s : ℝ} (hrs : r ≤ s) (hs : s < 1) :
    r / (1 - r) ≤ s / (1 - s) := by
  apply (div_le_div_iff₀ (sub_pos.mpr (hrs.trans_lt hs)) (sub_pos.mpr hs)).mpr
  nlinarith only [hrs]

/-- Rational lower allowance for the signed prime Euler cost.
Apply r/(1-r) to each endpoint and select the lower geometric endpoint
for nonnegative coefficients, the upper endpoint for negative coefficients.
All upper node endpoints must be strictly below one. -/
def gammaPrimeEulerIntervalLower (r : ℚ → ℚ × ℚ) : ℚ :=
  (gammaResolventCoefficients.map
      (fun ab ↦
        ab.2 *
          (if 0 ≤ ab.2 then (r ab.1).1 / (1 - (r ab.1).1) else (r ab.1).2 / (1 - (r ab.1).2)))).sum

/-- Rational upper allowance for the signed prime Euler cost.
Reverse the endpoint selection in the signed lower allowance.
This preserves cancellation among the fixed Gamma resolvent coefficients. -/
def gammaPrimeEulerIntervalUpper (r : ℚ → ℚ × ℚ) : ℚ :=
  (gammaResolventCoefficients.map
      (fun ab ↦
        ab.2 *
          (if 0 ≤ ab.2 then (r ab.1).2 / (1 - (r ab.1).2) else (r ab.1).1 / (1 - (r ab.1).1)))).sum

/-- A rational interval enclosing a node and ending below one encloses
its geometric ratio. Cast the endpoints and apply monotonicity twice.
This is the scalar interface used by the signed list combination. -/
theorem gamma_geometric_ratio_interval {l u : ℚ} {v : ℝ} (hl : (l : ℝ) ≤ v) (hu : v ≤ (u : ℝ))
    (hu1 : u < 1) :
    ((l / (1 - l) : ℚ) : ℝ) ≤ v / (1 - v) ∧ v / (1 - v) ≤ ((u / (1 - u) : ℚ) : ℝ) := by
  have huR : (u : ℝ) < 1 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hu1
    simpa only [Rat.cast_one] using h
  constructor
  · simpa only [Rat.cast_div, Rat.cast_sub, Rat.cast_one] using
      gamma_geometric_ratio_mono hl (hu.trans_lt huR)
  · simpa only [Rat.cast_div, Rat.cast_sub, Rat.cast_one] using gamma_geometric_ratio_mono hu huR

/-- Certified intervals for every actual Gamma node, with upper endpoints
below one, enclose the whole signed exact prime Euler cost. Apply geometric
monotonicity before the coefficient sign selection, then sum the list.
This bounds the actual infinite prime-power sum without an absolute-value loss. -/
theorem gamma_prime_euler_cost_interval {p : ℝ} (r : ℚ → ℚ × ℚ)
    (hr :
      ∀ ab ∈ gammaResolventCoefficients,
        ((r ab.1).1 : ℝ) ≤ p ^ (-(1 / 2 + (ab.1 : ℝ))) ∧
          p ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ ((r ab.1).2 : ℝ))
    (hu : ∀ ab ∈ gammaResolventCoefficients, (r ab.1).2 < 1) :
    (gammaPrimeEulerIntervalLower r : ℝ) ≤ gammaPrimeEulerCost p ∧
      gammaPrimeEulerCost p ≤ (gammaPrimeEulerIntervalUpper r : ℝ) := by
  have hn (ab : ℚ × ℚ) (hab : ab ∈ gammaResolventCoefficients) :=
    gamma_geometric_ratio_interval (hr ab hab).1 (hr ab hab).2 (hu ab hab)
  have hl :=
    List.sum_le_sum
      (fun ab hab ↦ (signed_rational_node_bounds (b := ab.2) (hn ab hab).1 (hn ab hab).2).1)
  have hh :=
    List.sum_le_sum
      (fun ab hab ↦ (signed_rational_node_bounds (b := ab.2) (hn ab hab).1 (hn ab hab).2).2)
  norm_num only [gammaPrimeEulerIntervalLower, gammaPrimeEulerIntervalUpper, gammaPrimeEulerCost,
    Rat.cast_list_sum, List.map_map, Function.comp_def]
  exact ⟨hl, hh⟩

/-- The executable prime Euler interval check combines the existing
twentieth-power node certificate with strict upper endpoint bounds.
A true result permits sound evaluation of every geometric denominator. -/
def gammaPrimeEulerIntervalCheck (p : ℚ) (r : ℚ → ℚ × ℚ) : Bool :=
  gammaFiniteEulerRatioCheck p r &&
    decide (gammaResolventCoefficients.Forall (fun ab ↦ (r ab.1).2 < 1))

/-- A true prime Euler interval check encloses the exact signed cost.
Use the existing real-power certificate and the strict endpoint checks.
No finite prime-power truncation or numerical special-function oracle is assumed. -/
theorem gamma_prime_euler_interval_check_sound {p : ℚ} {r : ℚ → ℚ × ℚ}
    (hc : gammaPrimeEulerIntervalCheck p r = true) :
    (gammaPrimeEulerIntervalLower r : ℝ) ≤ gammaPrimeEulerCost p ∧
      gammaPrimeEulerCost p ≤ (gammaPrimeEulerIntervalUpper r : ℝ) := by
  obtain ⟨hp, hu⟩ := Bool.and_eq_true_iff.mp hc
  have hu' := of_decide_eq_true hu
  exact
    gamma_prime_euler_cost_interval r (gamma_finite_ratio_check_sound hp)
      (fun ab hab ↦ List.forall_iff_forall_mem.mp hu' ab hab)

end PseudoPrime.Analysis
