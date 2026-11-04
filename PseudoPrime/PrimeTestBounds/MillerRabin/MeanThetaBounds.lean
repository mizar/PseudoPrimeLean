/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RelativeChebyshevBounds

/-! # Theta budgets for average-logarithm Miller–Rabin counting

Three rational relative-width certificates provide the endpoint and terminal-interval
theta bounds needed for the planned fixed-coefficient prime-product argument.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH and `B ≥ 52000 ^ 2`, theta has the displayed endpoint bounds and
lower bound on `[B / 16, B]`. Apply the relative-width estimates with rational widths
and verify their budgets. This supplies the first average-logarithm counting cell. -/
theorem mean_theta_cell_one (hRH : RiemannHypothesis) {B : ℕ} (hB : 52000 ^ 2 ≤ B) :
    (9968 / 10000 : ℝ) * B ≤ Chebyshev.theta B ∧
      (∀ t ∈ Set.Icc ((B : ℝ) / 16) B, (993 / 1000 : ℝ) * t ≤ Chebyshev.theta t) ∧
      Chebyshev.theta B ≤ (10029 / 10000 : ℝ) * B := by
  have hBr : (52000 : ℝ) ^ 2 ≤ B := by exact_mod_cast hB
  have hlo :=
    LLS.theta_lower_of_relative_budget hRH (h := 1 / 684) (r := 52000) (η := 9968 / 10000)
      (by norm_num only) (by norm_num only) (by norm_num only) hBr (by norm_num only)
  have hhi :=
    LLS.theta_upper_of_relative_budget hRH (h := 1 / 684) (r := 52000) (P := 10029 / 10000)
      (by norm_num only) (by norm_num only) hBr (by norm_num only)
  refine ⟨hlo, ?_, hhi⟩
  intro t ht
  have ht0 : (13000 : ℝ) ^ 2 ≤ t := by nlinarith only [hBr, ht.1]
  exact
    LLS.theta_lower_of_relative_budget hRH (h := 1 / 342) (r := 13000) (η := 993 / 1000)
      (by norm_num only) (by norm_num only) (by norm_num only) ht0 (by norm_num only)

/-- Under RH and `B ≥ 650000 ^ 2`, theta has the displayed endpoint bounds and
lower bound on `[B / 16, B]`. Rational relative-width budgets certify the bounds.
This supplies the second average-logarithm counting cell. -/
theorem mean_theta_cell_two (hRH : RiemannHypothesis) {B : ℕ} (hB : 650000 ^ 2 ≤ B) :
    (9991 / 10000 : ℝ) * B ≤ Chebyshev.theta B ∧
      (∀ t ∈ Set.Icc ((B : ℝ) / 16) B, (9983 / 10000 : ℝ) * t ≤ Chebyshev.theta t) ∧
      Chebyshev.theta B ≤ (10008 / 10000 : ℝ) * B := by
  have hBr : (650000 : ℝ) ^ 2 ≤ B := by exact_mod_cast hB
  have hlo :=
    LLS.theta_lower_of_relative_budget hRH (h := 1 / 2418) (r := 650000) (η := 9991 / 10000)
      (by norm_num only) (by norm_num only) (by norm_num only) hBr (by norm_num only)
  have hhi :=
    LLS.theta_upper_of_relative_budget hRH (h := 1 / 2418) (r := 650000) (P := 10008 / 10000)
      (by norm_num only) (by norm_num only) hBr (by norm_num only)
  refine ⟨hlo, ?_, hhi⟩
  intro t ht
  have ht0 : (162500 : ℝ) ^ 2 ≤ t := by nlinarith only [hBr, ht.1]
  exact
    LLS.theta_lower_of_relative_budget hRH (h := 1 / 1209) (r := 162500) (η := 9983 / 10000)
      (by norm_num only) (by norm_num only) (by norm_num only) ht0 (by norm_num only)

/-- Under RH and `B ≥ 65000000 ^ 2`, theta has the displayed endpoint bounds and
lower bound on `[B / 16, B]`. Rational relative-width budgets certify the bounds.
This supplies the third average-logarithm counting cell. -/
theorem mean_theta_cell_three (hRH : RiemannHypothesis) {B : ℕ} (hB : 65000000 ^ 2 ≤ B) :
    (99992 / 100000 : ℝ) * B ≤ Chebyshev.theta B ∧
      (∀ t ∈ Set.Icc ((B : ℝ) / 16) B, (99984 / 100000 : ℝ) * t ≤ Chebyshev.theta t) ∧
      Chebyshev.theta B ≤ (100008 / 100000 : ℝ) * B := by
  have hBr : (65000000 : ℝ) ^ 2 ≤ B := by exact_mod_cast hB
  have hlo :=
    LLS.theta_lower_of_relative_budget hRH (h := 1 / 24186) (r := 65000000) (η := 99992 / 100000)
      (by norm_num only) (by norm_num only) (by norm_num only) hBr (by norm_num only)
  have hhi :=
    LLS.theta_upper_of_relative_budget hRH (h := 1 / 24186) (r := 65000000) (P := 100008 / 100000)
      (by norm_num only) (by norm_num only) hBr (by norm_num only)
  refine ⟨hlo, ?_, hhi⟩
  intro t ht
  have ht0 : (16250000 : ℝ) ^ 2 ≤ t := by nlinarith only [hBr, ht.1]
  exact
    LLS.theta_lower_of_relative_budget hRH (h := 1 / 12093) (r := 16250000) (η := 99984 / 100000)
      (by norm_num only) (by norm_num only) (by norm_num only) ht0 (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
