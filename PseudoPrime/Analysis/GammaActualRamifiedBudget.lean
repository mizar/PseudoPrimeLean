/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaActualConductorBudget

/-! # Actual ramified prime losses with one input logarithmic budget -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At local value zero, the actual arbitrary-power Euler prefix and
full signed ramp loss are bounded together by log p times A_p. All
positive powers of the character vanish, identifying the ramified cost.
This connects character input to the common local logarithmic budget. -/
theorem gamma_actual_zero_prime_cost_le {f p : ℕ} (χ : DirichletCharacter ℂ f) (hp : p.Prime)
    (hχ : χ p = 0) (K : Finset ℕ) {x : ℝ} (hx : 0 < x) :
    gammaActualPrimeLocalCost χ p K x ≤ Real.log p * gammaRamifiedCombinedCost p x := by
  dsimp only [gammaActualPrimeLocalCost]
  simp only [map_pow, hχ, zero_pow (Nat.succ_ne_zero _), Complex.zero_re, sub_zero, one_mul]
  exact gamma_ramified_actual_prime_cost_le hp K hx

/-- Actual zero-valued local losses over any subset of input prime factors
share one logarithmic budget log n. Combine each Euler and ramp cost before
the dual cap. The same prime set pays for both contributions, giving the
input-independent allowance needed after the square and dyadic absorption. -/
theorem gamma_actual_ramified_joint_cost_le_input_dual_cap {n f : ℕ} (hn : 0 < n) (R : Finset ℕ)
    (hR : R ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ R, χ p = 0)
    (K : ℕ → Finset ℕ) {x μ : ℝ} (hx : 0 < x) (hμ : 0 ≤ μ) :
    (∑ p ∈ R, gammaActualPrimeLocalCost χ p (K p) x) ≤
      μ * Real.log n + ∑ p ∈ R, Real.log p * max (gammaRamifiedCombinedCost p x - μ) 0 := by
  have hpoint :=
    Finset.sum_le_sum
      (fun p hp ↦
        gamma_actual_zero_prime_cost_le χ (Nat.prime_of_mem_primeFactors (hR hp)) (hχ p hp) (K p)
          hx)
  exact
    hpoint.trans
      (ramified_cost_le_dual_cap R (fun p ↦ Real.log p) (fun p ↦ gammaRamifiedCombinedCost p x) hμ
        (fun p hp ↦
          Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors (hR hp)).one_le))
        (gamma_conductor_subset_log_budget hn R hR))

/-- Signed combined ramified allowance: the exact full Euler cost plus
the actual zero-valued local ramp series divided by sqrt x. The negative
cutoff tail is retained. This sharper cost is used in finite numerical
budgets; the count-based allowance is reserved for proving tail support. -/
noncomputable def gammaRamifiedSignedCombinedCost (p : ℕ) (x : ℝ) : ℝ :=
  gammaPrimeEulerCost p +
    ((∑' k : ℕ, exponentialRampLocalCorrection 0 ((p : ℝ) ^ (k + 1) / x) (k + 1)) / Real.sqrt x)

/-- At local value zero, the actual finite Euler prefix and full ramp
loss are bounded by log p times the signed combined allowance. Only the
Euler prefix is enlarged; the ramp series remains exact. This preserves
the numerical margin required by the refined ramified budget. -/
theorem gamma_actual_zero_prime_cost_le_signed {f p : ℕ} (χ : DirichletCharacter ℂ f) (hp : p.Prime)
    (hχ : χ p = 0) (K : Finset ℕ) (x : ℝ) :
    gammaActualPrimeLocalCost χ p K x ≤ Real.log p * gammaRamifiedSignedCombinedCost p x := by
  dsimp only [gammaActualPrimeLocalCost, gammaRamifiedSignedCombinedCost]
  simp only [map_pow, hχ, zero_pow (Nat.succ_ne_zero _), Complex.zero_re, sub_zero, one_mul]
  rw [mul_add]
  exact add_le_add (sum_gammaResolventMangoldtWeight_primePowers_le_cost hp K) le_rfl

/-- At positive scale the signed ramified allowance is at most the
count-based combined allowance. The actual local series is bounded by
its cutoff count. This transfers finite-tail support without weakening
the signed cost used inside the finite numerical sum. -/
theorem gamma_ramified_signed_cost_le_combined {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 0 < x) :
    gammaRamifiedSignedCombinedCost p x ≤ gammaRamifiedCombinedCost p x := by
  exact add_le_add le_rfl (gamma_ramp_zero_series_le_count hp hx)

/-- Actual ramified losses share a single input logarithmic budget with
the signed combined cost. Euler and ramp losses are grouped before the
dual cap; their finite excess preserves the actual ramp series rather
than replacing it by a coarse power count. -/
theorem gamma_actual_ramified_signed_cost_le_input_dual_cap {n f : ℕ} (hn : 0 < n) (R : Finset ℕ)
    (hR : R ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ R, χ p = 0)
    (K : ℕ → Finset ℕ) (x : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) :
    (∑ p ∈ R, gammaActualPrimeLocalCost χ p (K p) x) ≤
      μ * Real.log n + ∑ p ∈ R, Real.log p * max (gammaRamifiedSignedCombinedCost p x - μ) 0 := by
  have hpoint :=
    Finset.sum_le_sum
      (fun p hp ↦
        gamma_actual_zero_prime_cost_le_signed χ (Nat.prime_of_mem_primeFactors (hR hp)) (hχ p hp)
          (K p) x)
  exact
    hpoint.trans
      (ramified_cost_le_dual_cap R (fun p ↦ Real.log p)
        (fun p ↦ gammaRamifiedSignedCombinedCost p x) hμ
        (fun p hp ↦
          Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors (hR hp)).one_le))
        (gamma_conductor_subset_log_budget hn R hR))

end PseudoPrime.Analysis
