/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64DyadicLocalBounds
public import PseudoPrime.Analysis.GammaActualRamifiedBudget

/-! # Signed ramified costs with one logarithmic input budget -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: any signed node list, a prime base and a scale. Output: the full
signed Euler progression cost plus the exact zero-valued ramp series. The negative
ramp tail is retained for finite numerical budgets, unlike a power-count envelope. -/
noncomputable def finiteSignedRamifiedCost (l : List (ℚ × ℚ)) (p : ℕ) (x : ℝ) : ℝ :=
  finiteSignedPrimeProgressionCost l p 1 1 +
    ((∑' k : ℕ, exponentialRampLocalCorrection 0 ((p : ℝ) ^ (k + 1) / x) (k + 1)) / Real.sqrt x)

/-- For a prime with character value zero and a node list with positive
exponents and nonnegative combined Euler weight, every finite positive-power
prefix is bounded by log p times the signed ramified cost. Only the Euler prefix
is enlarged; the ramp remains exact. No positive-scale hypothesis is required. -/
theorem finiteSigned_actual_zero_prime_cost_le (l : List (ℚ × ℚ))
    (ha : ∀ ab ∈ l, 0 < (1 / 2 : ℝ) + (ab.1 : ℝ))
    (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ finiteSignedEulerWeight l u) {f p : ℕ} (χ : DirichletCharacter ℂ f)
    (hp : p.Prime) (hχ : χ p = 0) (K : Finset ℕ) (x : ℝ) :
    finiteSignedActualPrimeLocalCost l χ p K x ≤ Real.log p * finiteSignedRamifiedCost l p x := by
  have he :=
    sum_finiteSignedMangoldtWeight_progression_le_cost l ha hW hp (by norm_num only : 0 < (1 : ℕ))
      (by norm_num only : 0 < (1 : ℕ)) K
  simp only [Nat.one_mul] at he
  dsimp only [finiteSignedActualPrimeLocalCost, finiteSignedRamifiedCost]
  simp only [map_pow, hχ, zero_pow (Nat.succ_ne_zero _), Complex.zero_re, sub_zero, one_mul]
  rw [mul_add]
  exact add_le_add he le_rfl

/-- At a base above one and positive scale, the signed ramified cost is at most
the full Euler cost plus the normalized cutoff count. This transfers coarse tail
support to the signed cost without weakening its finite interior values. -/
theorem finiteSigned_ramified_cost_le_count (l : List (ℚ × ℚ)) {p : ℕ} (hp : 1 < p) {x : ℝ}
    (hx : 0 < x) :
    finiteSignedRamifiedCost l p x ≤
      finiteSignedPrimeProgressionCost l p 1 1 + gammaRampPowerCount p x / Real.sqrt x := by
  exact add_le_add le_rfl (gamma_ramp_zero_series_le_count hp hx)

/-- For selected zero-valued input-prime factors and a nonnegative dual
parameter, the actual local sum is bounded by mu log n plus one weighted positive
excess sum. Euler and ramp terms share the same logarithmic input budget. -/
theorem finiteSigned_ramified_cost_le_input_dual (l : List (ℚ × ℚ))
    (ha : ∀ ab ∈ l, 0 < (1 / 2 : ℝ) + (ab.1 : ℝ))
    (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ finiteSignedEulerWeight l u) {n f : ℕ} (hn : 0 < n) (R : Finset ℕ)
    (hR : R ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ R, χ p = 0)
    (K : ℕ → Finset ℕ) (x : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) :
    (∑ p ∈ R, finiteSignedActualPrimeLocalCost l χ p (K p) x) ≤
      μ * Real.log n + ∑ p ∈ R, Real.log p * max (finiteSignedRamifiedCost l p x - μ) 0 := by
  have hpoint :=
    Finset.sum_le_sum
      (fun p hp ↦
        finiteSigned_actual_zero_prime_cost_le l ha hW χ (Nat.prime_of_mem_primeFactors (hR hp))
          (hχ p hp) (K p) x)
  exact
    hpoint.trans
      (ramified_cost_le_dual_cap R (fun p ↦ Real.log p) (fun p ↦ finiteSignedRamifiedCost l p x) hμ
        (fun p hp ↦ Real.log_natCast_nonneg p) (gamma_conductor_subset_log_budget hn R hR))

/-- For arbitrary real costs on natural bases, a finite set containing every
selected positive excess bounds its weighted sum. Terms outside the set vanish
and all remaining log-weighted positive parts are nonnegative. No primality
hypothesis is needed, so the reduction can be reused for different local models. -/
theorem prime_weighted_positive_excess_le_finite (F : ℕ → ℝ) (μ : ℝ) (R P : Finset ℕ)
    (htail : ∀ p ∈ R, p ∉ P → F p ≤ μ) :
    (∑ p ∈ R, Real.log p * max (F p - μ) 0) ≤ ∑ p ∈ P, Real.log p * max (F p - μ) 0 := by
  let G : ℕ → ℝ := fun p ↦ Real.log p * max (F p - μ) 0
  have he : (∑ p ∈ R ∩ P, G p) = ∑ p ∈ R, G p := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro p hp hnot
    have hpP : p ∉ P := fun h ↦ hnot (Finset.mem_inter.mpr ⟨hp, h⟩)
    dsimp only [G]
    rw [max_eq_right (sub_nonpos.mpr (htail p hp hpP)), mul_zero]
  change (∑ p ∈ R, G p) ≤ ∑ p ∈ P, G p
  rw [← he]
  exact
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun p hp hnot ↦ mul_nonneg (Real.log_natCast_nonneg p) (le_max_right _ _))

end PseudoPrime.Analysis
