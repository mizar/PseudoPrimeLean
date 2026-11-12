/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterSensitiveExclusion
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLinearBound

/-! # Character-defect bounds with the global Chebyshev estimate -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For nonzero `m`, weights in `[0, 1/3]` and prime triviality outside `m`, the weighted
character defect is at most the excluded-prime cost plus `37 sqrt(x)/25` for `x ≥ 1`.
Split prime and nonprime terms and apply the unconditional sharp prime-power estimate. -/
theorem weighted_defect_le_excluded_sharp {f m : ℕ} (χ : DirichletCharacter ℂ f) (hm : m ≠ 0)
    {x : ℝ} (hx : 1 ≤ x) (w : ℕ → ℝ) (hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, 0 ≤ w n ∧ w n ≤ 1 / 3)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → ¬p ∣ m → χ p = 1) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * w n) ≤
      (2 / 3 : ℝ) * (∑ p ∈ m.primeFactors, Real.log p) + (37 / 25 : ℝ) * Real.sqrt x := by
  have hp := prime_character_defect_le_excluded χ hm (zero_le_one.trans hx) w hw hsmall
  have hc :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime),
        (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * w n) ≤
      (37 / 25 : ℝ) * Real.sqrt x := by
    apply
      le_trans
        (Finset.sum_le_sum
          (fun n hn ↦ mangoldt_character_defect_term_le χ n (hw n (Finset.mem_filter.mp hn).1).1))
    exact composite_weight_le_37_25_sqrt hx w (fun n hn ↦ (hw n hn).2)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊x⌋₊) Nat.Prime]
  exact add_le_add hp hc

/-- Under the same weight and prime-triviality assumptions, retain the character-sensitive
excluded-prime cost and bound the nonprime contribution by `37 sqrt(x)/25`.
The estimate is unconditional and is suitable for the cubic conductor budget. -/
theorem weighted_defect_le_sensitive_sharp {f m : ℕ} (χ : DirichletCharacter ℂ f) (hm : m ≠ 0)
    {x : ℝ} (hx : 1 ≤ x) (w : ℕ → ℝ) (hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, 0 ≤ w n ∧ w n ≤ 1 / 3)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → ¬p ∣ m → χ p = 1) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * w n) ≤
      characterExclusionCost χ m / 3 + (37 / 25 : ℝ) * Real.sqrt x := by
  have hp :=
    prime_character_defect_le_sensitive χ hm (zero_le_one.trans hx) w (fun n hn ↦ (hw n hn).2)
      hsmall
  have hc :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime),
        (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * w n) ≤
      (37 / 25 : ℝ) * Real.sqrt x := by
    apply
      le_trans
        (Finset.sum_le_sum
          (fun n hn ↦ mangoldt_character_defect_term_le χ n (hw n (Finset.mem_filter.mp hn).1).1))
    exact composite_weight_le_37_25_sqrt hx w (fun n hn ↦ (hw n hn).2)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊x⌋₊) Nat.Prime]
  exact add_le_add hp hc

end PseudoPrime.AnalyticNumberTheory.Arithmetic
