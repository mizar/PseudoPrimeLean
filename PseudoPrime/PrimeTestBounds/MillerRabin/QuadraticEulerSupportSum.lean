/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerPrefixBound

/-! # Reusing the exact cutoff support for other Mangoldt weights -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At the certified cutoff, any real function vanishing outside prime
powers splits into prime and higher-power contributions. This supports
reuse of the same finite payload with other Mangoldt weights. -/
theorem center50000_weight_split (f : ℕ → ℝ) (hf : ∀ n, ¬IsPrimePow n → f n = 0) :
    (∑ n ∈ Finset.Ioc 0 50000, f n) =
      (∑ n ∈ (Finset.Ioc 0 50000).filter Nat.Prime, f n) +
        ∑ n ∈ (Finset.Ioc 0 50000).filter (fun n ↦ IsPrimePow n ∧ ¬n.Prime), f n := by
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · simp only [hp, not_true_eq_false, and_false, ite_false, ite_true, add_zero]
  · by_cases hpow : IsPrimePow n
    · simp only [hp, hpow, not_false_eq_true, and_self, ite_true, ite_false, zero_add]
    · rw [hf n hpow]
      simp only [hp, hpow, false_and, ite_false, add_zero]

/-- The certified numerical rows give the exact sum at 50000 for any
real weight supported on prime powers. Transfer the support permutation
and distinctness independently of the numerical endpoint data. -/
theorem center50000_weight_rows (f : ℕ → ℝ) (hf : ∀ n, ¬IsPrimePow n → f n = 0) :
    (∑ n ∈ Finset.Ioc 0 50000, f n) = (centerRows50000.map (fun r ↦ f (r.p ^ (r.k + 1)))).sum := by
  have hs := (centerRows50000_index_perm.map (fun pk ↦ f (pk.1 ^ (pk.2 + 1)))).sum_eq
  simp only [List.map_map, Function.comp_def, List.map_append, List.sum_append, Nat.zero_add,
    pow_one] at hs
  rw [center50000_weight_split f hf, ← centerPrimes50000_Ioc, higher_payload_sum f,
    List.sum_toFinset _ centerPrimes50000_nodup, List.sum_toFinset _ centerHigherPowers_nodup]
  exact hs.symm

end PseudoPrime.PrimeTestBounds.MillerRabin
