/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerLogCaps
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerPrefixBound

/-! # Certified Chebyshev boundary at the Euler-center cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At the fixed cutoff, the Mangoldt sum splits into primes and higher
prime powers. All other terms vanish. This is the arithmetic support
identity needed to reuse the numerical Euler rows for Chebyshev psi. -/
theorem center50000_mangoldt_split :
    (∑ n ∈ Finset.Ioc 0 50000, ArithmeticFunction.vonMangoldt n) =
      (∑ n ∈ (Finset.Ioc 0 50000).filter Nat.Prime, ArithmeticFunction.vonMangoldt n) +
        ∑ n ∈ (Finset.Ioc 0 50000).filter (fun n ↦ IsPrimePow n ∧ ¬n.Prime),
          ArithmeticFunction.vonMangoldt n := by
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · simp only [hp, not_true_eq_false, and_false, ite_false, ite_true, add_zero]
  · by_cases hpow : IsPrimePow n
    · simp only [hp, hpow, not_false_eq_true, and_self, ite_true, ite_false, zero_add]
    · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow]
      simp only [hp, hpow, false_and, ite_false, add_zero]

/-- Chebyshev psi at the fixed cutoff equals its actual finite Mangoldt sum.
The natural floor is exact because the cutoff is a natural numeral. -/
theorem center50000_psi_eq_sum :
    Chebyshev.psi 50000 = ∑ n ∈ Finset.Ioc 0 50000, ArithmeticFunction.vonMangoldt n := by
  simp only [Chebyshev.psi, Nat.floor_ofNat]

/-- The exact prime and higher-power support identifies Chebyshev psi
with the numerical rows. Map the certified permutation to Mangoldt values,
then use distinctness to transfer finite-set sums to list sums. -/
theorem center50000_psi_rows :
    Chebyshev.psi 50000 =
      (centerRows50000.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum := by
  have hs :=
    (centerRows50000_index_perm.map
        (fun pk ↦ ArithmeticFunction.vonMangoldt (pk.1 ^ (pk.2 + 1)))).sum_eq
  simp only [List.map_map, Function.comp_def, List.map_append, List.sum_append, Nat.zero_add,
    pow_one] at hs
  rw [center50000_psi_eq_sum, center50000_mangoldt_split, ← centerPrimes50000_Ioc,
    higher_payload_sum ArithmeticFunction.vonMangoldt, List.sum_toFinset _ centerPrimes50000_nodup,
    List.sum_toFinset _ centerHigherPowers_nodup]
  exact hs.symm

/-- Unconditionally, Chebyshev psi at 50000 is at least 49985.95.
Combine the exact support identity with the checked logarithm lower caps.
This supplies the sharp positive boundary term for the finite Euler center. -/
theorem center50000_psi_lower : (999719 / 20 : ℝ) ≤ Chebyshev.psi 50000 := by
  rw [center50000_psi_rows]
  have h := (Rat.cast_le (K := ℝ)).mpr centerRows50000_log_lower_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h.trans center50000_rows_mangoldt_lower

end PseudoPrime.PrimeTestBounds.MillerRabin
