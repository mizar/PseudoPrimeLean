/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaFiniteEulerIntervals

/-! # Separate prime and composite-prime-power Euler contributions -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The actual finite Euler prefix splits into primes and composite prime
powers. Mangoldt vanishing removes all remaining indices. This allows a
prime-list certificate and a separate small higher-power payload to be
verified independently before adding their weighted sums. -/
theorem gamma_prefix_split_primes (B : ℕ) :
    (∑ n ∈ Finset.Ioc 0 B, Analysis.gammaResolventMangoldtWeight n) =
      (∑ n ∈ (Finset.Ioc 0 B).filter Nat.Prime, Analysis.gammaResolventMangoldtWeight n) +
        ∑ n ∈ (Finset.Ioc 0 B).filter (fun n ↦ IsPrimePow n ∧ ¬n.Prime),
          Analysis.gammaResolventMangoldtWeight n := by
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · simp only [hp, not_true_eq_false, and_false, ite_false, ite_true, add_zero]
  · by_cases hpow : IsPrimePow n
    · simp only [hp, hpow, not_false_eq_true, and_self, ite_true, ite_false, zero_add]
    · rw [Analysis.gammaResolventMangoldtWeight,
        ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow, zero_mul]
      simp only [hp, hpow, false_and, ite_false, add_zero]

/-- Fast-decision prime lists on any natural interval represent the exact
mathematical prime finset. Membership and decision soundness transfer the
computed list without evaluating the default slow decision. This bridges
each certified prime block to the actual weighted finite sum. -/
theorem fast_prime_list_finset (start len : ℕ) :
    ((List.range' start len).filter (fun n ↦ @decide n.Prime (Nat.decidablePrime' n))).toFinset =
      (Finset.Ico start (start + len)).filter Nat.Prime := by
  ext n
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range'_1, decide_eq_true_eq,
    Finset.mem_filter, Finset.mem_Ico]

end PseudoPrime.PrimeTestBounds.MillerRabin
