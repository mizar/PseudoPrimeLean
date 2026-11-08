/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine43Count
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeTable

/-! # Refined fourteen-prime supply for semiprime cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the refined fourteen-prime table gives a 0.28 witness for a
distinct semiprime when the weighted budget and count fit the target radius.
The generic table theorem transfers the certified count to the local kernel. -/
theorem target028_fine43_core {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (12451 / 1000 : ℝ) ≤ Real.log n) (H : ℕ) (hH : H ≤ 140) (D : ℝ)
    (hD : D ≤ Real.log (target028Fine43Row.getD H 0 : ℝ))
    (hbudget : (H : ℝ) / 20 ≤ (52915 / 100000 : ℝ) * Real.log n)
    (hmargin : (1 - 52915 / 100000 : ℝ) * Real.log n ≤ D) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hs : max ((H : ℝ) / 20) (Real.log n - D) ≤ (52915 / 100000 : ℝ) * Real.log n := by
    apply max_le hbudget
    linarith only [hmargin]
  have hs0 : 0 ≤ max ((H : ℝ) / 20) (Real.log n - D) :=
    le_trans (div_nonneg (Nat.cast_nonneg H) (by norm_num only)) (le_max_left _ _)
  have hsquare := mul_self_le_mul_self hs0 hs
  have hlocal :
    localFullEnvelope (max ((H : ℝ) / 20) (Real.log n - D)) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by
    exact
      (min_le_left _ _).trans
        ((min_le_left _ _).trans (by nlinarith only [hsquare, sq_nonneg (Real.log n)]))
  have hB : (43 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH target028FourteenPrimes
      target028Fine43Weights 43 H 140 target028Fine43Weight 20 (by norm_num only)
      target028_fine43_labels.1 (fun r hr ↦ (target028_fine43_supply r hr).1)
      (fun r hr ↦ (target028_fine43_supply r hr).2.1) target028_fine43_labels.2.2
      (fun r hr ↦ (target028_fine43_supply r hr).2.2) target028_fine43_labels.2.1 hH
      target028Fine43Row target028Fine43Tail target028_fine43_checked hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
