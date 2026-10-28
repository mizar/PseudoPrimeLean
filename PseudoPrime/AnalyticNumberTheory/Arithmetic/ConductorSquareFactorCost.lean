/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.JacobiSquareFactorBudget
public import PseudoPrime.LLS.FiniteExcludedTaperSavings

/-! # Exclusion costs with coupled conductor and square-factor rates -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For odd n, nonnegative x and a weight supported on prime powers, the
structural budget at 4n is the local cost at two plus the costs at prime divisors
of n. Reindex the exact prime-factor budget and use oddness to avoid duplication.
This isolates the two-adic cost before applying input-size rates. -/
theorem quadraticExcludedBudget_four_mul_eq_two_add {n : ℕ} (hn : Odd n) (q : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (w : ℕ → ℝ) (hw : ∀ m : ℕ, ¬IsPrimePow m → w m = 0) :
    quadraticExcludedBudget q (4 * n) (Finset.Ioc 0 ⌊x⌋₊) w =
      quadraticExcludedPrimeCost q x w 2 +
        ∑ p ∈ n.primeFactors, quadraticExcludedPrimeCost q x w p := by
  have hN : 4 * n ≠ 0 := Nat.mul_ne_zero (by norm_num only) hn.pos.ne'
  rw [quadraticExcludedBudget_eq_sum_primeFactors hN q hx w hw,
    Nat.primeFactors_mul (by norm_num only : (4 : ℕ) ≠ 0) hn.pos.ne']
  have h4 : (4 : ℕ).primeFactors = {2} := by
    simpa only [show (2 : ℕ) ^ 2 = 4 by norm_num only] using
      Nat.primeFactors_prime_pow (by norm_num only : (2 : ℕ) ≠ 0) Nat.prime_two
  have hnotdvd : ¬2 ∣ n :=
    Nat.prime_two.coprime_iff_not_dvd.mp (Nat.coprime_comm.mpr hn.coprime_two_right)
  have hnot : 2 ∉ n.primeFactors := fun h ↦
    hnotdvd ((Nat.mem_primeFactors_of_ne_zero hn.pos.ne').mp h).2
  rw [h4, Finset.singleton_union, Finset.sum_insert hnot]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
