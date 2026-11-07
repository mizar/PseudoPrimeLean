/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleSigns
public import PseudoPrime.NumberTheory.QuadraticCharacterConductor
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic.Ring

/-! # Simultaneous evaluation at the three pair levels

Use each Jacobi character at its own level, retaining its values at nonunits
of the full three-factor modulus.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For three nonzero levels with odd pair products, the real parts of the
three pair-level Jacobi characters sum to at least minus one at every integer.
Evaluate at the original levels and apply Jacobi multiplicativity. No unit
assumption is needed; this supplies the simultaneous Euler-tail estimate. -/
theorem pair_character_sum_ge_neg_one (a : ℤ) (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r]
    (hpq : Odd (p * q)) (hpr : Odd (p * r)) (hqr : Odd (q * r)) :
    (-1 : ℝ) ≤
      (NumberTheory.complexJacobiNumeratorCharacter (p * q) hpq a).re +
        (NumberTheory.complexJacobiNumeratorCharacter (p * r) hpr a).re +
        (NumberTheory.complexJacobiNumeratorCharacter (q * r) hqr a).re := by
  rw [NumberTheory.complexJacobiNumeratorCharacter_apply_int,
    NumberTheory.complexJacobiNumeratorCharacter_apply_int,
    NumberTheory.complexJacobiNumeratorCharacter_apply_int]
  exact jacobi_product_sum_ge_neg_one a p q r

/-- For summable common weights and signed contributions, a finite prefix
with contribution minus three times its weight improves the total upper bound
by four times the prefix mass. Outside the prefix assume the simultaneous
pointwise upper bound. Apply the finite-sum lower bound to the difference;
this is the summation step in the coupled Euler estimate. -/
theorem coupled_euler_prefix_bound (s : Finset ℕ) (w e : ℕ → ℝ) (hw : Summable w) (he : Summable e)
    (ht : ∀ j ∉ s, e j ≤ w j) (hp : ∀ j ∈ s, e j = -3 * w j) :
    (∑' j, e j) ≤ (∑' j, w j) - 4 * ∑ j ∈ s, w j := by
  have h := (hw.sub he).sum_le_tsum s (fun j hj ↦ sub_nonneg.mpr (ht j hj))
  have hsum : (∑ j ∈ s, (w j - e j)) = 4 * ∑ j ∈ s, w j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hp j hj]
    ring
  rw [hsum, hw.tsum_sub he] at h
  linarith only [h]

/-- A finite prefix sum equal to minus three times its mass suffices for the
fourfold Euler saving. Summable contributions bounded by the weight outside
the prefix give the total estimate by summing their difference. This permits
weighted prefix identities that leave zero-weight indices unrestricted. -/
theorem coupled_euler_prefix_sum_bound (s : Finset ℕ) (w e : ℕ → ℝ) (hw : Summable w)
    (he : Summable e) (ht : ∀ j ∉ s, e j ≤ w j) (hp : (∑ j ∈ s, e j) = -3 * ∑ j ∈ s, w j) :
    (∑' j, e j) ≤ (∑' j, w j) - 4 * ∑ j ∈ s, w j := by
  have h := (hw.sub he).sum_le_tsum s (fun j hj ↦ sub_nonneg.mpr (ht j hj))
  rw [Finset.sum_sub_distrib, hp, hw.tsum_sub he] at h
  linarith only [h]

/-- For a nonnegative summable kernel and three summable weighted sequences,
a simultaneous sign lower bound and prefix sum three give four times the
prefix below the combined principal and character sums. Apply the finite
prefix bound to the nonnegative combined series. This is the summation
step of the three-character main-term inequality. -/
theorem three_character_main_prefix_le (s : Finset ℕ) (w a b c : ℕ → ℝ) (hw : Summable w)
    (ha : Summable (fun n ↦ a n * w n)) (hb : Summable (fun n ↦ b n * w n))
    (hc : Summable (fun n ↦ c n * w n)) (hn : ∀ n, 0 ≤ w n) (ht : ∀ n, -1 ≤ a n + b n + c n)
    (hp : ∀ n ∈ s, a n + b n + c n = 3) :
    4 * ∑ n ∈ s, w n ≤ (∑' n, (w n + a n * w n + b n * w n + c n * w n)) := by
  have h :=
    (((hw.add ha).add hb).add hc).sum_le_tsum s
      (fun n _ ↦ by
        have hh := mul_le_mul_of_nonneg_right (ht n) (hn n)
        linarith only [hh])
  have he : (∑ n ∈ s, (w n + a n * w n + b n * w n + c n * w n)) = 4 * ∑ n ∈ s, w n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hns
    have hh := congrArg (fun t : ℝ ↦ t * w n) (hp n hns)
    linarith only [hh]
  rw [he] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
