/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleConductorPrefixBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TwoPolePrimePowerPrefixSavings

/-! # Prime-power savings within the full Euler prefix through thirteen -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The full Euler prefix through thirteen, minus the prime-two allowance, is at least one.
Retain the six prime lower bounds together with the powers four, eight and nine, and use
nonnegativity for the remaining indices. This improves the effective even-character cost to
87/25 in the conductor-cancelled negative-witness comparison. -/
theorem twoPoleEulerPrefixMass_thirteen_saving_one :
    (1 : ℝ) ≤ twoPoleEulerPrefixMass (Finset.Ioc 0 13) - (1 / 5 : ℝ) * Real.log 2 := by
  have hl9 : (2 : ℝ) ≤ Real.log 9 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_three_gt_d9]
  have hl11 :=
    hl9.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 9) (by norm_num only : (9 : ℝ) ≤ 11))
  have hl13 :=
    hl9.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 9) (by norm_num only : (9 : ℝ) ≤ 13))
  have h11 :=
    AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_ge_rational
      (by norm_num only : Nat.Prime 11) (b := 24) (t := 2) (by norm_num only)
      (by norm_num only [Nat.cast_ofNat]) hl11
  have h13 :=
    AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_ge_rational
      (by norm_num only : Nat.Prime 13) (b := 26) (t := 2) (by norm_num only)
      (by norm_num only [Nat.cast_ofNat]) hl13
  have hs : ({2,3,4,5,7,8,9,11,13} : Finset ℕ) ⊆ Finset.Ioc 0 13 := by decide
  have hsum :=
    Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun n _ _ ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_nonneg (5 / 4) (11 / 4)
          (by norm_num only : (0 : ℝ) ≤ 3 / 4) n)
  rw [Finset.sum_insert (by decide : (2 : ℕ) ∉ {3,4,5,7,8,9,11,13}),
    Finset.sum_insert (by decide : (3 : ℕ) ∉ {4,5,7,8,9,11,13}),
    Finset.sum_insert (by decide : (4 : ℕ) ∉ {5,7,8,9,11,13}),
    Finset.sum_insert (by decide : (5 : ℕ) ∉ {7,8,9,11,13}),
    Finset.sum_insert (by decide : (7 : ℕ) ∉ {8,9,11,13}),
    Finset.sum_insert (by decide : (8 : ℕ) ∉ {9,11,13}),
    Finset.sum_insert (by decide : (9 : ℕ) ∉ {11,13}),
    Finset.sum_insert (by decide : (11 : ℕ) ∉ {13}), Finset.sum_singleton] at hsum
  have h := AnalyticNumberTheory.Arithmetic.pairedEuler_small_prime_lower
  have hp := AnalyticNumberTheory.Arithmetic.pairedEuler_small_power_lower
  dsimp only [twoPoleEulerPrefixMass]
  norm_num only at h11 h13
  linarith only [hsum, h.1, h.2.1, h.2.2.1, h.2.2.2, h11, h13, hp.1, hp.2.1, hp.2.2,
    Real.log_two_lt_d9]

end PseudoPrime.LLS
