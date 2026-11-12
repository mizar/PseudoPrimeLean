/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerCutoffRows
public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerLogRowsBridge
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevIntervalPrefix

/-! # Certified Euler-row interval sums for Chebyshev psi -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `a ≤ b ≤ 50000`, filtering the checked cutoff rows at `a` gives the
exact interval sum of every weight supported on prime powers. The proof restricts
the established prefix support identity, so no new numerical enumeration is needed. -/
private theorem centerRows_interval_sum (f : ℕ → ℝ) (hf : ∀ n, ¬IsPrimePow n → f n = 0) {a b : ℕ}
    (hb : b ≤ 50000) :
    (∑ n ∈ Finset.Ioc a b, f n) =
      (((centerRowsBelow b).filter (fun r ↦ a < r.p ^ (r.k + 1))).map
          (fun r ↦ f (r.p ^ (r.k + 1)))).sum := by
  have hioc : (Finset.Ioc 0 b).filter (fun n ↦ a < n) = Finset.Ioc a b := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨_, hn⟩, ha⟩
      exact ⟨ha, hn⟩
    · rintro ⟨ha, hn⟩
      exact ⟨⟨Nat.zero_lt_of_lt ha, hn⟩, ha⟩
  have hz : ∀ n, ¬IsPrimePow n → (if a < n then f n else 0) = 0 := by
    intro n hn
    split
    · exact hf n hn
    · rfl
  rw [← hioc, Finset.sum_filter, centerRowsBelow_sum _ hz hb]
  simp only [List.sum_map_ite, List.map_const', List.sum_replicate, smul_zero, add_zero]

/-- Checked Euler rows through 50000 extend both bounds on a psi prefix.
The filtered row list has exact Mangoldt support by `centerRows_interval_sum`;
its checks follow from the certified cutoff rows without rechecking the data. -/
private theorem psi_prefix_from_center_rows {a b : ℕ} {L U : ℝ} (hab : a ≤ b) (hb : b ≤ 50000)
    (hL : L ≤ Chebyshev.psi a) (hU : Chebyshev.psi a ≤ U) :
    L + (((centerRowsBelow b).filter (fun r ↦ a < r.p ^ (r.k + 1))).map (fun r ↦ (r.lo : ℝ))).sum ≤
        Chebyshev.psi b ∧
      Chebyshev.psi b ≤
        U +
          (((centerRowsBelow b).filter (fun r ↦ a < r.p ^ (r.k + 1))).map
              (fun r ↦ (r.hi : ℝ))).sum := by
  apply psi_prefix_of_euler_rows hab hL hU
  · apply List.all_eq_true.mpr
    intro r hr
    exact List.all_eq_true.mp (centerRowsBelow_check b) r (List.mem_filter.mp hr).1
  · apply centerRows_interval_sum _ _ hb
    intro n hn
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn

private theorem row_sum_103_107_upper :
    (((centerRowsBelow 107).filter (fun r ↦ 103 < r.p ^ (r.k + 1))).map (fun r ↦ r.hi)).sum ≤
      (4673 / 1000 : ℚ) := by
  decide +kernel

/-- The increment of `psi` from 103 to 107 is at most 4.673. This concrete
bound uses the certified Euler rows and their exact prime-power support. -/
theorem psi_107_le_psi_103_add : Chebyshev.psi 107 ≤ Chebyshev.psi 103 + (4673 / 1000 : ℝ) := by
  have h :=
    (psi_prefix_from_center_rows (a := 103) (b := 107) (L := Chebyshev.psi 103) (U :=
        Chebyshev.psi 103) (by decide) (by decide) le_rfl le_rfl).2
  have hc :
    (((((centerRowsBelow 107).filter (fun r ↦ 103 < r.p ^ (r.k + 1))).map (fun r ↦ r.hi)).sum : ℚ) :
        ℝ) ≤
      ((4673 / 1000 : ℚ) : ℝ) := by
    exact_mod_cast row_sum_103_107_upper
  have hsum :
    (((centerRowsBelow 107).filter (fun r ↦ 103 < r.p ^ (r.k + 1))).map (fun r ↦ (r.hi : ℝ))).sum ≤
      (4673 / 1000 : ℝ) := by
    simpa only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_div,
      Rat.cast_ofNat] using hc
  exact h.trans (add_le_add_right hsum _)

/-- Filtering the checked Euler rows to prime values gives exactly the prime
logarithm sum on any interval ending at or below 50000. -/
private theorem centerRows_prime_interval_sum {a b : ℕ} (hb : b ≤ 50000) :
    (∑ n ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log n) =
      ((((centerRowsBelow b).filter (fun r ↦ a < r.p ^ (r.k + 1))).filter
              (fun r ↦ Nat.Prime (r.p ^ (r.k + 1)))).map
          (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum := by
  classical
  have hz :
    ∀ n, ¬IsPrimePow n → (if Nat.Prime n then ArithmeticFunction.vonMangoldt n else 0) = 0 := by
    intro n hn
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
    split <;> rfl
  have h :=
    centerRows_interval_sum (a := a)
      (fun n ↦ if Nat.Prime n then ArithmeticFunction.vonMangoldt n else 0) hz hb
  simp only [List.sum_map_ite, List.map_const', List.sum_replicate, smul_zero, add_zero] at h
  rw [Finset.sum_filter]
  convert h using 1
  apply Finset.sum_congr rfl
  intro n hn
  split
  · rename_i hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  · rfl

/-- Checked prime rows extend both sides of a theta prefix estimate through 50000. -/
private theorem theta_prefix_from_center_rows {a b : ℕ} {L U : ℝ} (hab : a ≤ b) (hb : b ≤ 50000)
    (hL : L ≤ Chebyshev.theta a) (hU : Chebyshev.theta a ≤ U) :
    L +
          (((((centerRowsBelow b).filter (fun r ↦ a < r.p ^ (r.k + 1))).filter
                  (fun r ↦ Nat.Prime (r.p ^ (r.k + 1)))).map
              (fun r ↦ (r.lo : ℝ))).sum) ≤
        Chebyshev.theta b ∧
      Chebyshev.theta b ≤
        U +
          (((((centerRowsBelow b).filter (fun r ↦ a < r.p ^ (r.k + 1))).filter
                  (fun r ↦ Nat.Prime (r.p ^ (r.k + 1)))).map
              (fun r ↦ (r.hi : ℝ))).sum) := by
  classical
  have hrows :
    (((centerRowsBelow b).filter (fun r ↦ a < r.p ^ (r.k + 1))).filter
            (fun r ↦ Nat.Prime (r.p ^ (r.k + 1)))).all
        eulerCenterRowCheck =
      true := by
    apply List.all_eq_true.mpr
    intro r hr
    exact
      List.all_eq_true.mp (centerRowsBelow_check b) r
        (List.mem_filter.mp (List.mem_filter.mp hr).1).1
  have h := euler_log_rows_bounds _ hrows
  apply AnalyticNumberTheory.Arithmetic.theta_prefix_bounds_of_interval hab hL hU
  · rw [centerRows_prime_interval_sum hb]
    exact h.1
  · rw [centerRows_prime_interval_sum hb]
    exact h.2

private theorem prime_row_sum_103_107_upper :
    (((((centerRowsBelow 107).filter (fun r ↦ 103 < r.p ^ (r.k + 1))).filter
              (fun r ↦ Nat.Prime (r.p ^ (r.k + 1)))).map
          (fun r ↦ r.hi)).sum) ≤
      (4673 / 1000 : ℚ) := by
  decide +kernel

/-- The prime-logarithm increment of `theta` from 103 to 107 is at most 4.673.
The prime rows and their rational bounds are checked against the shared Euler data. -/
theorem theta_107_le_theta_103_add :
    Chebyshev.theta 107 ≤ Chebyshev.theta 103 + (4673 / 1000 : ℝ) := by
  have h :=
    (theta_prefix_from_center_rows (a := 103) (b := 107) (L := Chebyshev.theta 103) (U :=
        Chebyshev.theta 103) (by decide) (by decide) le_rfl le_rfl).2
  have hc :
    ((((((centerRowsBelow 107).filter (fun r ↦ 103 < r.p ^ (r.k + 1))).filter
                  (fun r ↦ Nat.Prime (r.p ^ (r.k + 1)))).map
              (fun r ↦ r.hi)).sum :
          ℚ) :
        ℝ) ≤
      ((4673 / 1000 : ℚ) : ℝ) := by
    exact_mod_cast prime_row_sum_103_107_upper
  have hsum :
    (((((centerRowsBelow 107).filter (fun r ↦ 103 < r.p ^ (r.k + 1))).filter
              (fun r ↦ Nat.Prime (r.p ^ (r.k + 1)))).map
          (fun r ↦ (r.hi : ℝ))).sum) ≤
      (4673 / 1000 : ℝ) := by
    simpa only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_div,
      Rat.cast_ofNat] using hc
  exact h.trans (add_le_add_right hsum _)

end PseudoPrime.PrimeTestBounds.MillerRabin
