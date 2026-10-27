/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalSliceDescent
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-! # Integer power cutoffs for rational quotient induction -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For positive rational families of heights Q,D and positive divisor indices, transfer an
n-th-power quotient bound from heights Q/r,D/s to the slice product, retaining a factor r*s.
Scale both slices, preserve cardinalities and bound their quotient set by the original one.
This is the powered form of height descent used in the induction. -/
theorem slice_power_mul_indices_le_of_recursive_bound {A B : Finset ℚ} {Q D r s M n : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) (hr : 0 < r) (hs : 0 < s)
    (hrec :
      ∀ A' B' : Finset ℚ,
        (∀ q ∈ A', 0 < q ∧ q.num.natAbs ≤ Q / r ∧ q.den ≤ D / s) →
          (∀ q ∈ B', 0 < q ∧ q.num.natAbs ≤ Q / r ∧ q.den ≤ D / s) →
          (A'.card * B'.card) ^ n ≤
            M * ((Q / r) * (D / s)) * (rationalQuotientSet A' B').card ^ n) :
    ((divisorSlice A r s).card * (divisorSlice B r s).card) ^ n * (r * s) ≤
      M * (Q * D) * (rationalQuotientSet A B).card ^ n := by
  classical
  have hc : (s : ℚ) / r ≠ 0 := ne_of_gt (div_pos (Nat.cast_pos.mpr hs) (Nat.cast_pos.mpr hr))
  have ht :=
    hrec ((divisorSlice A r s).image (fun q ↦ (s : ℚ) / r * q))
      ((divisorSlice B r s).image (fun q ↦ (s : ℚ) / r * q)) (scaled_slice_family_height hA hr hs)
      (scaled_slice_family_height hB hr hs)
  rw [card_scaled_family _ hc, card_scaled_family _ hc] at ht
  have hcard := Finset.card_le_card (scaled_slice_quotientSet_subset A B hr hs)
  have hp := Nat.mul_le_mul_left (M * ((Q / r) * (D / s))) (Nat.pow_le_pow_left hcard n)
  have hh := Nat.mul_le_mul (Nat.div_mul_le_self Q r) (Nat.div_mul_le_self D s)
  have h1 := Nat.mul_le_mul_right (r * s) (ht.trans hp)
  have h2 := Nat.mul_le_mul_left (M * (rationalQuotientSet A B).card ^ n) hh
  nlinarith only [h1, h2]

/-- For natural nonnegative counts and positive n,x, a powered count weighted by an index
at least x is at most M*U*R^n. If M*U is at most x^(n+1), the count is at most x*R.
Cancel the positive cutoff and use monotonicity of natural powers. -/
theorem product_le_of_powered_index_budget {a R M U x r n : ℕ} (hx : 0 < x) (hn : 0 < n)
    (hxr : x ≤ r) (ha : a ^ n * r ≤ M * U * R ^ n) (hxpow : M * U ≤ x ^ (n + 1)) : a ≤ x * R := by
  apply (Nat.pow_le_pow_iff_left (ne_of_gt hn)).mp
  have ht := (Nat.mul_le_mul_left (a ^ n) hxr).trans ha
  have hu := Nat.mul_le_mul_right (R ^ n) hxpow
  have hc : a ^ n * x ≤ (x * R) ^ n * x := by
    simpa only [pow_succ, mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ht.trans hu
  exact Nat.le_of_mul_le_mul_right hc hx

/-- For a positive natural mass m and positive exponent n, either there is a positive cutoff
x at most U with m at most x^n at most 2^n*m, or U^n is at most m.
Take one more than the integer n-th root. This supplies an exact cutoff without real rounding. -/
theorem exists_power_cutoff_or_base {m U n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (∃ x : ℕ, 0 < x ∧ x ≤ U ∧ m ≤ x ^ n ∧ x ^ n ≤ 2 ^ n * m) ∨ U ^ n ≤ m := by
  have hn0 := ne_of_gt hn
  have hr : 1 ≤ Nat.nthRoot n m :=
    (Nat.le_nthRoot_iff hn0).mpr
      (by
        rw [one_pow]; exact hm)
  by_cases hU : Nat.nthRoot n m + 1 ≤ U
  · left
    refine ⟨Nat.nthRoot n m + 1, Nat.zero_lt_succ _, hU, (Nat.lt_pow_nthRoot_add_one hn0 m).le, ?_⟩
    have hdouble : Nat.nthRoot n m + 1 ≤ 2 * Nat.nthRoot n m := by nlinarith only [hr]
    calc
      _ ≤ (2 * Nat.nthRoot n m) ^ n := Nat.pow_le_pow_left hdouble n
      _ = 2 ^ n * Nat.nthRoot n m ^ n := mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_nthRoot_le (Or.inl hn0))
  · right
    have hu : U ≤ Nat.nthRoot n m := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hU)
    exact (Nat.pow_le_pow_left hu n).trans (Nat.pow_nthRoot_le (Or.inl hn0))

end PseudoPrime.NumberTheory.Heilbronn
