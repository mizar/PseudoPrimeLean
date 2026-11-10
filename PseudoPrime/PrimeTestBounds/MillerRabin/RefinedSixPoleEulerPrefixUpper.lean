/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerPrefix1000

/-! Certified upper bound for the refined Euler prefix through 1000. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Bound a prime-power Euler term using certified upper endpoints for its logarithm
and negative power. -/
theorem refined_euler_primePower_upper {p k n : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hn : n = p ^ k)
    {hi v : ℝ} (hl : Real.log p ≤ hi) (hv : (n : ℝ) ^ (-79 / 50 : ℝ) ≤ v) :
    ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n ≤
      hi * v * (3 + (81 / 25 : ℝ) * (k : ℝ) * hi + (729 / 625 : ℝ) * ((k : ℝ) * hi) ^ 2) / 8 := by
  have hΛ : ArithmeticFunction.vonMangoldt n = Real.log p := by
    rw [hn, ArithmeticFunction.vonMangoldt_apply_pow hk,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : Real.log n = (k : ℝ) * Real.log p := by rw [hn, Nat.cast_pow, Real.log_pow]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hp0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hi0 : 0 ≤ hi := hp0.trans hl
  have hkl : Real.log n ≤ (k : ℝ) * hi := by
    rw [hlog]
    exact mul_le_mul_of_nonneg_left hl hk0
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hsq := pow_le_pow_left₀ hlog0 hkl 2
  have hpoly :
    3 + (81 / 25 : ℝ) * Real.log n + (729 / 625 : ℝ) * (Real.log n) ^ 2 ≤
      3 + (81 / 25 : ℝ) * ((k : ℝ) * hi) + (729 / 625 : ℝ) * ((k : ℝ) * hi) ^ 2 := by
    linarith only [hkl, hsq]
  have hpoly0 : 0 ≤ 3 + (81 / 25 : ℝ) * Real.log n + (729 / 625 : ℝ) * (Real.log n) ^ 2 := by
    nlinarith only [hlog0, sq_nonneg (Real.log n)]
  have hpow0 : 0 ≤ (n : ℝ) ^ (-79 / 50 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hv0 : 0 ≤ v := hpow0.trans hv
  have h1 := mul_le_mul hl hv hpow0 hi0
  have h2 := mul_le_mul h1 hpoly hpoly0 (mul_nonneg hi0 hv0)
  rw [hΛ]
  unfold refinedSixEulerWeight
  rw [neg_div, Real.rpow_neg (Nat.cast_nonneg n)] at h2
  simp only [div_eq_mul_inv, mul_inv_rev] at h2 ⊢
  nlinarith only [h2]

/-- The rational upper contribution of a prime-power row with a one-trillionth power allowance. -/
def refinedEulerAtomUpper (n : ℕ) (r : RefinedEulerAtom) : ℚ :=
  if IsPrimePow n then
    r.hi * (r.v + 1 / 1000000000000) *
        (3 + (81 / 25 : ℚ) * r.k * r.hi + (729 / 625 : ℚ) * ((r.k : ℚ) * r.hi) ^ 2) /
      8
  else 0

/-- Check the negative-power upper endpoint used by the Euler row. -/
def refinedEulerUpperCheck (n : ℕ) (r : RefinedEulerAtom) : Bool :=
  AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck n 0 (r.v + 1 / 1000000000000) 79 50

/-- A checked prime-power row bounds its refined Euler contribution above. -/
theorem refined_euler_upper_atom_sound {n : ℕ} {r : RefinedEulerAtom}
    (hc : IsPrimePow n → refinedEulerAtomCheck 24 n r = true)
    (hu : IsPrimePow n → refinedEulerUpperCheck n r = true) :
    ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n ≤
      (refinedEulerAtomUpper n r : ℝ) := by
  by_cases hn : IsPrimePow n
  · have h := hc hn
    simp only [refinedEulerAtomCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl := Analysis.rationalLogIntervalCheck_sound h.2.1
    have hv := AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (hu hn)
    simp only [Rat.cast_natCast] at hl hv
    norm_num only at hv
    have he :=
      refined_euler_primePower_upper h.1.1 h.1.2.1 h.1.2.2.1.symm hl.2
        (by
          simpa only [neg_div, refinedEulerUpperCheck, Rat.cast_add, Rat.cast_div, Rat.cast_one,
            Rat.cast_ofNat] using hv.2)
    simpa only [refinedEulerAtomUpper, ite_eq_left hn, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow] using he
  · have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
    simp only [refinedEulerAtomUpper, ite_eq_right hn, Rat.cast_zero, hz, zero_mul, le_refl]

set_option maxRecDepth 1000000 in
-- Kernel reduction checks the finite rational certificate.
/-- The 193 stored rows pass their upper negative-power checks. -/
theorem refined_euler_upper_check :
    ∀ n ∈ refinedEulerPrefixSet,
      IsPrimePow n → refinedEulerUpperCheck n (refinedEulerData n) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
-- Kernel reduction checks the finite rational certificate.
/-- All prime powers at most 1000 occur in the stored prefix. -/
theorem refined_euler_prefix_support :
    ∀ n ∈ Finset.Ioc 0 1000, IsPrimePow n → n ∈ refinedEulerPrefixSet := by decide +kernel

set_option maxRecDepth 1000000 in
-- Kernel reduction checks the finite rational certificate.
/-- The rational upper row sum is strictly below 13107/5000. -/
theorem refined_euler_prefix_rational_upper :
    ∑ n ∈ refinedEulerPrefixSet, refinedEulerAtomUpper n (refinedEulerData n) <
      (13107 / 5000 : ℚ) := by
  decide +kernel

set_option maxRecDepth 1000000 in
-- Kernel reduction checks the finite rational certificate.
/-- All stored prefix indices lie in the interval from one to 1000. -/
theorem refined_euler_prefix_subset : refinedEulerPrefixSet ⊆ Finset.Ioc 0 1000 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The refined Euler prefix through 1000 is below 13107/5000. -/
theorem refined_euler_prefix_1000_upper :
    (∑ n ∈ Finset.Ioc 0 1000, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) <
      (13107 / 5000 : ℝ) := by
  have he :
    (∑ n ∈ Finset.Ioc 0 1000, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) =
      ∑ n ∈ refinedEulerPrefixSet, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    symm
    apply Finset.sum_subset refined_euler_prefix_subset
    intro n hn hn'
    have hnp : ¬IsPrimePow n := fun hp ↦ hn' (refined_euler_prefix_support n hn hp)
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp, zero_mul]
  have hu :
    (∑ n ∈ refinedEulerPrefixSet, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) ≤
      ((∑ n ∈ refinedEulerPrefixSet, refinedEulerAtomUpper n (refinedEulerData n) : ℚ) : ℝ) := by
    rw [Rat.cast_sum]
    apply Finset.sum_le_sum
    intro n hn
    exact
      refined_euler_upper_atom_sound (refined_euler_prefix_check n hn)
        (refined_euler_upper_check n hn)
  have hr :
    ((∑ n ∈ refinedEulerPrefixSet, refinedEulerAtomUpper n (refinedEulerData n) : ℚ) : ℝ) <
      (((13107 / 5000 : ℚ) : ℝ)) :=
    Rat.cast_lt.mpr refined_euler_prefix_rational_upper
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  rw [he]
  exact hu.trans_lt hr

end PseudoPrime.PrimeTestBounds.MillerRabin
