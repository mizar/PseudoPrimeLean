/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleGammaSecond
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates

/-! # Exact rational certificates for the refined Euler prefix -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime-power term of the normalized refined Euler weight is bounded below
by a rational-type expression using lower bounds for the prime logarithm and
the negative power. Positivity and monotonicity of the logarithmic polynomial
preserve the lower bounds. This is the analytic step of each certificate row. -/
theorem refined_euler_primePower_lower {p k n : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hn : n = p ^ k)
    {lo v : ℝ} (hlo : 0 ≤ lo) (hl : lo ≤ Real.log p) (hv0 : 0 ≤ v)
    (hv : v ≤ (n : ℝ) ^ (-79 / 50 : ℝ)) :
    lo * v * (3 + (81 / 25 : ℝ) * (k : ℝ) * lo + (729 / 625 : ℝ) * ((k : ℝ) * lo) ^ 2) / 8 ≤
      ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have hΛ : ArithmeticFunction.vonMangoldt n = Real.log p := by
    rw [hn, ArithmeticFunction.vonMangoldt_apply_pow hk,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : Real.log n = (k : ℝ) * Real.log p := by rw [hn, Nat.cast_pow, Real.log_pow]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hp0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hkl : (k : ℝ) * lo ≤ Real.log n := by
    rw [hlog]
    exact mul_le_mul_of_nonneg_left hl hk0
  have hkl0 : 0 ≤ (k : ℝ) * lo := mul_nonneg hk0 hlo
  have hsq := pow_le_pow_left₀ hkl0 hkl 2
  have hpoly :
    3 + (81 / 25 : ℝ) * ((k : ℝ) * lo) + (729 / 625 : ℝ) * ((k : ℝ) * lo) ^ 2 ≤
      3 + (81 / 25 : ℝ) * Real.log n + (729 / 625 : ℝ) * (Real.log n) ^ 2 := by
    linarith only [hkl, hsq]
  have hpoly0 : 0 ≤ 3 + (81 / 25 : ℝ) * ((k : ℝ) * lo) + (729 / 625 : ℝ) * ((k : ℝ) * lo) ^ 2 := by
    nlinarith only [hkl0, sq_nonneg ((k : ℝ) * lo)]
  have hpow0 : 0 ≤ (n : ℝ) ^ (-79 / 50 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h1 := mul_le_mul hl hv hv0 hp0
  have h2 := mul_le_mul h1 hpoly hpoly0 (mul_nonneg hp0 hpow0)
  rw [hΛ]
  unfold refinedSixEulerWeight
  rw [neg_div, Real.rpow_neg (Nat.cast_nonneg n)] at h2
  simp only [div_eq_mul_inv, mul_inv_rev] at h2 ⊢
  nlinarith only [h2]

/-- Rational data for one prime-power Euler-prefix term. The fields record the
prime base, exponent, logarithm interval and lower negative-power endpoint.
The accompanying checker verifies all conditions before the data are used. -/
structure RefinedEulerAtom where
  p : ℕ
  k : ℕ
  lo : ℚ
  hi : ℚ
  v : ℚ
  deriving Inhabited, DecidableEq

/-- Check a prime-power identity, nonnegative lower endpoints, a rational
logarithm interval and the negative-power enclosure for a prefix row. A true
result makes the numerical row usable in the real weighted Euler sum. -/
def refinedEulerAtomCheck (terms n : ℕ) (r : RefinedEulerAtom) : Bool :=
  decide (r.p.Prime ∧ r.k ≠ 0 ∧ r.p ^ r.k = n ∧ 0 ≤ r.lo ∧ 0 ≤ r.v) &&
    (Analysis.rationalLogIntervalCheck r.p (Nat.log2 r.p + 1) terms r.lo r.hi &&
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck n r.v 1 79 50)

/-- The rational lower Euler contribution represented by a row. It is zero
when the index is not a prime power; on prime powers it evaluates the
nonnegative logarithmic polynomial using the row''s lower endpoints. -/
def refinedEulerAtomLower (n : ℕ) (r : RefinedEulerAtom) : ℚ :=
  if IsPrimePow n then
    r.lo * r.v * (3 + (81 / 25 : ℚ) * r.k * r.lo + (729 / 625 : ℚ) * ((r.k : ℚ) * r.lo) ^ 2) / 8
  else 0

/-- A checked row bounds the corresponding real refined Euler term from below.
Soundness of the logarithm and power interval checkers supplies the analytic
inputs; non-prime-power indices have zero von Mangoldt value. -/
theorem refined_euler_atom_sound {terms n : ℕ} {r : RefinedEulerAtom}
    (hc : IsPrimePow n → refinedEulerAtomCheck terms n r = true) :
    (refinedEulerAtomLower n r : ℝ) ≤
      ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  by_cases hn : IsPrimePow n
  · have h := hc hn
    simp only [refinedEulerAtomCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl := Analysis.rationalLogIntervalCheck_sound h.2.1
    have hv := AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound h.2.2
    simp only [Rat.cast_natCast] at hl hv
    norm_num only at hv
    have he :=
      refined_euler_primePower_lower h.1.1 h.1.2.1 h.1.2.2.1.symm (Rat.cast_nonneg.mpr h.1.2.2.2.1)
        hl.1 (Rat.cast_nonneg.mpr h.1.2.2.2.2) (by simpa only [neg_div] using hv.1)
    simpa only [refinedEulerAtomLower, ite_eq_left hn, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using he
  · have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
    simp only [refinedEulerAtomLower, ite_eq_right hn, Rat.cast_zero, hz, zero_mul, le_refl]

/-- The sum of checked rational rows over a finite set is a lower bound for
the actual refined Euler prefix. Cast the rational sum and apply the row
soundness theorem term by term. This is the finite certificate interface. -/
theorem refined_euler_prefix_sound {terms : ℕ} (s : Finset ℕ) (r : ℕ → RefinedEulerAtom)
    (hc : ∀ n ∈ s, IsPrimePow n → refinedEulerAtomCheck terms n (r n) = true) :
    ((∑ n ∈ s, refinedEulerAtomLower n (r n) : ℚ) : ℝ) ≤
      ∑ n ∈ s, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  rw [Rat.cast_sum]
  exact Finset.sum_le_sum (fun n hn ↦ refined_euler_atom_sound (hc n hn))

end PseudoPrime.PrimeTestBounds.MillerRabin
