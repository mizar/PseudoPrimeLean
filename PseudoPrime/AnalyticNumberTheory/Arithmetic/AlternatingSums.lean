/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors

/-!
# Elementary alternating-sum bounds

This file bounds alternating sums of nonnegative decreasing real sequences and specializes
them to `1/p^k - 1/x`. It also gives exact alternating sums of affine weights and the rational
inequality `(1 - 1/y)⁻² * (c - b)/2 ≤ c/2 + 13/20` under the stated bounds on `y`, `c`, and `b`.
-/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-! Input: a nonnegative non-increasing sequence on `[1, 2m]`. Conclusion: its even alternating
sum is nonnegative and bounded by the first-to-last drop. -/

theorem sum_neg_one_pow_succ_mul_even_bounds {a : ℕ → ℝ} {K : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (hmK : 2 * m ≤ K) (ha_nonneg : ∀ k, 1 ≤ k → k ≤ K → 0 ≤ a k)
    (ha_anti : ∀ k, 1 ≤ k → k < K → a (k + 1) ≤ a k) :
    0 ≤ ∑ k ∈ Finset.Icc 1 (2 * m), (-1 : ℝ) ^ (k + 1) * a k ∧
      ∑ k ∈ Finset.Icc 1 (2 * m), (-1 : ℝ) ^ (k + 1) * a k ≤ a 1 - a (2 * m) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have hanti12 : a 2 ≤ a 1 := ha_anti 1 le_rfl (by omega)
    have hterm : ∑ k ∈ Finset.Icc 1 2, (-1 : ℝ) ^ (k + 1) * a k = a 1 - a 2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_Icc_succ_top (by omega), Finset.Icc_self,
        Finset.sum_singleton]
      ring
    rw [show (2 * 1 : ℕ) = 2 from rfl, hterm]
    exact ⟨by linarith, le_rfl⟩
  | succ m hm ih =>
    have hmK' : 2 * m ≤ K := by omega
    obtain ⟨hnonneg, hle⟩ := ih hmK'
    have heq :
      ∑ k ∈ Finset.Icc 1 (2 * m + 1 + 1), (-1 : ℝ) ^ (k + 1) * a k =
        (∑ k ∈ Finset.Icc 1 (2 * m), (-1 : ℝ) ^ (k + 1) * a k) + a (2 * m + 1) -
          a (2 * m + 1 + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have hpow1 : (-1 : ℝ) ^ (2 * m + 1 + 1) = 1 := Even.neg_one_pow ⟨m + 1, by ring⟩
      have hpow2 : (-1 : ℝ) ^ (2 * m + 1 + 1 + 1) = -1 := Odd.neg_one_pow ⟨m + 1, by ring⟩
      rw [hpow1, hpow2]
      ring
    have hanti1 : a (2 * m + 1 + 1) ≤ a (2 * m + 1) := ha_anti (2 * m + 1) (by omega) (by omega)
    have hanti0 : a (2 * m + 1) ≤ a (2 * m) := ha_anti (2 * m) (by omega) (by omega)
    have ha2m1 : 0 ≤ a (2 * m + 1) := ha_nonneg (2 * m + 1) (by omega) (by omega)
    have hK2 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [hK2, heq]
    exact ⟨by linarith, by linarith⟩

/-! Input: a nonnegative non-increasing sequence on `[1,K]`, with `K ≥ 1`. Conclusion: its
alternating sum lies between zero and its first term. -/

theorem sum_neg_one_pow_succ_mul_bounds {a : ℕ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    (ha_nonneg : ∀ k, 1 ≤ k → k ≤ K → 0 ≤ a k) (ha_anti : ∀ k, 1 ≤ k → k < K → a (k + 1) ≤ a k) :
    0 ≤ ∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ (k + 1) * a k ∧
      ∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ (k + 1) * a k ≤ a 1 := by
  rcases Nat.even_or_odd K with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hm1 : 1 ≤ m := by omega
    have hbound := sum_neg_one_pow_succ_mul_even_bounds m hm1 (by omega) ha_nonneg ha_anti
    have ha2m : 0 ≤ a (2 * m) := ha_nonneg (2 * m) (by omega) (by omega)
    have hKeq : K = 2 * m := by omega
    rw [hKeq]
    exact ⟨hbound.1, by linarith only [hbound.2, ha2m]⟩
  · rcases Nat.eq_zero_or_pos m with hm0 | hm1
    · have ha1 : 0 ≤ a 1 := ha_nonneg 1 le_rfl hK
      have hKeq : K = 1 := by omega
      rw [hKeq]
      have hsum : ∑ k ∈ Finset.Icc 1 1, (-1 : ℝ) ^ (k + 1) * a k = a 1 := by
        simp only [Finset.Icc_self, Finset.sum_singleton, Nat.reduceAdd, even_two, Even.neg_pow,
          one_pow, one_mul]
      rw [hsum]
      exact ⟨ha1, le_rfl⟩
    · have hbound :=
        sum_neg_one_pow_succ_mul_even_bounds m hm1 (by omega) ha_nonneg
          (fun k hk1 hkK ↦ ha_anti k hk1 (by omega))
      have heq :
        ∑ k ∈ Finset.Icc 1 (2 * m + 1), (-1 : ℝ) ^ (k + 1) * a k =
          (∑ k ∈ Finset.Icc 1 (2 * m), (-1 : ℝ) ^ (k + 1) * a k) + a (2 * m + 1) := by
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hpow : (-1 : ℝ) ^ (2 * m + 1 + 1) = 1 := Even.neg_one_pow ⟨m + 1, by ring⟩
        rw [hpow]
        ring
      have ha2m1 : 0 ≤ a (2 * m + 1) := ha_nonneg (2 * m + 1) (by omega) (by omega)
      have ha2m1le : a (2 * m + 1) ≤ a (2 * m) := ha_anti (2 * m) (by omega) (by omega)
      have hKeq : K = 2 * m + 1 := by omega
      rw [hKeq, heq]
      exact ⟨by linarith only [hbound.1, ha2m1], by linarith only [hbound.2, ha2m1le]⟩

/-! The alternating reciprocal prime-power sum is bounded by `1/p - 1/x`. -/

theorem sum_neg_one_pow_succ_mul_inv_pow_bounds {p : ℕ} (hp : p.Prime) {x : ℝ} (_hx : 0 < x) {K : ℕ}
    (hK : 1 ≤ K) (hKle : (p : ℝ) ^ K ≤ x) :
    0 ≤ ∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ (k + 1) * (1 / (p : ℝ) ^ k - 1 / x) ∧
      ∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ (k + 1) * (1 / (p : ℝ) ^ k - 1 / x) ≤
        1 / (p : ℝ) - 1 / x := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hbound :=
    sum_neg_one_pow_succ_mul_bounds (a := fun k ↦ 1 / (p : ℝ) ^ k - 1 / x) hK
      (fun k _ hkK ↦ by
        have hpk : (p : ℝ) ^ k ≤ x := (pow_le_pow_right₀ hp1 hkK).trans hKle
        have hpkpos : (0 : ℝ) < (p : ℝ) ^ k := by positivity
        have := one_div_le_one_div_of_le hpkpos hpk
        linarith)
      (fun k _ _ ↦ by
        have hstep : (p : ℝ) ^ k ≤ (p : ℝ) ^ (k + 1) := pow_le_pow_right₀ hp1 (Nat.le_succ k)
        have hpkpos : (0 : ℝ) < (p : ℝ) ^ k := by positivity
        have := one_div_le_one_div_of_le hpkpos hstep
        linarith)
  simpa only [one_div, pow_one] using hbound

/-! For real `y ≥ 8`, `conductorLog ≤ y`, and `1 ≤ piLog ≤ conductorLog`, the inverse-square
factor costs at most `13/20` after subtracting `piLog/2`. The proof clears the positive
denominator `(y - 1)²` and bounds the resulting polynomial. -/

theorem inverseSquareLogTradeoff {y conductorLog piLog : ℝ} (hy : 8 ≤ y) (hc : conductorLog ≤ y)
    (hp : 1 ≤ piLog) (_hdiff : 0 ≤ conductorLog - piLog) :
    (1 - 1 / y)⁻¹ ^ 2 * ((conductorLog - piLog) / 2) ≤ conductorLog / 2 + 13 / 20 := by
  have hypos : 0 < y := by linarith
  have hyone : 0 < y - 1 := by linarith
  have hinverse : (1 - 1 / y)⁻¹ ^ 2 = y ^ 2 / (y - 1) ^ 2 := by field_simp [hypos.ne']
  rw [hinverse, div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hyone)]
  have hfactor : 0 ≤ 2 * y - 1 := by linarith
  have hconductorMul := mul_le_mul_of_nonneg_left hc hfactor
  have hpiMul := mul_le_mul_of_nonneg_left hp (sq_nonneg y)
  nlinarith only [hconductorMul, hpiMul, _hdiff, hy, hfactor]

/-- Exact even-length alternating sum for an affine weight. -/
theorem sum_neg_one_pow_succ_mul_affine_even (a L : ℝ) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * m), (-1 : ℝ) ^ (k + 1) * (L - k * a) = (m : ℝ) * a := by
  induction m with
  | zero =>
    simp only [mul_zero, Order.lt_one_iff, Finset.Icc_eq_empty_of_lt, Finset.sum_empty,
      CharP.cast_eq_zero, zero_mul]
  | succ m ih =>
    have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [h2, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have hpow1 : (-1 : ℝ) ^ (2 * m + 1 + 1) = 1 := Even.neg_one_pow ⟨m + 1, by ring⟩
    have hpow2 : (-1 : ℝ) ^ (2 * m + 1 + 1 + 1) = -1 := Odd.neg_one_pow ⟨m + 1, by ring⟩
    rw [hpow1, hpow2, ih]
    push_cast
    ring

/-- Exact odd-length alternating sum for an affine weight. -/
theorem sum_neg_one_pow_succ_mul_affine_odd (a L : ℝ) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * m + 1), (-1 : ℝ) ^ (k + 1) * (L - k * a) = L - (m + 1 : ℝ) * a := by
  rw [Finset.sum_Icc_succ_top (by omega), sum_neg_one_pow_succ_mul_affine_even a L m]
  have hpow : (-1 : ℝ) ^ (2 * m + 1 + 1) = 1 := Even.neg_one_pow ⟨m + 1, by ring⟩
  rw [hpow]
  push_cast
  ring

end PseudoPrime.AnalyticNumberTheory.Arithmetic
