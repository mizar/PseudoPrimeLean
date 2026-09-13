/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt

/-!
# Small-prime-factor exclusion clears the common-factor weighted sums

This file gives the arithmetic step behind LLS Theorem 1.1(2)'s original small-prime-exclusion
hypothesis: if `m` has no prime factor strictly below `X`, then both weighted common-factor sums
`commonFactorLogWeightedSum X m` and `commonFactorReciprocalWeightedSum X m` vanish identically.

No character is involved: this is a fact about the natural number `m` and the real cutoff `X`
alone. It does not require `X ∉ ℕ`, or that the boundary case `p = X` (for `p ∣ m` prime) cannot
occur: at `n = X` the log-weight `log(X / n)` and the reciprocal weight `1 - n / X` both vanish, so
that boundary term contributes `0` to the sum regardless of whether it survives the strict
inequality used in the hypothesis.
-/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- `m` has no prime factor strictly below the real cutoff `X`. -/
def NoSmallPrimeFactor (m : ℕ) (X : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℝ) < X → ¬p ∣ m

/--
Input/assumptions: `X > 0` and `m` has no prime factor strictly below `X`.
Conclusion: the logarithmic common-factor weighted sum at `X` vanishes.
Content: every surviving prime divisor `p ≤ ⌊X⌋₊` of `m` must satisfy `(p : ℝ) = X` (since the
hypothesis forbids `p < X`, and `p ≤ ⌊X⌋₊ ≤ X` forbids `p > X`); the same equality then forces
every admissible power `p ^ k` in the reindexed sum to equal `X`, making `log(X / p ^ k) = 0`.
Role: supplies `dS = 0` for the common public core `LLSWeightedComparisonCore` on the original-paper
branch.
-/
theorem commonFactorLogWeightedSum_eq_zero_of_noSmallPrimeFactor {m : ℕ} {X : ℝ} (hX : 0 < X)
    (hsmall : NoSmallPrimeFactor m X) : commonFactorLogWeightedSum X m = 0 := by
  rw [commonFactorLogWeightedSum_eq_sum_prime_divisors]
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hpmem, hpdvd⟩ := Finset.mem_filter.mp hp
  have hpprime : p.Prime := Nat.prime_of_mem_primesLE hpmem
  have hpfloor : p ≤ ⌊X⌋₊ := Nat.le_of_mem_primesLE hpmem
  have hpXle : (p : ℝ) ≤ X := (Nat.cast_le.mpr hpfloor).trans (Nat.floor_le hX.le)
  have hpXge : X ≤ (p : ℝ) := by
    by_contra hlt
    exact hsmall p hpprime (not_le.mp hlt) hpdvd
  have hpXeq : (p : ℝ) = X := le_antisymm hpXle hpXge
  apply Finset.sum_eq_zero
  intro k hk
  obtain ⟨hk1, hkle⟩ := Finset.mem_Icc.mp hk
  have hfloorne : ⌊X⌋₊ ≠ 0 := by
    have : 0 < ⌊X⌋₊ := lt_of_lt_of_le hpprime.pos hpfloor
    omega
  have hpk_le_nat : p ^ k ≤ ⌊X⌋₊ := Nat.pow_le_of_le_log hfloorne hkle
  have hpk_le : ((p ^ k : ℕ) : ℝ) ≤ X := (Nat.cast_le.mpr hpk_le_nat).trans (Nat.floor_le hX.le)
  have hpk_ge : (p : ℝ) ≤ (p : ℝ) ^ k :=
    le_self_pow₀ (by exact_mod_cast hpprime.one_lt.le) (Nat.one_le_iff_ne_zero.mp hk1)
  push_cast at hpk_le
  have hpk_eq : (p : ℝ) ^ k = X := le_antisymm hpk_le (hpXeq ▸ hpk_ge)
  unfold logWeightedMangoldtTerm
  rw [show ((p ^ k : ℕ) : ℝ) = X from by
      push_cast; exact hpk_eq,
    div_self hX.ne', Real.log_one, mul_zero]

/--
Input/assumptions: `1 ≤ X` and `m` has no prime factor strictly below `X`.
Conclusion: the reciprocal common-factor weighted sum at `X` vanishes.
Content: reindex by `k` and the admissible prime range `p ≤ ⌊X ^ (1/k)⌋₊ ≤ X ^ (1/k) ≤ X`
(monotonicity of `x ↦ X ^ x` for `X ≥ 1`). The hypothesis forces `p ≥ X` for any surviving prime
divisor, so `p = X`; for `k ≥ 2` this makes `p ≤ X ^ (1/k) < p`, a contradiction, so no term
survives past `k = 1`, where `p = X` makes the reciprocal weight `1 - p / X` vanish.
Role: supplies `dR = 0` for the common public core `LLSWeightedComparisonCore` on the
original-paper branch.
-/
theorem commonFactorReciprocalWeightedSum_eq_zero_of_noSmallPrimeFactor {m : ℕ} {X : ℝ} (hX : 1 ≤ X)
    (hsmall : NoSmallPrimeFactor m X) : commonFactorReciprocalWeightedSum X m = 0 := by
  rw [commonFactorReciprocalWeightedSum_eq_sum_prime_powers m (zero_le_one.trans hX)]
  apply Finset.sum_eq_zero
  intro k hk
  obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hk
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hpmem, hpprime, hpdvd⟩ := Finset.mem_filter.mp hp
  have hpfloor : p ≤ ⌊X ^ ((1 : ℝ) / k)⌋₊ := (Finset.mem_Ioc.mp hpmem).2
  have hexp_le_one : (1 : ℝ) / k ≤ 1 := by
    rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk1))]
    exact_mod_cast hk1
  have hrpow_le : X ^ ((1 : ℝ) / k) ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX hexp_le_one
  have hpXle : (p : ℝ) ≤ X := by
    have :=
      (Nat.cast_le.mpr hpfloor).trans (Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hX) _))
    rw [Real.rpow_one] at hrpow_le
    exact this.trans hrpow_le
  have hpXge : X ≤ (p : ℝ) := by
    by_contra hlt
    exact hsmall p hpprime (not_le.mp hlt) hpdvd
  have hpXeq : (p : ℝ) = X := le_antisymm hpXle hpXge
  rcases eq_or_lt_of_le hk1 with hk1eq | hk1lt
  · have hkeq : k = 1 := hk1eq.symm
    subst hkeq
    unfold reciprocalWeightedMangoldtTerm
    rw [pow_one, hpXeq, div_self (zero_lt_one.trans_le hX).ne', sub_self, mul_zero]
  · exfalso
    have hpge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
    have hexp_lt_one : (1 : ℝ) / k < 1 := by
      rw [div_lt_one (by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk1))]
      exact_mod_cast hk1lt
    have hppow : (p : ℝ) ^ ((1 : ℝ) / k) < (p : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) hexp_lt_one
    rw [Real.rpow_one] at hppow
    have hfloor_lt : ⌊(p : ℝ) ^ ((1 : ℝ) / k)⌋₊ < p :=
      (Nat.floor_lt (Real.rpow_nonneg (by positivity) _)).mpr hppow
    rw [← hpXeq] at hpfloor
    omega

end PseudoPrime.AnalyticNumberTheory.Arithmetic
