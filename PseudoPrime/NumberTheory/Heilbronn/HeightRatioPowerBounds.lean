/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeightRatioLayers
public import PseudoPrime.NumberTheory.Heilbronn.DivisorPowerBounds

/-! # Polynomial losses for canonical-height ratio layers -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The total height exponent after raising the layer growth inequality to r
and replacing the quotient-growth coefficient by its explicit polynomial bound.
The fixed degree m and free parameters n,r allow an arbitrarily small relative loss. -/
def heightRatioLossExponent (m n r : ℕ) : ℕ :=
  ((m - 1) * m) * r + (4 * m) * (n ^ 2 * (m - 1))

/-- Actual height-restricted ratios satisfy a polynomial bound with a coefficient
depending only on m,n,r. Raise the existing growth estimate to r, replace the
quotient coefficient by its proved divisor/logarithmic bound, and collect powers.
There is no additional rational-growth or congruence-count hypothesis. -/
theorem heightRestrictedRatioSet_power_le_polynomial {p H T m n r : ℕ} [Fact p.Prime] (hHp : H < p)
    (hT : 0 < T) (hm : 0 < m) (hn : 0 < n) (hr : 0 < r) (hmod : T ^ (2 * m) < p ^ 2) :
    (heightRestrictedRatioSet p H T).card ^ (n * m * r) ≤
      quotientPowerBoundConstant r ^ (n ^ 2 * (m - 1)) * T ^ heightRatioLossExponent m n r *
        (p - 1) ^ (n * r) := by
  have hg := Nat.pow_le_pow_left (heightRestrictedRatioSet_power_growth_bound hHp hT hm hn hmod) r
  have hq :=
    Nat.pow_le_pow_left
      (quotientPowerConstant_pow_le_explicit (U := T ^ (2 * m)) (Nat.pow_pos hT) hr)
      (n ^ 2 * (m - 1))
  have hg' :
    (heightRestrictedRatioSet p H T).card ^ (n * m * r) ≤
      (quotientPowerConstant (T ^ (2 * m)) ^ r) ^ (n ^ 2 * (m - 1)) * T ^ (((m - 1) * m) * r) *
        (p - 1) ^ (n * r) := by
    simpa only [mul_pow, ← pow_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hg
  have hmul :=
    Nat.mul_le_mul_right ((p - 1) ^ (n * r)) (Nat.mul_le_mul_right (T ^ (((m - 1) * m) * r)) hq)
  apply hg'.trans
  convert hmul using 1
  simp only [quotientPowerBoundConstant, heightRatioLossExponent, divisorPowerBoundConstant,
    mul_pow, pow_add, ← pow_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  ring

/-- For each fixed positive degree m and each natural precision c, choose
positive n,r so that c times the height loss is smaller than n*m*r.
The explicit choices leave an exact positive gap m, allowing arbitrarily
small height-power losses without changing the subgroup degree. -/
theorem exists_height_ratio_small_loss {m : ℕ} (hm : 0 < m) (c : ℕ) :
    ∃ n r : ℕ, 0 < n ∧ 0 < r ∧ c * heightRatioLossExponent m n r < n * m * r := by
  let n := c * (m - 1) + 1
  let r := 4 * c * n ^ 2 * (m - 1) + 1
  refine ⟨n, r, Nat.succ_pos _, Nat.succ_pos _, ?_⟩
  have he : n * m * r = c * heightRatioLossExponent m n r + m := by
    dsimp only [n, r, heightRatioLossExponent]
    ring
  rw [he]
  exact Nat.lt_add_of_pos_right hm

/-- For fixed subgroup degree m and requested precision c, one common choice
of n,r and coefficient C works for every prime and every admissible height
layer. The relative height loss is smaller than 1/c when c is positive.
All constants are independent of p,H,T and no growth hypothesis is supplied. -/
theorem exists_uniform_height_ratio_power_bound {m : ℕ} (hm : 0 < m) (c : ℕ) :
    ∃ n r C : ℕ,
      0 < n ∧
        0 < r ∧
        c * heightRatioLossExponent m n r < n * m * r ∧
        ∀ (p H T : ℕ) [Fact p.Prime],
          H < p →
            0 < T →
            T ^ (2 * m) < p ^ 2 →
            (heightRestrictedRatioSet p H T).card ^ (n * m * r) ≤
              C * T ^ heightRatioLossExponent m n r * p ^ (n * r) := by
  obtain ⟨n, r, hn, hr, hl⟩ := exists_height_ratio_small_loss hm c
  refine ⟨n, r, quotientPowerBoundConstant r ^ (n ^ 2 * (m - 1)), hn, hr, hl, ?_⟩
  intro p H T hp hHp hT hmod
  exact
    (heightRestrictedRatioSet_power_le_polynomial hHp hT hm hn hr hmod).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.sub_le p 1) (n * r)))

/-- Extract a real root from a natural polynomial count bound, with a harmless
coefficient C+1 independent of all variables. Compare N-th powers and retain
the exact height and modulus exponents as real quotients. -/
theorem natural_count_le_polynomial_root {a C T p L M N : ℕ} (hN : 0 < N)
    (h : a ^ N ≤ C * T ^ L * p ^ M) :
    (a : ℝ) ≤ (C + 1 : ℕ) * (T : ℝ) ^ ((L : ℝ) / N) * (p : ℝ) ^ ((M : ℝ) / N) := by
  have hn0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  have hroot (x e : ℕ) : ((x : ℝ) ^ ((e : ℝ) / N)) ^ N = (x : ℝ) ^ e := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg x), div_mul_cancel₀ _ hn0, Real.rpow_natCast]
  have hc : C ≤ (C + 1) ^ N := by
    have hp := Nat.pow_le_pow_right (Nat.succ_pos C) hN
    exact (Nat.le_succ C).trans (by simpa only [pow_one] using hp)
  have hb := h.trans (Nat.mul_le_mul_right (p ^ M) (Nat.mul_le_mul_right (T ^ L) hc))
  have hr : 0 ≤ (C + 1 : ℕ) * (T : ℝ) ^ ((L : ℝ) / N) * (p : ℝ) ^ ((M : ℝ) / N) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg a) hr (ne_of_gt hN)).mp
  rw [mul_pow, mul_pow, hroot, hroot]
  have hh := Nat.cast_le (α := ℝ).mpr hb
  simpa only [Nat.cast_mul, Nat.cast_pow] using hh

/-- Inputs: a positive real exponent `delta`. Claim: one positive real constant bounds
`maxDivisorCount H` by that constant times `H^delta` for every natural `H`. Content: extract
an `r`-th root from the explicit divisor-power estimate with `1/r < delta`. Proof: apply
`natural_count_le_polynomial_root`, handle `H=0` directly, and use monotonicity of real powers
for `H≥1`. Role: absorb the small-height divisor loss in the shifted-layer congruence count. -/
theorem exists_uniform_maxDivisorCount_rpow_bound {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, (maxDivisorCount H : ℝ) ≤ C * (H : ℝ) ^ delta := by
  obtain ⟨r, hr, hrecip⟩ := Real.exists_nat_pos_inv_lt hdelta
  let D : ℕ := (r.factorial * 2 ^ r) ^ (2 ^ (r - 1))
  refine ⟨(D + 1 : ℕ), Nat.cast_pos.mpr (Nat.succ_pos D), ?_⟩
  intro H
  have hpoly := maxDivisorCount_pow_le_explicit H hr
  have hpoly' : maxDivisorCount H ^ r ≤ D * H := by
    exact hpoly.trans (Nat.mul_le_mul_right H (divisorPowerBoundConstant_le_half r))
  have hpoly'' : maxDivisorCount H ^ r ≤ D * 1 ^ 0 * H ^ 1 := by
    simpa only [Nat.one_pow, Nat.pow_one, Nat.mul_one] using hpoly'
  have hroot :=
    natural_count_le_polynomial_root (a := maxDivisorCount H) (C := D) (T := 1) (p := H) (L := 0)
      (M := 1) (N := r) hr hpoly''
  by_cases hH : H = 0
  · subst H
    simp only [maxDivisorCount, Nat.zero_add, Finset.range_one, Finset.sup_singleton,
      Nat.divisors_zero, Finset.card_empty, Nat.cast_zero, Real.zero_rpow hdelta.ne', mul_zero]
    exact le_rfl
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
    have hHreal : (1 : ℝ) ≤ (H : ℝ) := Nat.one_le_cast.mpr hHpos
    have hExp : 1 / (r : ℝ) ≤ delta := by simpa only [one_div] using hrecip.le
    have hpow := Real.rpow_le_rpow_of_exponent_le hHreal hExp
    have hroot' : (maxDivisorCount H : ℝ) ≤ (D + 1 : ℕ) * (H : ℝ) ^ (1 / (r : ℝ)) := by
      simpa only [Nat.cast_zero, zero_div, Nat.cast_one, one_mul, mul_one, Real.one_rpow] using
        hroot
    exact hroot'.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (D + 1)))

/-- For fixed positive degree m and precision c, one positive real constant
bounds every admissible restricted ratio count by C*T^(1/c)*p^(1/m).
Choose polynomial parameters with sufficiently small height loss and extract
the natural root. The coefficient is independent of the prime and both heights. -/
theorem exists_uniform_height_ratio_rpow_bound {m c : ℕ} (hm : 0 < m) (hc : 0 < c) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (p H T : ℕ) [Fact p.Prime],
          H < p →
            0 < T →
            T ^ (2 * m) < p ^ 2 →
            ((heightRestrictedRatioSet p H T).card : ℝ) ≤
              C * (T : ℝ) ^ (1 / (c : ℝ)) * (p : ℝ) ^ (1 / (m : ℝ)) := by
  obtain ⟨n, r, D, hn, hr, hl, hbound⟩ := exists_uniform_height_ratio_power_bound hm c
  refine ⟨(D + 1 : ℕ), Nat.cast_pos.mpr (Nat.succ_pos D), ?_⟩
  intro p H T hp hHp hT hmod
  have hN := Nat.mul_pos (Nat.mul_pos hn hm) hr
  have hN0 : (0 : ℝ) < (n * m * r : ℕ) := Nat.cast_pos.mpr hN
  have hc0 : (0 : ℝ) < c := Nat.cast_pos.mpr hc
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have he : ((n * r : ℕ) : ℝ) / (n * m * r : ℕ) = 1 / (m : ℝ) := by
    apply (div_eq_div_iff (ne_of_gt hN0) (ne_of_gt hm0)).mpr
    simp only [Nat.cast_mul, one_mul]
    ring
  have hl' : ((heightRatioLossExponent m n r : ℕ) : ℝ) / (n * m * r : ℕ) ≤ 1 / (c : ℝ) := by
    apply (div_le_div_iff₀ hN0 hc0).mpr
    have hh := Nat.cast_le (α := ℝ).mpr hl.le
    simpa only [Nat.cast_mul, one_mul, mul_one, mul_comm] using hh
  have hb := natural_count_le_polynomial_root hN (hbound p H T hHp hT hmod)
  rw [he] at hb
  have ht := Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hT) hl'
  exact
    hb.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (D + 1)))
        (Real.rpow_nonneg (Nat.cast_nonneg p) _))

/-- For each fixed positive degree m and each real delta>0, there is one
positive constant C such that every admissible height layer has at most
C*T^delta*p^(1/m) distinct ratios. Choose a reciprocal natural precision
below delta and use monotonicity of real powers for T>=1. -/
theorem exists_uniform_height_ratio_small_power_bound {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (p H T : ℕ) [Fact p.Prime],
          H < p →
            0 < T →
            T ^ (2 * m) < p ^ 2 →
            ((heightRestrictedRatioSet p H T).card : ℝ) ≤
              C * (T : ℝ) ^ δ * (p : ℝ) ^ (1 / (m : ℝ)) := by
  obtain ⟨c, hc, hprec⟩ := Real.exists_nat_pos_inv_lt hδ
  obtain ⟨C, hC, hb⟩ := exists_uniform_height_ratio_rpow_bound hm hc
  refine ⟨C, hC, ?_⟩
  intro p H T hp hHp hT hmod
  have he : 1 / (c : ℝ) ≤ δ := by simpa only [one_div] using hprec.le
  have ht := Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hT) he
  exact
    (hb p H T hHp hT hmod).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hC.le)
        (Real.rpow_nonneg (Nat.cast_nonneg p) _))

end PseudoPrime.NumberTheory.Heilbronn
