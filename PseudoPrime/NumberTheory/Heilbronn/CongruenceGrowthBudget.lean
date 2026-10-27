/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.SignedCongruencePairCounting

/-! # Explicit full congruence counts in the Heilbronn energy budget -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The explicit natural bound for the 2*n*m-th power of the full bounded congruence count.
It combines the signed integer-pair multiplicity factor, divisor-count loss, proved rational
product-growth coefficient, height powers and subgroup cardinality. No congruence count occurs
on the right-hand side; all parameters p,H,m,n are natural. -/
noncomputable def congruenceCountPowerBound (p H m n : ℕ) : ℕ :=
  (144 * H ^ 2 * maxDivisorCount H ^ 2) ^ (n * m) *
    quotientPowerConstant (H ^ (2 * m)) ^ (n ^ 2 * (m - 1)) *
    H ^ ((m - 1) * m) *
    (p - 1) ^ n

/-- For odd prime p and positive H,m,n with H^(2m) less than p^2, bound the actual full count
raised to 2*n*m by congruenceCountPowerBound. Derive H less than p, apply the signed square
count, raise to n*m and substitute the proved positive-ratio growth estimate. -/
theorem boundedCongruenceCount_power_le_growth_bound {p H m n : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hH : 0 < H) (hm : 0 < m) (hn : 0 < n) (hmod : H ^ (2 * m) < p ^ 2) :
    boundedCongruenceCount p H ^ (2 * (n * m)) ≤ congruenceCountPowerBound p H m n := by
  have h2 := Nat.pow_le_pow_right hH (Nat.mul_le_mul_left 2 hm)
  have hHp : H < p := (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp (h2.trans_lt hmod)
  have hc := Nat.pow_le_pow_left (boundedCongruenceCount_sq_le_positive_ratios hodd hH hHp) (n * m)
  have hg := positive_ratio_power_growth_bound hH hm hn hmod
  calc
    _ = (boundedCongruenceCount p H ^ 2) ^ (n * m) := pow_mul _ _ _
    _ ≤ (144 * H ^ 2 * maxDivisorCount H ^ 2 * (positiveRatioSet p H).card) ^ (n * m) := hc
    _ = (144 * H ^ 2 * maxDivisorCount H ^ 2) ^ (n * m) * (positiveRatioSet p H).card ^ (n * m) :=
      mul_pow _ _ _
    _ ≤
        (144 * H ^ 2 * maxDivisorCount H ^ 2) ^ (n * m) *
          (quotientPowerConstant (H ^ (2 * m)) ^ (n ^ 2 * (m - 1)) * H ^ ((m - 1) * m) *
            (p - 1) ^ n) :=
      Nat.mul_le_mul_left _ hg
    _ = _ := by
      rw [congruenceCountPowerBound]; ring

/-- For positive natural r, a square energy bound E^2 at most A and count bound N^(2r) at
most B imply p*E*N less than k^2 whenever (p^2*A)^r*B is less than k^(4r).
Multiply the powered inequalities and compare positive natural powers. -/
theorem counting_budget_of_even_power {p k E N A B r : ℕ} (hr : 0 < r) (hE : E ^ 2 ≤ A)
    (hN : N ^ (2 * r) ≤ B) (hgap : (p ^ 2 * A) ^ r * B < k ^ (4 * r)) : p * E * N < k ^ 2 := by
  have he := Nat.pow_le_pow_left hE r
  have hm := Nat.mul_le_mul_left (p ^ (2 * r)) (Nat.mul_le_mul he hN)
  have hp : (p * E * N) ^ (2 * r) < (k ^ 2) ^ (2 * r) := by
    have hl : (p * E * N) ^ (2 * r) ≤ (p ^ 2 * A) ^ r * B := by
      simpa only [mul_pow, pow_mul, Nat.mul_assoc] using hm
    have heq : k ^ (4 * r) = (k ^ 2) ^ (2 * r) := by
      rw [← pow_mul]
      congr 1
      ring
    exact hl.trans_lt (hgap.trans_eq heq)
  exact (Nat.pow_lt_pow_iff_left (ne_of_gt (Nat.mul_pos (by decide : 0 < 2) hr))).mp hp

/-- For odd prime p and positive H,m,n satisfying subgroup injectivity, an explicit inequality
in p,H,m,n,k and divisor/logarithm losses yields p*E*fullCount less than k^2.
Combine the unconditional energy-square bound with the proved full congruence count estimate.
The former unknown-count premise is removed; absorbing the explicit losses remains separate. -/
theorem boundedCongruence_energy_budget_of_growth {p H m n k : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hH : 0 < H) (hm : 0 < m) (hn : 0 < n) (hmod : H ^ (2 * m) < p ^ 2)
    (hgap : (18874370 * p ^ 7) ^ (n * m) * congruenceCountPowerBound p H m n < k ^ (4 * (n * m))) :
    p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  apply
    counting_budget_of_even_power (Nat.mul_pos hn hm) (heilbronnEnergy_square_le_uniform hodd)
      (boundedCongruenceCount_power_le_growth_bound hodd hH hm hn hmod)
  have he : p ^ 2 * (18874370 * p ^ 5) = 18874370 * p ^ 7 := by ring
  simpa only [he] using hgap

end PseudoPrime.NumberTheory.Heilbronn
