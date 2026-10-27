/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterSensitiveExclusion
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors

/-! # Product and ramified-support estimates for character exclusion costs -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For nonzero factors, the exclusion cost of their product is at most the
sum of their costs. Prime supports form a union and the intersection cost is
nonnegative. This separates squarefree and square-factor contributions. -/
theorem characterExclusionCost_mul_le {f a b : ℕ} (χ : DirichletCharacter ℂ f) (ha : a ≠ 0)
    (hb : b ≠ 0) :
    characterExclusionCost χ (a * b) ≤ characterExclusionCost χ a + characterExclusionCost χ b := by
  unfold characterExclusionCost
  rw [Nat.primeFactors_mul ha hb]
  have he :=
    Finset.sum_union_inter (s₁ := a.primeFactors) (s₂ := b.primeFactors) (f := fun p : ℕ ↦
      (1 - (χ p).re) * Real.log p)
  have hz : 0 ≤ ∑ p ∈ a.primeFactors ∩ b.primeFactors, (1 - (χ p).re) * Real.log p :=
    Finset.sum_nonneg fun p _ ↦ mul_nonneg (character_defect_nonneg χ p) (Real.log_natCast_nonneg p)
  linarith only [he, hz]

/-- If chi vanishes at the prime divisors of nonzero d, its exclusion cost at d
is at most log d. Identify the defect with one and use the radical logarithm
bound. This charges ramified squarefree support only once. -/
theorem characterExclusionCost_le_log_of_zero {f d : ℕ} (χ : DirichletCharacter ℂ f) (hd : d ≠ 0)
    (hz : ∀ p ∈ d.primeFactors, χ p = 0) : characterExclusionCost χ d ≤ Real.log d := by
  have he : characterExclusionCost χ d = ∑ p ∈ d.primeFactors, Real.log p := by
    unfold characterExclusionCost
    apply Finset.sum_congr rfl
    intro p hp
    rw [hz p hp, Complex.zero_re]
    ring
  exact he.trans_le (sum_log_primeFactors_le_log hd)

/-- For nonzero s,d and a character vanishing on the prime support of d,
the cost at 2(s²d) is at most log(4d)+2sum over prime divisors of s of log p.
Separate products, discard repeated prime factors in the square, and bound two.
This supplies the arithmetic envelope for a square-factor witness bound. -/
theorem characterExclusionCost_square_factor_le {f s d : ℕ} (χ : DirichletCharacter ℂ f)
    (hs : s ≠ 0) (hd : d ≠ 0) (hz : ∀ p ∈ d.primeFactors, χ p = 0) :
    characterExclusionCost χ (2 * (s ^ 2 * d)) ≤
      Real.log ((4 * d : ℕ) : ℝ) + 2 * ∑ p ∈ s.primeFactors, Real.log p := by
  have hp := characterExclusionCost_mul_le χ (by decide : 2 ≠ 0) (mul_ne_zero (pow_ne_zero 2 hs) hd)
  have hsd := characterExclusionCost_mul_le χ (pow_ne_zero 2 hs) hd
  have htwo := characterExclusionCost_le_twice χ 2
  rw [Nat.prime_two.primeFactors, Finset.sum_singleton] at htwo
  norm_num only [Nat.cast_ofNat] at htwo
  have hsq : characterExclusionCost χ (s ^ 2) = characterExclusionCost χ s := by
    unfold characterExclusionCost
    rw [Nat.primeFactors_pow s (by decide : 2 ≠ 0)]
  have hsc := characterExclusionCost_le_twice χ s
  have hdc := characterExclusionCost_le_log_of_zero χ hd hz
  have hl : Real.log ((4 * d : ℕ) : ℝ) = 2 * Real.log 2 + Real.log d := by
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hd)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  rw [hsq] at hsd
  nlinarith only [hp, hsd, htwo, hsc, hdc, hl]

/-- For nonzero a,b, split the product exclusion cost into the full support of a
and the prime factors of b absent from a. This exact identity avoids charging
shared ramified primes twice in later negative-support estimates. -/
theorem characterExclusionCost_mul_eq_add_sdiff {f a b : ℕ} (χ : DirichletCharacter ℂ f)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    characterExclusionCost χ (a * b) =
      characterExclusionCost χ a +
        ∑ p ∈ b.primeFactors \ a.primeFactors, (1 - (χ p).re) * Real.log p := by
  unfold characterExclusionCost
  rw [Nat.primeFactors_mul ha hb, ← Finset.union_sdiff_self_eq_union,
    Finset.sum_union disjoint_sdiff_self_right]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
