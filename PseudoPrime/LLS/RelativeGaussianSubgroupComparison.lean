/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RelativeGaussianPrincipalBounds
public import PseudoPrime.LLS.GaussianConstantSubgroupComparison

/-! # Relative-loss Gaussian subgroup comparison -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, q at least 20000, x at least 4, and relative width in (0,1/2],
absence of subgroup witnesses forces the actual Gaussian cutoff comparison.
Assume every prime divisor exceeds the cutoff, so the finite principal sum is
level one. Combine the relative lower error with the constant principal upper
error, retaining the conductor sum and ambient error for later normalization. -/
theorem gaussian_noSmallPrimes_inequality_relative {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {h x lambda : ℝ} (hh : 0 < h) (hh1 : h ≤ 1 / 2) (hx : 4 ≤ x) (hl : 0 ≤ lambda)
    (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊lambda * x⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p) :
    ((H.index : ℝ) * (1 - h) *
            (∫ u in (0 : ℝ)..lambda, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * subgroupConductorLogSum H +
        (H.index : ℝ) *
          (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
        13 +
        ((H.index - 1 : ℕ) : ℝ) * gaussianAmbientError q x := by
  have hlo :=
    gaussian_level_one_sum_lower_relative hGRH.riemann hh hh1
      ((by norm_num only : (0 : ℝ) < 4).trans_le hx) hl
  have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg H.index)
  have hhi :=
    gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes_constant_principal hq H hGRH hx
      hsmall
  have he : Finset.Icc 1 ⌊lambda * x⌋₊ = Finset.Ioc 0 ⌊lambda * x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  rw [he, ← Complex.re_sum,
    MellinKernel.principal_sum_eq_level_one_of_no_small_prime_divisor gaussianGammaMellinKernel
      (q := q) x hdiv,
    Complex.re_sum] at hhi
  nlinarith only [hm, hhi]

/-- Under the same relative Gaussian hypotheses, if the prime cutoff reaches
50000 then the transferred prefix lowers the ambient additive error. -/
theorem gaussian_noSmallPrimes_inequality_relative_prefix_gain {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {h x lambda : ℝ} (hh : 0 < h) (hh1 : h ≤ 1 / 2) (hx : 4 ≤ x) (hl : 0 ≤ lambda)
    (hX : 50000 ≤ lambda * x) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊lambda * x⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p) :
    ((H.index : ℝ) * (1 - h) *
            (∫ u in (0 : ℝ)..lambda, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * subgroupConductorLogSum H +
        (H.index : ℝ) *
          (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
        13 +
        ((H.index - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefix q x := by
  have hlo :=
    gaussian_level_one_sum_lower_relative hGRH.riemann hh hh1
      ((by norm_num only : (0 : ℝ) < 4).trans_le hx) hl
  have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg H.index)
  have hhi :=
    gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes_constant_principal_prefix_gain hq H
      hGRH hx hX hdiv hsmall
  have he : Finset.Icc 1 ⌊lambda * x⌋₊ = Finset.Ioc 0 ⌊lambda * x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  rw [he, ← Complex.re_sum,
    MellinKernel.principal_sum_eq_level_one_of_no_small_prime_divisor gaussianGammaMellinKernel
      (q := q) x hdiv,
    Complex.re_sum] at hhi
  nlinarith only [hm, hhi]

/-- The relative-width comparison with the signed 50000-prefix error. -/
theorem gaussian_noSmallPrimes_inequality_relative_prefix_gain_signed {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h x lambda : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1 / 2) (hx : 4 ≤ x) (hl : 0 ≤ lambda) (hX : 50000 ≤ lambda * x)
    (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊lambda * x⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p) :
    ((H.index : ℝ) * (1 - h) *
            (∫ u in (0 : ℝ)..lambda, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * subgroupConductorLogSum H +
        (H.index : ℝ) *
          (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
        13 +
        ((H.index - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefixSigned q x := by
  have hlo :=
    gaussian_level_one_sum_lower_relative hGRH.riemann hh hh1
      ((by norm_num only : (0 : ℝ) < 4).trans_le hx) hl
  have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg H.index)
  have hhi := gaussian_principal_sum_le_noSmall_prefix_signed hq H hGRH hx hX hdiv hsmall
  have he : Finset.Icc 1 ⌊lambda * x⌋₊ = Finset.Ioc 0 ⌊lambda * x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  rw [he, ← Complex.re_sum,
    MellinKernel.principal_sum_eq_level_one_of_no_small_prime_divisor gaussianGammaMellinKernel
      (q := q) x hdiv,
    Complex.re_sum] at hhi
  nlinarith only [hm, hhi]

/-- Under the same relative Gaussian hypotheses, a cutoff of at least 1000
uses the transferred 1000-prefix gain in the ambient error. -/
theorem gaussian_noSmallPrimes_inequality_relative_prefix1000_gain {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h x lambda : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1 / 2) (hx : 4 ≤ x) (hl : 0 ≤ lambda) (hX : 1000 ≤ lambda * x)
    (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊lambda * x⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p) :
    ((H.index : ℝ) * (1 - h) *
            (∫ u in (0 : ℝ)..lambda, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * subgroupConductorLogSum H +
        (H.index : ℝ) *
          (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
        13 +
        ((H.index - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefix1000 q x := by
  have hlo :=
    gaussian_level_one_sum_lower_relative hGRH.riemann hh hh1
      ((by norm_num only : (0 : ℝ) < 4).trans_le hx) hl
  have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg H.index)
  have hhi :=
    gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes_constant_principal_prefix1000_gain hq
      H hGRH hx hX hdiv hsmall
  have he : Finset.Icc 1 ⌊lambda * x⌋₊ = Finset.Ioc 0 ⌊lambda * x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  rw [he, ← Complex.re_sum,
    MellinKernel.principal_sum_eq_level_one_of_no_small_prime_divisor gaussianGammaMellinKernel
      (q := q) x hdiv,
    Complex.re_sum] at hhi
  nlinarith only [hm, hhi]

end PseudoPrime.LLS.PaperStatements
