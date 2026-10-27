/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GaussianPrincipalEulerBudget
public import PseudoPrime.LLS.GaussianGammaPrefixTransfer

/-! # LLS-specific prefix gains for Gaussian zero mass -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- If a primitive character is trivial throughout the 50000 prefix, transfer
the Gamma prefix lower bound to reduce the Gaussian zero-mass additive constant
from 12871/1000 to 159169/50000. -/
theorem gaussian_zeroMass_add_pairedTail_lt_prefix_gain {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hRiemann : RiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 50000 → χ p = 1) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) +
        Analysis.gaussianPairedEulerTail χ (Finset.Ioc 0 (50000 : ℕ)) <
      (20115621 / 50000000 : ℝ) * Real.log q + 159169 / 50000 := by
  let B := Finset.Ioc 0 (50000 : ℕ)
  have h := gaussian_zeroMass_add_pairedTail_lt_principal_prefix hq hRH hRiemann hp hne hinv B
  have hprefix := PseudoPrime.LLS.gaussian_prefix50000_lower hRiemann (le_refl (50000 : ℝ))
  have hfloor : ⌊(50000 : ℝ)⌋₊ = (50000 : ℕ) := Nat.floor_natCast 50000
  rw [hfloor] at hprefix
  have htrivB : ∑ m ∈ B, (1 - (χ m).re) * Analysis.gaussianResolventMangoldtWeight m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    by_cases hΛ : ArithmeticFunction.vonMangoldt m = 0
    · simp only [Analysis.gaussianResolventMangoldtWeight, hΛ, zero_mul, mul_zero]
    · obtain ⟨p, r, hp, hr, rfl⟩ :=
        (isPrimePow_nat_iff (n := m)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
      have hpbound : (p : ℝ) ≤ 50000 := by
        calc
          (p : ℝ) ≤ (p ^ r : ℕ) := by exact_mod_cast Nat.le_pow hr
          _ ≤ 50000 := by exact_mod_cast (Finset.mem_Ioc.mp hm).2
      simp only [Analysis.gaussianResolventMangoldtWeight, Nat.cast_pow, map_pow,
        hsmall p hp hpbound, one_pow, Complex.one_re, sub_self, zero_mul]
  have hsum := hprefix
  dsimp only [B] at hsum h
  rw [htrivB, add_zero] at h
  have hsum' :
    (484381 / 100000 : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 (50000 : ℕ), Analysis.gaussianResolventMangoldtWeight m := by
    norm_num only at hsum
    exact hsum
  have hconst :
    (20115621 / 50000000 : ℝ) * Real.log q + 12871 / 1000 -
        2 * (∑ m ∈ Finset.Ioc 0 (50000 : ℕ), Analysis.gaussianResolventMangoldtWeight m) ≤
      (20115621 / 50000000 : ℝ) * Real.log q + 159169 / 50000 := by
    nlinarith only [hsum']
  exact lt_of_lt_of_le h hconst

/-- If a primitive character is trivial throughout the 1000 prefix, transfer
the Gaussian prefix lower bound to reduce the additive constant to 5969/1000. -/
theorem gaussian_zeroMass_add_pairedTail_lt_prefix1000_gain {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hRiemann : RiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 1000 → χ p = 1) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) +
        Analysis.gaussianPairedEulerTail χ (Finset.Ioc 0 (1000 : ℕ)) <
      (20115621 / 50000000 : ℝ) * Real.log q + 5969 / 1000 := by
  let B := Finset.Ioc 0 (1000 : ℕ)
  have h := gaussian_zeroMass_add_pairedTail_lt_principal_prefix hq hRH hRiemann hp hne hinv B
  have hprefix := PseudoPrime.LLS.gaussian_prefix1000_lower hRiemann (le_refl (1000 : ℝ))
  have hfloor : ⌊(1000 : ℝ)⌋₊ = (1000 : ℕ) := Nat.floor_natCast 1000
  rw [hfloor] at hprefix
  have htrivB : ∑ m ∈ B, (1 - (χ m).re) * Analysis.gaussianResolventMangoldtWeight m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    by_cases hΛ : ArithmeticFunction.vonMangoldt m = 0
    · simp only [Analysis.gaussianResolventMangoldtWeight, hΛ, zero_mul, mul_zero]
    · obtain ⟨p, r, hp, hr, rfl⟩ :=
        (isPrimePow_nat_iff (n := m)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
      have hpbound : (p : ℝ) ≤ 1000 := by
        calc
          (p : ℝ) ≤ (p ^ r : ℕ) := by exact_mod_cast Nat.le_pow hr
          _ ≤ 1000 := by exact_mod_cast (Finset.mem_Ioc.mp hm).2
      simp only [Analysis.gaussianResolventMangoldtWeight, Nat.cast_pow, map_pow,
        hsmall p hp hpbound, one_pow, Complex.one_re, sub_self, zero_mul]
  have hsum := hprefix
  dsimp only [B] at hsum h
  rw [htrivB, add_zero] at h
  have hsum' :
    (3451 / 1000 : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 (1000 : ℕ), Analysis.gaussianResolventMangoldtWeight m := by
    norm_num only at hsum
    exact hsum
  have hconst :
    (20115621 / 50000000 : ℝ) * Real.log q + 12871 / 1000 -
        2 * (∑ m ∈ Finset.Ioc 0 (1000 : ℕ), Analysis.gaussianResolventMangoldtWeight m) ≤
      (20115621 / 50000000 : ℝ) * Real.log q + 5969 / 1000 := by
    nlinarith only [hsum']
  exact lt_of_lt_of_le h hconst

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
