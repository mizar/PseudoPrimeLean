/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GaussianPrincipalEulerBudget

/-! # Signed Gaussian prefix comparison with arbitrary certified cutoff mass -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

variable {N : ℕ} {P : ℝ}

/-- Given a certified Gaussian prefix mass and triviality on its prime bases,
transfer the signed prefix gain through this comparison, retaining the exact conductor coefficient.
The result is used by the next stage of the constant-principal MR comparison. -/
theorem gaussian_zeroMass_prefix_lt
    (hprefix : P ≤ ∑ n ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight n) {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hRiemann : RiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ N → χ p = 1) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) +
        Analysis.gaussianPairedEulerTail χ (Finset.Ioc 0 (N : ℕ)) <
      (20115621 / 50000000 : ℝ) * Real.log q + (12871 / 1000 - 2 * P) := by
  let B := Finset.Ioc 0 (N : ℕ)
  have h := gaussian_zeroMass_add_pairedTail_lt_principal_prefix hq hRH hRiemann hp hne hinv B
  have htrivB : ∑ m ∈ B, (1 - (χ m).re) * Analysis.gaussianResolventMangoldtWeight m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    by_cases hΛ : ArithmeticFunction.vonMangoldt m = 0
    · simp only [Analysis.gaussianResolventMangoldtWeight, hΛ, zero_mul, mul_zero]
    · obtain ⟨p, r, hp, hr, rfl⟩ :=
        (isPrimePow_nat_iff (n := m)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
      have hpbound : (p : ℝ) ≤ N := by
        calc
          (p : ℝ) ≤ (p ^ r : ℕ) := by exact_mod_cast Nat.le_pow hr
          _ ≤ N := by exact_mod_cast (Finset.mem_Ioc.mp hm).2
      simp only [Analysis.gaussianResolventMangoldtWeight, Nat.cast_pow, map_pow,
        hsmall p hp hpbound, one_pow, Complex.one_re, sub_self, zero_mul]
  dsimp only [B] at h
  rw [htrivB, add_zero] at h
  linarith only [h, hprefix]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
