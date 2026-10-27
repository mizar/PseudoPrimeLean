/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.HalfScaleThetaSupply
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyUniformHalfScale

/-! # Polynomial-height theta supply with an explicit scalar budget -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

open Classical in
open DirichletLFunction in
/-- A positive tolerance fixes a polynomial exponent, height threshold, and principal
threshold before the modulus and residue. Avoiding the exceptional conductors now supplies
the half-scale hypothesis unconditionally; only the displayed scalar budget and endpoint
scale conditions remain to obtain the progression theta lower bound. -/
theorem exists_uniform_polynomial_half_scale_theta_threshold :
    ∀ ε : ℝ,
      0 < ε →
        ∃ b : ℕ,
          1 ≤ b ∧
            ∃ R₀ X : ℝ,
              4 ≤ R₀ ∧
                1 ≤ X ∧
                ∀ H : ℕ,
                  3 ≤ H →
                    R₀ ≤ ((H + 1 : ℕ) : ℝ) →
                    ∀ q a : ℕ,
                      ∀ [NeZero q],
                        Nat.Coprime a q →
                          q ≤ H + 1 →
                          (q : ℝ) ≤ Real.sqrt ((H + 1 : ℕ) : ℝ) →
                          (∀
                            e ∈
                              LogFreeDensity.exceptionalFamilyConductorsAwayFromFour
                                (H + 1) (1 - 1 / Real.log ((H + 1 : ℕ) : ℝ)),
                            ¬e ∣ q) →
                          ∀ x : ℝ,
                            X ≤ x →
                              ((H + 1 : ℕ) : ℝ) ^ b ≤ 4 * x / 5 →
                              (1 / 2 : ℝ) * q.primeFactors.card * (Real.log x) ^ 2 +
                                  (4 * ε * x +
                                    2 *
                                      (((Finset.univ : Finset (DirichletCharacter ℂ q)).erase
                                            1).card :
                                        ℝ) *
                                      ((Real.log 4 + 4) * (2 * ((H + 1 : ℕ) : ℝ) ^ b) *
                                        Real.log (2 * ((H + 1 : ℕ) : ℝ) ^ b))) +
                                  18 * (q.totient : ℝ) * Real.sqrt x * Real.log (5 / 4) ≤
                                (1 / 32 : ℝ) * x * Real.log (5 / 4) →
                              x / (2 * (q.totient : ℝ)) ≤ thetaInProgressionReal x q a := by
  intro ε hε
  obtain ⟨b, hb, R₀, hR₀, hhalf⟩ :=
    DirichletLFunction.LogFreeDensity.exists_uniform_character_family_half_scale_bound ε hε
  obtain ⟨X, hX, htheta⟩ := exists_uniform_half_scale_theta_threshold
  refine ⟨b, hb, R₀, X, hR₀, hX, ?_⟩
  intro H hH hR q a inst ha hq hsqrt havoid x hx hLx hbudget
  have hRone : (1 : ℝ) ≤ ((H + 1 : ℕ) : ℝ) := by linarith only [hR₀.trans hR]
  apply htheta q a ha ε (((H + 1 : ℕ) : ℝ) ^ b) x hε.le (one_le_pow₀ hRone) hx hLx
  · intro t ht
    exact
      hhalf H hH hR q hq hsqrt ((Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1)
        (fun χ hχ ↦ (Finset.mem_erase.mp hχ).1) havoid t ht
  · exact hbudget

end PseudoPrime.AnalyticNumberTheory.AGP
