/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HalfScaleBudgetScaleSelection
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyScalarHalfScaleBudget

/-! # Uniform nonprincipal half-scale bounds away from exceptional conductors -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

open Classical in
/-- Every positive tolerance admits a polynomial exponent and height threshold chosen
before the level, finite nonprincipal character family, and time. For levels at most the
square root of the height parameter and avoiding the exceptional conductor divisors,
the actual sum of half-scale errors is at most the tolerance times time. The proof fixes
a strip below one, absorbs all explicit remainders, and chooses one exponent for both
the density scale and leading exponential error. Conductor four is included. -/
theorem exists_uniform_character_family_half_scale_bound :
    ∀ ε : ℝ,
      0 < ε →
        ∃ b : ℕ,
          1 ≤ b ∧
            ∃ R₀ : ℝ,
              4 ≤ R₀ ∧
                ∀ H : ℕ,
                  3 ≤ H →
                    R₀ ≤ ((H + 1 : ℕ) : ℝ) →
                    ∀ q : ℕ,
                      ∀ [NeZero q],
                        q ≤ H + 1 →
                          (q : ℝ) ≤ Real.sqrt ((H + 1 : ℕ) : ℝ) →
                          ∀ S : Finset (DirichletCharacter ℂ q),
                            (∀ χ ∈ S, χ ≠ 1) →
                              (∀
                                e ∈
                                  exceptionalFamilyConductorsAwayFromFour (H + 1)
                                    (1 - 1 / Real.log ((H + 1 : ℕ) : ℝ)),
                                ¬e ∣ q) →
                              ∀ x : ℝ,
                                ((H + 1 : ℕ) : ℝ) ^ b ≤ x →
                                  (∑ χ ∈ S,
                                      ‖Arithmetic.characterLogWeightedSum x χ -
                                          Arithmetic.characterLogWeightedSum (x / 2) χ‖) ≤
                                    ε * x := by
  intro ε hε
  obtain ⟨A, B, C, K, T, hA, hB, hC, hK, hT, hbudget⟩ :=
    exists_character_family_scalar_half_scale_budget
  let η := min (1 / 4 : ℝ) (1 / (4 * A))
  let σ := 1 - η
  have hη : 0 < η :=
    lt_min (by norm_num only) (one_div_pos.mpr (by nlinarith only [hA] : 0 < 4 * A))
  have hηquarter : η ≤ 1 / 4 := min_le_left _ _
  have hηA : η ≤ 1 / (4 * A) := min_le_right _ _
  have hσlo : (1 / 2 : ℝ) ≤ σ := by
    dsimp only [σ]; linarith only [hηquarter]
  have hσhi : σ < 1 := by
    dsimp only [σ]; linarith only [hη]
  have hstrip : A * (1 - σ) ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (by nlinarith only [hA] : 0 < 4 * A)).mp hηA
    dsimp only [σ]
    nlinarith only [hh]
  have hεthird : 0 < ε / 3 := div_pos hε (by norm_num only)
  obtain ⟨X, hX, hbound⟩ := hbudget (ε / 3) hεthird
  obtain ⟨b₀, hb₀, R₁, hR₁, habsorb⟩ :=
    exists_uniform_remainder_absorption_above_polynomial_scale hσlo hσhi hC.le hK.le hT.le hεthird
  obtain ⟨b, hb, hexp⟩ := exists_small_exponential_at_nat_scale hB hεthird (max (b₀ : ℝ) (4 * A))
  have hbb : b₀ ≤ b := by exact_mod_cast (le_max_left (b₀ : ℝ) (4 * A)).trans hb
  have hbA : 4 * A ≤ (b : ℝ) := (le_max_right (b₀ : ℝ) (4 * A)).trans hb
  refine ⟨b, hb₀.trans hbb, max R₁ X, hR₁.trans (le_max_left _ _), ?_⟩
  intro H hH hR q inst hq hsqrt S hne havoid x hx
  have hR₁H : R₁ ≤ ((H + 1 : ℕ) : ℝ) := (le_max_left R₁ X).trans hR
  have hXH : X ≤ ((H + 1 : ℕ) : ℝ) := (le_max_right R₁ X).trans hR
  have hRtwo : (2 : ℝ) ≤ ((H + 1 : ℕ) : ℝ) := by linarith only [hR₁.trans hR₁H]
  have hRx : ((H + 1 : ℕ) : ℝ) ≤ x := by
    have hp :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [hRtwo] : (1 : ℝ) ≤ ((H + 1 : ℕ) : ℝ))
        (by exact_mod_cast hb₀.trans hbb : (1 : ℝ) ≤ (b : ℝ))
    rw [Real.rpow_one, Real.rpow_natCast] at hp
    exact hp.trans hx
  have hlogs := polynomial_scale_log_bounds hRtwo hA.le hbA hx
  have hscale : 2 * A * Real.log ((H + 1 + 1 : ℕ) : ℝ) ≤ Real.log x := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlogs.1
  have hmain :=
    hbound 1 (by norm_num only) H ((by norm_num only : 2 ≤ (3 : ℕ)).trans hH) x σ (hXH.trans hRx)
      hσlo hσhi.le hstrip hscale q hq S hne havoid
  have hrem := habsorb b hbb H hH hR₁H q (NeZero.pos q) hq hsqrt x hx
  have hxp : 0 ≤ x := (by linarith only [hRtwo] : (0 : ℝ) ≤ ((H + 1 : ℕ) : ℝ)).trans hRx
  have hleading := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlogs.2) (mul_nonneg hB.le hxp)
  have he := mul_le_mul_of_nonneg_right hexp hxp
  nlinarith only [hmain, hrem, hleading, he]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
