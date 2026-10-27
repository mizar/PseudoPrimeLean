/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.FixedConductorCardinality
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveHalfScaleTransfer
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalFixedModulusHalfSum

/-! # Uniform half-scale errors for families induced from conductor four -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For any positive error rate, one threshold works for every finite
nonprincipal family at any nonzero level whose primitive conductors are all four.
Its aggregate half-scale norm is at most the requested linear error plus the
explicit level-change correction. Injective primitive labels bound the number of
such characters by the fixed number modulo four; apply the fixed-modulus limit
at a correspondingly smaller error rate. The leading error is independent of the
ambient modulus and no quantitative zero-free region for conductor four is assumed. -/
theorem exists_uniform_induced_conductor_four_half_sum_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ,
      2 ≤ X ∧
        ∀ (q : ℕ) [NeZero q],
          ∀ S : Finset (DirichletCharacter ℂ q),
            (∀ χ ∈ S, χ ≠ 1) →
              (∀ χ ∈ S, χ.conductor = 4) →
              ∀ x : ℝ,
                X ≤ x →
                  (∑ χ ∈ S,
                      ‖Arithmetic.characterLogWeightedSum x χ -
                          Arithmetic.characterLogWeightedSum (x / 2) χ‖) ≤
                    ε * x + (S.card : ℝ) * ((q.primeFactors.card : ℝ) * (Real.log x) ^ 2) := by
  classical
  let N : ℝ := Fintype.card (DirichletCharacter ℂ 4)
  have hN : 0 < N + 1 := by
    dsimp only [N]
    linarith only [(Nat.cast_nonneg (Fintype.card (DirichletCharacter ℂ 4)) :
        (0 : ℝ) ≤ Fintype.card (DirichletCharacter ℂ 4))]
  let δ : ℝ := ε / (N + 1)
  have hδ : 0 < δ := div_pos hε hN
  obtain ⟨X, hX, hfour⟩ := exists_uniform_conductor_four_half_sum_bound hδ
  refine ⟨max 2 X, le_max_left _ _, ?_⟩
  intro q inst S hne hcon x hx
  have hx2 : 2 ≤ x := (le_max_left 2 X).trans hx
  have hxX : X ≤ x := (le_max_right 2 X).trans hx
  have hsource (χ : DirichletCharacter ℂ q) (hχ : χ ∈ S) :
    ‖Arithmetic.characterLogWeightedSum x χ.primitiveCharacter -
          Arithmetic.characterLogWeightedSum (x / 2) χ.primitiveCharacter‖ ≤
      δ * x := by
    have htransport :
      ∀ (d : ℕ),
        d = 4 →
          ∀ ψ : DirichletCharacter ℂ d,
            ψ.IsPrimitive →
              ψ ≠ 1 →
              ‖Arithmetic.characterLogWeightedSum x ψ -
                    Arithmetic.characterLogWeightedSum (x / 2) ψ‖ ≤
                δ * x := by
      intro d hd
      subst d
      exact hfour x hxX
    exact
      htransport χ.conductor (hcon χ hχ) χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
        (Arithmetic.primitiveCharacter_ne_one_of_ne_one (hne χ hχ))
  have hcard : (S.card : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast Arithmetic.card_character_family_of_fixed_conductor_le S 4 hcon
  have hm := mul_le_mul_of_nonneg_right (hcard.trans (le_add_of_nonneg_right zero_le_one)) hδ.le
  have hδeq : δ * (N + 1) = ε := div_mul_cancel₀ _ hN.ne'
  have hscalar : (S.card : ℝ) * δ ≤ ε := by nlinarith only [hm, hδeq]
  have hs :=
    Finset.sum_le_sum (s := S)
      (fun χ hχ ↦
        (Arithmetic.norm_characterLogWeightedSum_half_le_primitive_add_level_error χ hx2).trans
          (add_le_add (hsource χ hχ) le_rfl))
  rw [Finset.sum_const, nsmul_eq_mul] at hs
  have hsmall := mul_le_mul_of_nonneg_right hscalar (by linarith only [hx2] : 0 ≤ x)
  nlinarith only [hs, hsmall]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
