/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeNonOneBounds
public import PseudoPrime.LLS.GammaPrincipalEulerCharacterBounds
public import PseudoPrime.LLS.GammaRetainedCommonCostBounds
public import PseudoPrime.LLS.GammaPrincipalEulerNonOneBounds3

/-! # Non-one witnesses from retained real-axis Euler budgets -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH for nonprincipal χ at level q ≥ 20000 and x ≥ 2, a cap C on the sum
of principal Euler mass and the primitive signed Gamma cost gives the displayed
conductor-retaining arithmetic bound. Use the empty signed prefix and the completed
remainder. This transports any improved common cost without fixing parity or a certificate. -/
theorem gamma_primitiveCharacter_sum_re_lt_common_euler_cost {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C : ℝ} (hx : 2 ≤ x)
    (hCost :
      (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) +
          gammaSignedGammaCost χ.primitiveCharacter.gammaFactor <
        C) :
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re <
      (11783423 / 25000000 : ℝ) * Real.log χ.conductor + C +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hz :=
    AnalyticNumberTheory.DirichletLFunction.gammaResolvent_zeroMass_le_signed_prefix
      (le_trans (by norm_num only : (2 : ℕ) ≤ 3) hm) (hGRH _ χ.primitiveCharacter hp) hp hnp
      (inv_ne_one.mpr hnp) ∅
  have hu :=
    gamma_primitive_sum_re_le_resolvent_conductor_free hq hm hmq hGRH hp hnp (inv_ne_one.mpr hnp) hx
  simp only [Finset.sum_empty, mul_zero, sub_zero, add_zero] at hz
  dsimp only [gammaSignedGammaCost] at hCost
  linarith only [hz, hu, hCost]

end PseudoPrime.LLS.PaperStatements
