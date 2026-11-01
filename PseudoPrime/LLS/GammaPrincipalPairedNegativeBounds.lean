/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaPrincipalPairedNumerics
public import PseudoPrime.LLS.GammaNearSquareNegativeBounds
public import PseudoPrime.LLS.PaperStatements.GammaNearSquareNegativeBounds
public import PseudoPrime.LLS.PaperStatements.GammaPrincipalEulerCharacterBounds
public import PseudoPrime.LLS.PaperStatements.GammaPrincipalPairedNegativeBounds

/-! # Negative witnesses from log 550 using principal Euler positivity -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, odd original input, a nonprincipal quadratic level-4n
character, ambient level at least 20000 and L at least 550 with the stated
level bound, prime triviality through (99/100)L squared is impossible.
Combine the actual paired ramp lower bound, primitive upper bound and signed
conductor absorption. The whole-half-line numerical gap is proved here. -/
theorem not_primeTrivial_principalPaired_GRH {n : ℕ} (hn : Odd n) (χ : DirichletCharacter ℂ (4 * n))
    (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hq : 20000 ≤ 4 * n) {L : ℝ} (hL : 550 ≤ L)
    (hlogq : Real.log (4 * n : ℕ) ≤ L + 7 / 5)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ¬(∀ p : ℕ,
        p.Prime → ¬p ∣ 4 * n → (p : ℝ) ≤ (99 / 40 : ℝ) * ((2 / 5 : ℝ) * L ^ 2) → χ p = 1) := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  let x := (2 / 5 : ℝ) * L ^ 2
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 550)]
  intro hsmall
  have hQ := gamma_ramp_no_witness_comparison χ hquad (zero_lt_one.trans_le hx) hsmall
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann hx
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann hx
  have hC := PaperStatements.gammaCharSum_principalPaired_conductor_GRH hq χ hne hGRH hL hlogq
  have hE := gammaQuadraticCorrection_nearSquare_20 hn χ hquad hq (by linarith only [hL]) hlogq
  have he := gamma_principal_paired_nearSquare_budgets hL
  nlinarith only [hQ, hP, hT, hC, hE, he.1, he.2.1, he.2.2, hL]

end PseudoPrime.LLS
