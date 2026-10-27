/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaPrincipalPairedNumerics
public import PseudoPrime.LLS.GammaNearSquareNegativeBounds
public import PseudoPrime.LLS.GammaPrincipalEulerCharacterBounds

/-! # Negative witnesses from log 550 using principal Euler positivity -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH at ambient level q at least 20000, scale x=(2/5)L squared,
L at least 550 and log q at most L+7/5, the primitive Gamma sum is at most
M log(conductor)+277/20. Keep the actual conductor and combine the signed
principal Euler bound, pole cost and conductor-free left cost.
This is the conductor-retaining upper input for the paired comparison. -/
theorem gamma_primitiveCharacter_sum_re_le_principal_paired_nearSquare_conductor {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 550 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log χ.conductor + 277 / 20 := by
  let x := (2 / 5 : ℝ) * L ^ 2
  have hL0 : 0 < L := by linarith only [hL]
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 550)]
  have hx1 : 1 ≤ x := le_trans (by norm_num only) hx
  have hx0 := zero_lt_one.trans_le hx1
  have hs := Real.sqrt_pos.mpr hx0
  have hroot : (63 / 100 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx0.le).mpr
    dsimp only [x]
    nlinarith only [sq_nonneg L]
  have hd :=
    rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 1) (by norm_num only)
      (by
        norm_num only; exact hx1)
  simp only [one_mul] at hd
  have hleft : 43 * x ^ (-9 / 16 : ℝ) ≤ 3 / 20 := by
    have hm := mul_le_mul_of_nonneg_left hd (by norm_num only : (0 : ℝ) ≤ 43)
    have hh : 43 * (1 / Real.sqrt x) ≤ (3 / 20 : ℝ) := by
      rw [mul_one_div, div_le_iff₀ hs]
      linarith only [hroot, hL]
    exact hm.trans hh
  have hpole : ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x ≤ 2 := by
    rw [div_le_iff₀ hs]
    linarith only [hlogq, hroot, hL]
  have hu := gamma_primitiveCharacter_sum_re_lt_principal_euler hq χ hne hGRH hx
  linarith only [hu, hleft, hpole]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under GRH, odd original input, a nonprincipal quadratic level-4n
character, ambient level at least 20000 and L at least 550 with the stated
level bound, prime triviality through (99/100)L squared is impossible.
Combine the actual paired ramp lower bound, primitive upper bound and signed
conductor absorption. The whole-half-line numerical gap is proved here. -/
theorem gamma_ramp_prime_trivial_false_principal_paired_nearSquare_endpoint {n : ℕ} (hn : Odd n)
    (χ : DirichletCharacter ℂ (4 * n)) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hq : 20000 ≤ 4 * n)
    {L : ℝ} (hL : 550 ≤ L) (hlogq : Real.log (4 * n : ℕ) ≤ L + 7 / 5)
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
  have hC :=
    PaperStatements.gamma_primitiveCharacter_sum_re_le_principal_paired_nearSquare_conductor hq χ
      hne hGRH hL hlogq
  have hE :=
    gammaQuadraticLocalCorrection_absorbed_nearSquare_of_twenty_le hn χ hquad hq
      (by linarith only [hL]) hlogq
  have he := gamma_principal_paired_nearSquare_budgets hL
  nlinarith only [hQ, hP, hT, hC, hE, he.1, he.2.1, he.2.2, hL]

end PseudoPrime.LLS
