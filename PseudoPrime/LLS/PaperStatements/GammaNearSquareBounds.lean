/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSignedPrefixBounds
public import PseudoPrime.LLS.GammaNearSquareNumerics

/-! # Coefficient 99/100 Miller-Rabin witnesses from logarithmic scale 1000 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH at q ≥ 20000 and log q ≥ 1000, every nonprincipal primitive
Gamma sum at x=(2/5)(log q)² is at most M log q+217/10.
The thirty-two-term zero certificate contributes 197/10; the near-square
pole and left budgets contribute at most 15/8 and 7/100.
This upper bound is uniform in the character and its conductor. -/
theorem gamma_primitiveCharacter_sum_re_le_nearSquare {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 1000 ≤ Real.log q) :
    let x := (2 / 5 : ℝ) * (Real.log q) ^ 2;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log q + 217 / 10 := by
  let x := (2 / 5 : ℝ) * (Real.log q) ^ 2
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (Real.log q - 1000)]
  have he := nearSquare_gamma_error_budgets hL
  have hu :=
    gamma_primitiveCharacter_sum_re_le_conductor_free_prefix hq χ hne hGRH hx 32
      Analysis.gammaResolvent_thirtyTwo_error_lt
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hf : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hmqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hmq
  have hlead :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hf hmqR)
      (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  linarith only [hu, hlead, he.1, he.2.2.2.1]

end PseudoPrime.LLS.PaperStatements
