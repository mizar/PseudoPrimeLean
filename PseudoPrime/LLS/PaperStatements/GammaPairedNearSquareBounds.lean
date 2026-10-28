/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSignedPrefixBounds
public import PseudoPrime.LLS.GammaPairedNearSquareNegativeBounds

/-! # Prime MR rejecting witnesses from log 700 with paired ramp errors -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH at q at least 20000 and log q at least 700, every nonprincipal
primitive Gamma sum at x=(2/5)(log q) squared is at most M log q+22.
Enlarge the actual conductor in the paired upper bound only after the
primitive comparison. This supplies a common upper bound for MR extraction. -/
theorem gamma_primitiveCharacter_sum_re_le_paired_nearSquare {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 700 ≤ Real.log q) :
    let x := (2 / 5 : ℝ) * (Real.log q) ^ 2;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log q + 22 := by
  have hu :=
    gamma_primitiveCharacter_sum_re_le_paired_nearSquare_conductor hq χ hne hGRH hL
      (by linarith only : Real.log q ≤ Real.log q + 7 / 5)
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hf : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hmqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hmq
  have hlead :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hf hmqR)
      (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  linarith only [hu, hlead]

end PseudoPrime.LLS.PaperStatements
