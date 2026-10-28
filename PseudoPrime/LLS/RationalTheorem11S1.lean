/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RefinedTheorem11S1
public import PseudoPrime.Analysis.RationalPart1Separation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorSplitBounds
public import PseudoPrime.LLS.RationalTheorem11S13

/-! # Rational Part 1 radius and universal logarithmic profile -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, every nonprincipal character at q ≥ 3000 has a coprime prime
with non-one value through (log q+(1791/250)log log q+499/250)².
Compare the nonnegative rational radius roots and transfer the existing witness.
This realizes the rational triple (1,1791/250,499/250) at starting value 3000. -/
theorem exists_prime_character_ne_one_le_rationalProfile3000 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 3000 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        χ p ≠ 1 ∧
        (p : ℝ) ≤ (Real.log q + (1791 / 250 : ℝ) * Real.log (Real.log q) + 499 / 250) ^ 2 := by
  have hq0 : q ≠ 0 := Nat.ne_zero_of_lt ((by decide : (0 : ℕ) < 3000).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  obtain ⟨p, hp, hd, hv, hb⟩ := exists_prime_character_ne_one_le_rationalRadius χ hq hne hGRH
  have hR := rationalRadiusRoot_le_logarithmic_shift hq
  have hR0 : 0 ≤ rationalRadiusRoot q := by
    unfold rationalRadiusRoot
    have hL := Analysis.eight_lt_log_level hq
    have hB : 0 ≤ rationalCorrectionTerm q := le_max_left _ _
    linarith only [hL, hB]
  exact ⟨p, hp, hd, hv, hb.trans ((sq_le_sq₀ hR0 (hR0.trans hR)).mpr hR)⟩

end PseudoPrime.LLS
