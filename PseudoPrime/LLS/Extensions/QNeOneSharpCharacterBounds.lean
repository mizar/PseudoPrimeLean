/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.QNeOneSharpLowerBounds

/-! # Connecting the sharp small-scale separation to actual character sums -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- Input: the Riemann lower bound and a half-square defect with an additional correction c.
Claim: the actual character sum plus c dominates the sharp lower envelope.
Proof: transfer the Riemann bound through the defect and retain the sharper constants.
This single interface supplies the zero, one and corrected negative-one branches. -/
theorem qNeOneSharpLowerBound_le_corrected_sum {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f)
    (hriemann : LLSRiemannWeightedLowerBound) {y c : ℝ} (hy : 8 ≤ y)
    (hd : weightedLogDefect ψ (y ^ 2) ≤ (Real.log (y ^ 2)) ^ 2 / 2 + c) :
    qNeOneSharpLowerBound y ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) ψ).re + c := by
  have hx := Analysis.sq_ge_64_of_ge_8 hy
  have hs :=
    re_characterLogWeightedSum_ge_of_defect_le hriemann ψ
      (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 64) hx) hd
  have hl := qNeOneSharpLowerBound_le_riemann_lower hy
  linarith only [hs, hl]

/-- Input: GRH, an even primitive inducing character, y at least 99/10,
conductor bounds for the ramified and unramified branches, and three-valuedness at two.
Claim: the primitive character cannot be one on the required odd primes.
Proof: use the appropriate core and the all-scale sharp separation for each value at two.
This is an analytic character contradiction independent of finite input certificates. -/
theorem not_oddPrimeTrivial_of_sharp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hne : χ ≠ 1) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : (99 / 10 : ℝ) ≤ y)
    (hlog4 : Real.log χ.conductor ≤ y + Real.log 4)
    (hlogOdd : χ.primitiveCharacter 2 ≠ 0 → Real.log χ.conductor ≤ y)
    (hcases :
      χ.primitiveCharacter 2 = 0 ∨ χ.primitiveCharacter 2 = 1 ∨ χ.primitiveCharacter 2 = -1) :
    ¬OddPrimeTrivial χ (y ^ 2) := by
  intro hodd
  have h8 : 8 ≤ y := by linarith only [hy]
  have hx := Analysis.sq_ge_64_of_ge_8 h8
  have hriemann := llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann
  have hreciprocal := llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann
  have hsep := qNeOneCommonUpperBound_lt_sharp hy
  rcases hcases with h2 | h2 | h2
  · have hcore := weightedComparisonCore_even_zero χ hne heven hGRH hx hodd h2
    have hl :=
      qNeOneSharpLowerBound_le_corrected_sum χ.primitiveCharacter hriemann h8 (c := 0)
        (by simpa only [add_zero] using hcore.logDefect_le)
    have hu :=
      (primitiveLogWeightedBounds_of_qneOne_zero_branch_even_star χ hne heven hGRH h8 hlog4 hriemann
          hreciprocal hodd h2).2
    simp only [add_zero] at hl
    exact (not_lt_of_ge (hl.trans (hu.trans (le_max_left _ _)))) hsep
  · have hcore := weightedComparisonCore_even_one χ hne heven hGRH hx hodd h2
    have hl :=
      qNeOneSharpLowerBound_le_corrected_sum χ.primitiveCharacter hriemann h8 (c := 0)
        (by simpa only [add_zero] using hcore.logDefect_le)
    have hlog :=
      hlogOdd
        (by
          rw [h2]; norm_num only)
    have hu :=
      (primitiveLogWeightedBounds_of_qneOne_one_branch_even_common χ hne heven hGRH h8 hlog hriemann
          hreciprocal hodd h2).2
    simp only [add_zero] at hl
    exact (not_lt_of_ge (hl.trans hu)) hsep
  · have hcore := weightedComparisonCore_even_neg_one χ hne heven hGRH hx hodd h2
    have hd :
      weightedLogDefect χ.primitiveCharacter (y ^ 2) ≤
        (Real.log (y ^ 2)) ^ 2 / 2 + Analysis.logTwoSquareCorrection y := by
      simpa only [Analysis.logTwoSquareCorrection, Real.log_pow, Nat.cast_ofNat] using
        hcore.logDefect_le
    have hl := qNeOneSharpLowerBound_le_corrected_sum χ.primitiveCharacter hriemann h8 hd
    have hlog :=
      hlogOdd
        (by
          rw [h2]; norm_num only)
    have hu :=
      (primitiveLogWeightedBounds_of_qneOne_neg_one_branch_corrected_star χ hne heven hGRH h8 hlog
          hriemann hreciprocal hodd h2).2
    exact (not_lt_of_ge (hl.trans (hu.trans (le_max_left _ _)))) hsep

end PseudoPrime.LLS.Extensions
