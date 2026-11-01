/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPolePrimeTrivialNumerics
public import PseudoPrime.LLS.GammaNonOneComparison
public import PseudoPrime.LLS.PaperStatements.TwoPoleOddNonOneBounds

/-! # Odd non-one witnesses with the prime-two cost retained -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For a nonprincipal quadratic character at even nonzero level q, GRH and
ambient A at least q with log A at least 1700 give an odd prime non-one witness
through the shift-thirty-two affine cutoff. The spare unit in the two-pole
separation absorbs the prime-two logarithmic local cost. No input enumeration or
additional numerical separation hypothesis is required. -/
theorem exists_odd_prime_ne_one_le_twoPole_shift32 {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 1700 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log A + 32) ^ 2 ∧ χ p ≠ 1 := by
  let r := (500 / 821 : ℝ) * Real.log A + 32
  let x := r ^ 2
  have hD := twoPole_shifted_root_data hL (c := 32) (by norm_num only) (by norm_num only)
  have hx : 1 ≤ x := hD.1
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hr : 0 < r := by
    dsimp only [r]; linarith only [hL]
  have hs : Real.sqrt x = r := Real.sqrt_sq hr.le
  have hlocal : (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x ≤ 1 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hxpos)).mpr
    have ht := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
    rw [hs]
    have hroot : (3 / 5 : ℝ) * Real.log A + 18 ≤ r := hD.2.1
    have hlog : Real.log ((99 / 40 : ℝ) * x) ≤ Real.log A / 40 := hD.2.2.1
    linarith only [ht, hroot, hlog, hL]
  have hsep := twoPolePrimeTrivialSeparation_shift32_gt_one hL
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann hx
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann hx
  have hC := PaperStatements.gammaCharacterSum_re_le_twoPole_ambient χ hne hqA hGRH hx
  apply
    exists_odd_prime_ne_one_of_gamma_ramp_gap χ hquad h2 hxpos
      (show 1 ≤ (99 / 40 : ℝ) * x by nlinarith only [hx])
  dsimp only [twoPolePrimeTrivialSeparation] at hsep
  nlinarith only [hP, hT, hC, hsep, hlocal]

end PseudoPrime.LLS
