/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneNumerics

/-! # Coefficient-preserving non-one witnesses at logarithm 40000

The actual series comparison, variable-scale budgets and rational main margin
yield odd non-one primes without an extra analytic budget assumption.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, for a nonprincipal quadratic character at even level q≥20000,
 logarithmic scale L≥40000 with log(q)≤L+2 yields an odd non-one prime at most (4/5)L².
 Combine the actual principal and ramp bounds with conductor-retaining variable errors.
 The prime-two cost is at most 1/100 and the strict main margin exceeds all rounded errors.
 This supplies the strengthened pointwise and common-endpoint witness interface. -/
theorem exists_odd_prime_ne_one_of_gamma_log_40000 {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 40000 ≤ L)
    (hlogq : Real.log q ≤ L + 2) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  let x := (32 / 99 : ℝ) * L ^ 2
  have hxlarge : (3 : ℝ) ^ 16 ≤ x := Analysis.nonOne_ramp_scale_large hL
  have hx : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ 3 ^ 16).trans hxlarge
  have hx0 := zero_lt_one.trans_le hx
  have hs0 := Real.sqrt_pos.mpr hx0
  have hcut : 1 ≤ (99 / 40 : ℝ) * x := by linarith only [hx]
  have hs := Analysis.ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hfpos : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hmqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hmq
  have hlogf := (Real.log_le_log hfpos hmqR).trans hlogq
  have hf0 : 0 ≤ Real.log χ.conductor :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero)
  have hpole := PaperStatements.nonOne_pole_budget hL hs hlogq
  have hleft := PaperStatements.nonOne_left_budget hL hxlarge hs hf0 hlogf
  have hlead := mul_le_mul_of_nonneg_left hlogf (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann hx
  have heP := (div_le_iff₀ hs0).mpr (Analysis.nonOne_exponential_error hL)
  have hT := gamma_ramp_sum_lower_variable hGRH.riemann hx
  have heT := (div_le_iff₀ hs0).mpr (Analysis.nonOne_ramp_error_numerator hL)
  have htwo := Analysis.nonOne_prime_two_budget hL
  have hmain := Analysis.nonOne_main_term_gap (show (0 : ℝ) < L by linarith only [hL])
  have hgap :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re +
        ((11783423 / 25000000 : ℝ) * Real.log χ.conductor + 24 + 64 / 9 +
          ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
          x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log χ.conductor + 283) + 5 / 3)) +
        (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) := by
    change _ ≤ (1 / 5 : ℝ) at heP
    change _ ≤ (691 / 100 : ℝ) at heT
    change _ ≤ (21 / 10 : ℝ) at hpole
    change _ ≤ (2 : ℝ) at hleft
    change _ ≤ (1 / 100 : ℝ) at htwo
    change
      _ <
        (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) *
          Real.sqrt x at hmain
    nlinarith only [hP, heP, hT, heT, hpole, hleft, hlead, htwo, hmain, hL]
  obtain ⟨p, hp, hodd, hbound, hval⟩ :=
    exists_odd_prime_ne_one_of_gamma_variable_budget hq χ hquad hne h2 hGRH hx hcut hgap
  refine ⟨p, hp, hodd, ?_, hval⟩
  calc
    (p : ℝ) ≤ (99 / 40 : ℝ) * x := hbound
    _ = (4 / 5 : ℝ) * L ^ 2 := by
      dsimp only [x]
      ring

end PseudoPrime.LLS
