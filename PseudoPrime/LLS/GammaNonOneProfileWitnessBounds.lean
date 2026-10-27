/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneCommonNumerics
public import PseudoPrime.LLS.GammaVariablePrefixWitnessBounds

/-! # Common logarithmic witness profiles for variable Gamma prefixes

One scalar domain and one budget inequality support every certified prefix length.
Certified sixteen- and thirty-two-term profiles share this interface.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH for nonprincipal quadratic even q≥20000, a certified prefix error C
 and the displayed scalar budget at L≥35000 yield an odd non-one prime at most (4/5)L².
 Combine the actual principal/ramp bounds and common contour/local budgets with the
 variable-prefix comparison. This avoids a separate analytic proof for each profile. -/
theorem exists_odd_prime_ne_one_of_gamma_prefix_profile {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (prefixLen : ℕ) {C : ℝ}
    (hC : Analysis.gammaResolventPrefixErrorSum prefixLen < C) {L : ℝ} (hL : 35000 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5)
    (hbudget :
      C + 64 / 9 + 21 / 10 + 17 / 10 + 2 * (693 / 100) + 3 / 20 + 1 / 100 +
          (11783423 / 25000000 : ℝ) * (7 / 5) ≤
        L / 795) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  let x := (32 / 99 : ℝ) * L ^ 2
  have hxlarge : (17 / 5 : ℝ) ^ 16 ≤ x := Analysis.common_nonOne_ramp_scale_large hL
  have hx : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ (17 / 5) ^ 16).trans hxlarge
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
  have hlogq2 : Real.log q ≤ L + 2 := by linarith only [hlogq]
  have hlogf2 : Real.log χ.conductor ≤ L + 2 := by linarith only [hlogf]
  have hpole := PaperStatements.common_nonOne_pole_budget hL hs hlogq2
  have hleft := PaperStatements.common_nonOne_left_budget hL hxlarge hs hf0 hlogf2
  have hlead := mul_le_mul_of_nonneg_left hlogf (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann hx
  have heP := (div_le_iff₀ hs0).mpr (Analysis.common_nonOne_exponential_error hL)
  have hT := gamma_ramp_sum_lower_variable hGRH.riemann hx
  have heT := (div_le_iff₀ hs0).mpr (Analysis.common_nonOne_ramp_error_numerator hL)
  have htwo := Analysis.common_nonOne_prime_two_budget hL
  have hmain := Analysis.nonOne_main_term_gap (show (0 : ℝ) < L by linarith only [hL])
  have hgap :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re +
        ((11783423 / 25000000 : ℝ) * Real.log χ.conductor + C + 64 / 9 +
          ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
          x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log χ.conductor + 283) + 5 / 3)) +
        (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) := by
    change _ ≤ (3 / 20 : ℝ) at heP
    change _ ≤ (693 / 100 : ℝ) at heT
    change _ ≤ (21 / 10 : ℝ) at hpole
    change _ ≤ (17 / 10 : ℝ) at hleft
    change _ ≤ (1 / 100 : ℝ) at htwo
    change
      _ <
        (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) *
          Real.sqrt x at hmain
    nlinarith only [hP, heP, hT, heT, hpole, hleft, hlead, htwo, hmain, hbudget]
  obtain ⟨p, hp, hodd, hbound, hval⟩ :=
    exists_odd_prime_ne_one_of_variable_prefix_budget hq χ hquad hne h2 hGRH hx hcut prefixLen hC
      hgap
  refine ⟨p, hp, hodd, ?_, hval⟩
  calc
    (p : ℝ) ≤ (99 / 40 : ℝ) * x := hbound
    _ = (4 / 5 : ℝ) * L ^ 2 := by
      dsimp only [x]
      ring

/-- Under GRH for nonprincipal quadratic even q≥20000, L≥36090 and log(q)≤L+7/5
 give an odd non-one prime at most (4/5)L². Instantiate the common profile with sixteen terms
 and certified error 99/5. The scalar budget holds throughout the full logarithmic range. -/
theorem exists_odd_prime_ne_one_of_gamma_sixteen_log {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 36090 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  exact
    exists_odd_prime_ne_one_of_gamma_prefix_profile hq χ hquad hne h2 hGRH 16
      Analysis.gammaResolvent_sixteen_error_lt ((by norm_num only : (35000 : ℝ) ≤ 36090).trans hL)
      hlogq (by linarith only [hL])

/-- Under GRH for a nonprincipal quadratic character at even q≥20000,
 L≥36010 and log(q)≤L+7/5 yield an odd non-one prime at most (4/5)L².
 Instantiate the shared profile with thirty-two terms and certified zero error 197/10.
 The scalar margin is verified throughout the full logarithmic range. -/
theorem exists_odd_prime_ne_one_of_gamma_thirtyTwo_log {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 36010 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  exact
    exists_odd_prime_ne_one_of_gamma_prefix_profile hq χ hquad hne h2 hGRH 32
      Analysis.gammaResolvent_thirtyTwo_error_lt ((by norm_num only : (35000 : ℝ) ≤ 36010).trans hL)
      hlogq (by linarith only [hL])

end PseudoPrime.LLS
