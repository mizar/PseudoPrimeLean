/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeNonOneBounds
public import PseudoPrime.LLS.PaperStatements.GammaNonOneLogRatioBounds

/-! # Non-one Gamma witnesses with explicit logarithmic and prefix budgets -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, let χ be a nonprincipal quadratic character of even level q ≥ 20000.
If L ≥ 15000, log L ≤ L/2800, log q ≤ L+7/5, and the certified prefix bound C
satisfies the displayed budget, an odd prime p ≤ (4/5)L² has χ(p) ≠ 1.
Retain the primitive conductor in the Gamma comparison and combine the principal,
ramp and pole bounds. The prefix length and its cost remain parameters. -/
theorem exists_odd_prime_ne_one_of_log_ratio_prefix_profile {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 15000 ≤ L)
    (hlogL : Real.log L ≤ L / 2800) (hlogq : Real.log q ≤ L + 7 / 5) (prefixLen : ℕ) {C : ℝ}
    (hC : Analysis.gammaResolventPrefixErrorSum prefixLen < C)
    (hbudget : C + 1627 / 100 + (11783423 / 25000000 : ℝ) * (7 / 5) ≤ L / 795) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  let x := (32 / 99 : ℝ) * L ^ 2
  have hL0 : 0 < L := by linarith only [hL]
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 15000)]
  have hx1 : 1 ≤ x := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hx
  have hx0 := zero_lt_one.trans_le hx1
  have hs := Analysis.ramp_scale_sqrt_lower hL0.le
  have hl := Analysis.nonOne_cutoff_log_of_log_ratio hL0 hlogL
  obtain ⟨hleft, heP, heT, htwo⟩ := PaperStatements.nonOne_error_budgets_of_log_ratio hL hx1 hs hl
  have hpole :=
    PaperStatements.gamma_tail_pole_budget (show (15000 : ℝ) ≤ L by linarith only [hL]) hs
      (show Real.log q ≤ L + 2 by linarith only [hlogq])
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hfpos : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hmqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hmq
  have hlogf := (Real.log_le_log hfpos hmqR).trans hlogq
  have hlead := mul_le_mul_of_nonneg_left hlogf (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann hx1
  have hT := gamma_ramp_sum_lower_variable hGRH.riemann hx1
  have hmain := Analysis.nonOne_main_term_gap hL0
  have hnp :=
    PaperStatements.gamma_primitiveCharacter_sum_re_le_conductor_free_prefix hq χ hne hGRH hx
      prefixLen hC
  have hactual :
    (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re +
        (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x k).re +
        (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) := by
    change
      _ <
        (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) *
          Real.sqrt x at hmain
    nlinarith only [hP, hT, hmain, hnp, hlead, hleft, heP, heT, htwo, hpole, hbudget]
  obtain ⟨p, hp, hodd, hbound, hval⟩ :=
    exists_odd_prime_ne_one_of_gamma_ramp_gap χ hquad h2 hx0
      (show 1 ≤ (99 / 40 : ℝ) * x by linarith only [hx]) hactual
  refine ⟨p, hp, hodd, ?_, hval⟩
  dsimp only [x] at hbound
  nlinarith only [hbound]

end PseudoPrime.LLS
