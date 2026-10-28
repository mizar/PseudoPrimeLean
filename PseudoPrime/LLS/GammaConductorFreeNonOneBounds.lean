/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeAdaptiveBounds
public import PseudoPrime.LLS.GammaNonOneAdaptiveWitnessBounds
public import PseudoPrime.LLS.GammaNonOneProfileWitnessBounds
public import PseudoPrime.LLS.GammaRefinedTailErrorBounds
public import PseudoPrime.LLS.PaperStatements.GammaConductorFreeNonOneBounds

/-! # Non-one quadratic Gamma witnesses from logarithmic scale 30000 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH for a nonprincipal quadratic even level q ≥ 20000,
the conductor-free comparison with any certified prefix error C yields
a non-one prime below (4/5)L² for L ≥ 30000 when the explicit scalar
budget is at most L/795. All actual sums and errors are retained before
the strict main gap is applied. This is the reusable prefix-profile theorem. -/
theorem exists_odd_prime_ne_one_of_conductor_free_prefix_profile {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 30000 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) (prefixLen : ℕ) {C : ℝ}
    (hC : Analysis.gammaResolventPrefixErrorSum prefixLen < C)
    (hbudget : C + 1627 / 100 + (11783423 / 25000000 : ℝ) * (7 / 5) ≤ L / 795) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  let x := (32 / 99 : ℝ) * L ^ 2
  have hL0 : 0 < L := by linarith only [hL]
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 30000)]
  have hx1 : 1 ≤ x := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hx
  have hx0 := zero_lt_one.trans_le hx1
  have hs := Analysis.ramp_scale_sqrt_lower hL0.le
  have hl := Analysis.conductor_free_nonOne_cutoff_log (show (30000 : ℝ) ≤ L by linarith only [hL])
  obtain ⟨hleft, heP, heT, htwo⟩ :=
    PaperStatements.conductor_free_nonOne_error_budgets (show (30000 : ℝ) ≤ L by linarith only [hL])
      hx1 hs hl
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

/-- Under GRH for nonprincipal quadratic even q ≥ 20000, L ≥ 30000 and
log q ≤ L+7/5, there is an odd prime with character value different from
one at most (4/5)L². Instantiate the conductor-free profile with the
existing thirty-two-term certificate C=197/10; its scalar budget holds
throughout this half-line. No unresolved numerical gap is assumed. -/
theorem exists_odd_prime_ne_one_of_gamma_log_30000 {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 30000 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  exact
    exists_odd_prime_ne_one_of_conductor_free_prefix_profile hq χ hquad hne h2 hGRH hL hlogq 32
      Analysis.gammaResolvent_thirtyTwo_error_lt (by linarith only [hL])

/-- Under GRH, a nonprincipal quadratic character at even level q ≥ 20000
has an odd prime with value different from one below (4/5)L² whenever
L ≥ 30300 and log q ≤ L+7/5. Use the conductor-free adaptive character
bound and certified common-scale errors; the strict main-term gap absorbs
all constants on the full half-line. No numerical-gap hypothesis remains. -/
theorem exists_odd_prime_ne_one_of_gamma_log_30300 {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 30300 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  exact
    exists_odd_prime_ne_one_of_gamma_log_30000 hq χ hquad hne h2 hGRH (by linarith only [hL]) hlogq

end PseudoPrime.LLS
