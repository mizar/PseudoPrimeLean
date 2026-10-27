/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeNonOneBounds

/-! # Non-one Gamma witnesses with explicit logarithmic and prefix budgets -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L > 0 with log L ≤ L/2800, the four-fifths cutoff logarithm is at most L/1400.
Compare the cutoff with L² and use log(L²)=2 log L. This isolates the logarithmic
hypothesis from the numerical starting point for subsequent error estimates. -/
theorem nonOne_cutoff_log_of_log_ratio {L : ℝ} (hL0 : 0 < L) (hlogL : Real.log L ≤ L / 2800) :
    Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) ≤ L / 1400 := by
  have hc :=
    Real.log_le_log
      (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 32 / 99) (sq_pos_of_pos hL0))
        (by norm_num only : (0 : ℝ) < 99 / 40))
      (show ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) ≤ L ^ 2 by nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hc
  norm_num only [Nat.cast_ofNat] at hc
  linarith only [hc, hlogL]

end PseudoPrime.Analysis

namespace PseudoPrime.LLS.PaperStatements

/-- For L ≥ 15000, x ≥ 1, sqrt x ≥ 9L/16 and log(99x/40) ≤ L/1400,
the principal, ramp, decay and prime-two errors satisfy the four displayed budgets.
Use the inverse-square-root decay bound and linear comparisons after clearing
positive denominators. These estimates feed the character witness comparison. -/
theorem nonOne_error_budgets_of_log_ratio {L x : ℝ} (hL : 15000 ≤ L) (hx : 1 ≤ x)
    (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hlog : Real.log (x * (99 / 40 : ℝ)) ≤ L / 1400) :
    43 * x ^ (-9 / 16 : ℝ) ≤ 1 / 100 ∧
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤
        3 / 20 ∧
      ((135 / 20 : ℝ) * Real.sqrt x +
            86 * ((1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20)) /
          Real.sqrt x ≤
        7 ∧
      (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x ≤ 1 / 100 := by
  have hx0 := zero_lt_one.trans_le hx
  have hs := Real.sqrt_pos.mpr hx0
  have hlx : Real.log x ≤ Real.log (x * (99 / 40 : ℝ)) :=
    Real.log_le_log hx0 (by nlinarith only [hx])
  have hdecay :=
    rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 1) (by norm_num only)
      (by
        norm_num only; exact hx)
  simp only [one_mul] at hdecay
  have hleft := mul_le_mul_of_nonneg_left hdecay (by norm_num only : (0 : ℝ) ≤ 43)
  have hleft' : 43 * (1 / Real.sqrt x) ≤ (1 / 100 : ℝ) := by
    rw [mul_one_div, div_le_iff₀ hs]
    linarith only [hroot, hL]
  refine ⟨hleft.trans hleft', ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hs]
    linarith only [hlx, hlog, hroot, hL]
  · rw [div_le_iff₀ hs]
    linarith only [hlog, hroot, hL]
  · rw [mul_comm (99 / 40 : ℝ), div_le_iff₀ hs]
    linarith only [hlog, hroot, hL, Real.log_two_lt_d9]

end PseudoPrime.LLS.PaperStatements

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

namespace PseudoPrime.Analysis

/-- For L ≥ 29121, log L ≤ L/2800. Bound the anchor by 2^15, use the
certified logarithm of two, and extend by the logarithm tangent inequality.
This closes the logarithmic hypothesis on a full half-line. -/
theorem nonOne_log_ratio_of_ge_29121 {L : ℝ} (hL : 29121 ≤ L) : Real.log L ≤ L / 2800 := by
  have hanchor :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 29121) (by norm_num only : (29121 : ℝ) ≤ 2 ^ 15)
  rw [Real.log_pow] at hanchor
  norm_num only [Nat.cast_ofNat] at hanchor
  have h :=
    log_le_mul_of_anchor (a := 29121) (b := 1 / 2800) (by norm_num only) hL
      (by linarith only [hanchor, Real.log_two_lt_d9]) (by norm_num only)
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

end PseudoPrime.Analysis

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal quadratic character of even level q ≥ 20000 has an
odd-prime non-one witness at most (4/5)L² whenever L ≥ 29121 and log q ≤ L+7/5.
Apply the parameterized comparison with the existing 32-term prefix certificate.
This improves the starting scale without generating further finite certificates. -/
theorem exists_odd_prime_ne_one_of_gamma_log_29121 {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 29121 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  exact
    exists_odd_prime_ne_one_of_log_ratio_prefix_profile hq χ hquad hne h2 hGRH
      (by linarith only [hL]) (Analysis.nonOne_log_ratio_of_ge_29121 hL) hlogq 32
      Analysis.gammaResolvent_thirtyTwo_error_lt (by linarith only [hL])

end PseudoPrime.LLS
