/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeNonOneBounds
public import PseudoPrime.LLS.GammaPrincipalEulerCharacterBounds
public import PseudoPrime.LLS.GammaRetainedCommonCostBounds

/-! # Non-one witnesses from retained real-axis Euler budgets -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L > 0 and log L ≤ L/2000, the four-fifths cutoff logarithm is at most L/1000.
Compare the cutoff with L² and double the logarithm bound. This weaker logarithmic
hypothesis permits smaller starting scales in the retained Euler comparison. -/
theorem nonOne_cutoff_log_of_wide_ratio {L : ℝ} (hL0 : 0 < L) (hlogL : Real.log L ≤ L / 2000) :
    Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) ≤ L / 1000 := by
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

/-- For L ≥ 15000, x ≥ 1, sqrt x ≥ 9L/16 and log(99x/40) ≤ L/1000,
the four normalized errors obey the displayed bounds, with ramp allowance 71/10.
Clear positive denominators and use inverse-square-root decay. These estimates
are independent of the source of the character's zero-mass budget. -/
theorem nonOne_error_budgets_of_wide_ratio {L x : ℝ} (hL : 15000 ≤ L) (hx : 1 ≤ x)
    (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hlog : Real.log (x * (99 / 40 : ℝ)) ≤ L / 1000) :
    43 * x ^ (-9 / 16 : ℝ) ≤ 1 / 100 ∧
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤
        3 / 20 ∧
      ((135 / 20 : ℝ) * Real.sqrt x +
            86 * ((1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20)) /
          Real.sqrt x ≤
        71 / 10 ∧
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

/-- Under GRH, let χ be quadratic at an even nonzero level. Suppose L ≥ 15000,
log L ≤ L/2000, log q ≤ L+7/5, and the actual primitive Gamma sum has the stated
conductor-retaining upper bound with cost C. If its displayed scalar budget closes,
an odd prime p ≤ (4/5)L² has χ(p) ≠ 1. Combine the actual upper bound with the
principal and ramp lower comparison. No prefix certificate is required by this interface. -/
theorem exists_odd_prime_ne_one_of_log_ratio_character_budget {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 15000 ≤ L)
    (hlogL : Real.log L ≤ L / 2000) (hlogq : Real.log q ≤ L + 7 / 5) {C : ℝ}
    (hupper :
      (∑' k : ℕ,
            PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter ((32 / 99 : ℝ) * L ^ 2)
              k).re ≤
        (11783423 / 25000000 : ℝ) * Real.log χ.conductor + C +
          ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt ((32 / 99 : ℝ) * L ^ 2) +
          43 * ((32 / 99 : ℝ) * L ^ 2) ^ (-9 / 16 : ℝ))
    (hbudget : C + 1647 / 100 + (11783423 / 25000000 : ℝ) * (7 / 5) ≤ L / 795) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  let x := (32 / 99 : ℝ) * L ^ 2
  have hL0 : 0 < L := by linarith only [hL]
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 15000)]
  have hx1 : 1 ≤ x := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hx
  have hx0 := zero_lt_one.trans_le hx1
  have hs := Analysis.ramp_scale_sqrt_lower hL0.le
  have hl := Analysis.nonOne_cutoff_log_of_wide_ratio hL0 hlogL
  obtain ⟨hleft, heP, heT, htwo⟩ := PaperStatements.nonOne_error_budgets_of_wide_ratio hL hx1 hs hl
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
  have hnp := hupper
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

/-- For every L ≥ 22920, log L ≤ L/2000. Compare the anchor with 2^15,
use the certified logarithm of two and extend by a tangent inequality.
This discharges the logarithmic condition on a complete half-line. -/
theorem nonOne_log_ratio_of_ge_22920 {L : ℝ} (hL : 22920 ≤ L) : Real.log L ≤ L / 2000 := by
  have hanchor :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 22920) (by norm_num only : (22920 : ℝ) ≤ 2 ^ 15)
  rw [Real.log_pow] at hanchor
  norm_num only [Nat.cast_ofNat] at hanchor
  have h :=
    log_le_mul_of_anchor (a := 22920) (b := 1 / 2000) (by norm_num only) hL
      (by linarith only [hanchor, Real.log_two_lt_d9]) (by norm_num only)
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

end PseudoPrime.Analysis

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal quadratic character of even level q ≥ 20000 has
an odd-prime non-one witness at most (4/5)L² if L ≥ 22920 and log q ≤ L+7/5.
Use the signed real-axis Euler bound with cost 117/10 in the generic comparison.
This lowers the starting point without adding a numerical prefix certificate. -/
theorem exists_odd_prime_ne_one_of_gamma_log_22920 {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 22920 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  apply
    exists_odd_prime_ne_one_of_log_ratio_character_budget χ hquad h2 hGRH (by linarith only [hL])
      (Analysis.nonOne_log_ratio_of_ge_22920 hL) hlogq (C := 117 / 10)
  · exact
      (PaperStatements.gamma_primitiveCharacter_sum_re_lt_principal_euler hq χ hne hGRH
          (by nlinarith only [hL, sq_nonneg (L - 22920)])).le
  · linarith only [hL]

end PseudoPrime.LLS

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH for nonprincipal χ at level q ≥ 20000 and x ≥ 2, a cap C on the sum
of principal Euler mass and the primitive signed Gamma cost gives the displayed
conductor-retaining arithmetic bound. Use the empty signed prefix and the completed
remainder. This transports any improved common cost without fixing parity or a certificate. -/
theorem gamma_primitiveCharacter_sum_re_lt_common_euler_cost {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C : ℝ} (hx : 2 ≤ x)
    (hCost :
      (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) +
          gammaSignedGammaCost χ.primitiveCharacter.gammaFactor <
        C) :
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re <
      (11783423 / 25000000 : ℝ) * Real.log χ.conductor + C +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hz :=
    AnalyticNumberTheory.DirichletLFunction.gammaResolvent_zeroMass_le_signed_prefix
      (le_trans (by norm_num only : (2 : ℕ) ≤ 3) hm) (hGRH _ χ.primitiveCharacter hp) hp hnp
      (inv_ne_one.mpr hnp) ∅
  have hu :=
    gamma_primitive_sum_re_le_resolvent_conductor_free hq hm hmq hGRH hp hnp (inv_ne_one.mpr hnp) hx
  simp only [Finset.sum_empty, mul_zero, sub_zero, add_zero] at hz
  dsimp only [gammaSignedGammaCost] at hCost
  linarith only [hz, hu, hCost]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.Analysis

/-- For L ≥ 22221, log L ≤ L/2000. Bound the anchor by 2^15 and extend
with the logarithm tangent. This supplies the error condition for the even-character bound. -/
theorem nonOne_log_ratio_of_ge_22221 {L : ℝ} (hL : 22221 ≤ L) : Real.log L ≤ L / 2000 := by
  have hanchor :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 22221) (by norm_num only : (22221 : ℝ) ≤ 2 ^ 15)
  rw [Real.log_pow] at hanchor
  norm_num only [Nat.cast_ofNat] at hanchor
  have h :=
    log_le_mul_of_anchor (a := 22221) (b := 1 / 2000) (by norm_num only) hL
      (by linarith only [hanchor, Real.log_two_lt_d9]) (by norm_num only)
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

end PseudoPrime.Analysis

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal even quadratic character at even level q ≥ 20000
has an odd-prime non-one witness through (4/5)L² when L ≥ 22221 and log q ≤ L+7/5.
Retain parity through primitivization and use common Euler cost 541/50.
This improves the starting scale for positive-input quadratic characters. -/
theorem exists_odd_prime_ne_one_of_even_gamma_log_22221 {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (heven : χ.Even) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 22221 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  apply
    exists_odd_prime_ne_one_of_log_ratio_character_budget χ hquad h2 hGRH (by linarith only [hL])
      (Analysis.nonOne_log_ratio_of_ge_22221 hL) hlogq (C := 541 / 50)
  · exact
      (PaperStatements.gamma_primitiveCharacter_sum_re_lt_common_euler_cost hq χ hne hGRH
          (by nlinarith only [hL, sq_nonneg (L - 22221)])
          (gamma_even_common_cost_lt_precise hGRH.riemann
            ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven))).le
  · linarith only [hL]

end PseudoPrime.LLS
