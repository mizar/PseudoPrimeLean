/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNearSquareNumerics

/-! # Quadratic non-one witnesses at near-square scale from log 1000 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At L ≥ 1000 and x=(2/5)L², the dyadic correction is at most 1/20.
If log q ≤ L+7/5, the ambient pole cost is at most two.
Use the common logarithmic tangent and a rational lower bound for sqrt x.
These full-half-line budgets apply to characters at original level 4n. -/
theorem nearSquare_gamma_dyadic_pole_budgets {q : ℕ} {L : ℝ} (hL : 1000 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x ≤ 1 / 20 ∧
      ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x ≤ 2 := by
  dsimp only
  let x := (2 / 5 : ℝ) * L ^ 2
  have hL0 : 0 < L := by linarith only [hL]
  have hx : 0 < x := mul_pos (by norm_num only) (sq_pos_of_pos hL0)
  have hs := Real.sqrt_pos.mpr hx
  have hroot : (63 / 100 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx.le).mpr
    dsimp only [x]
    nlinarith only [sq_nonneg L]
  have hc :=
    Real.log_le_log (mul_pos (by norm_num only : (0 : ℝ) < 99 / 40) hx)
      (show (99 / 40 : ℝ) * x ≤ L ^ 2 by
        dsimp only [x]
        nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hc
  norm_num only [Nat.cast_ofNat] at hc
  have hl := Analysis.nearSquare_gamma_log_bound hL
  constructor
  · rw [div_le_iff₀ hs]
    linarith only [hc, hl, hroot, hL, Real.log_two_lt_d9]
  · rw [div_le_iff₀ hs]
    linarith only [hlogq, hroot, hL]

/-- Under GRH, q ≥ 20000, L ≥ 1000 and log q ≤ L+7/5, every
nonprincipal primitive Gamma sum at x=(2/5)L² is at most M L+23.
Bound the conductor by q and use the existing thirty-two-term certificate,
the common left cost, and the pole budget above. The bound is uniform in q's
factorization and in the character; quadraticity is not required. -/
theorem gamma_primitiveCharacter_sum_re_le_nearSquare_endpoint {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 1000 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * L + 23 := by
  let x := (2 / 5 : ℝ) * L ^ 2
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 1000)]
  have he := nearSquare_gamma_error_budgets hL
  have hpole := (nearSquare_gamma_dyadic_pole_budgets hL hlogq).2
  have hu :=
    gamma_primitiveCharacter_sum_re_le_conductor_free_prefix hq χ hne hGRH hx 32
      Analysis.gammaResolvent_thirtyTwo_error_lt
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hf : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hmqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hmq
  have hlead :=
    mul_le_mul_of_nonneg_left ((Real.log_le_log hf hmqR).trans hlogq)
      (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  linarith only [hu, hlead, he.1, hpole]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under GRH at even q ≥ 20000, a nonprincipal quadratic character has
an odd prime with value different from one below (99/100)L² whenever
L ≥ 1000 and log q ≤ L+7/5. Combine the certified actual principal/ramp
bounds with the uniform primitive sum and dyadic correction. The strict
gap is proved on the entire half-line and is not an additional assumption. -/
theorem exists_odd_prime_ne_one_of_nearSquare_gamma_endpoint {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 1000 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 100 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  let x := (2 / 5 : ℝ) * L ^ 2
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 1000)]
  have hx0 := zero_lt_one.trans_le hx
  have he := PaperStatements.nearSquare_gamma_error_budgets hL
  have htwo := (PaperStatements.nearSquare_gamma_dyadic_pole_budgets hL hlogq).1
  have hu :=
    PaperStatements.gamma_primitiveCharacter_sum_re_le_nearSquare_endpoint hq χ hne hGRH hL hlogq
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann hx
  have hT := gamma_ramp_sum_lower_variable hGRH.riemann hx
  have hgap :
    (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re +
        (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x k).re +
        (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) := by
    nlinarith only [hu, hP, hT, he.2.1, he.2.2.1, he.2.2.2.2, htwo, hL]
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_ne_one_of_gamma_ramp_gap χ hquad h2 hx0
      (show 1 ≤ (99 / 40 : ℝ) * x by linarith only [hx]) hgap
  refine ⟨p, hp, ho, ?_, hv⟩
  dsimp only [x] at hb
  nlinarith only [hb]

end PseudoPrime.LLS
