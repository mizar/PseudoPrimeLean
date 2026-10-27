/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNearSquareNonOneBounds
public import PseudoPrime.LLS.GammaQuadraticUniformBounds

/-! # Signed local absorption for negative witnesses from logarithmic scale 1000 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At q ≥ 20000 under GRH, L ≥ 1000 and log q ≤ L+7/5, retain the
actual primitive conductor in the upper bound M log(conductor)+22 at x=(2/5)L².
The existing thirty-two-term certificate, pole cost two and left cost 7/100
prove the constant. Retaining the conductor permits local quotient absorption. -/
theorem gamma_primitiveCharacter_sum_re_le_nearSquare_conductor {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 1000 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log χ.conductor + 22 := by
  let x := (2 / 5 : ℝ) * L ^ 2
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 1000)]
  have he := nearSquare_gamma_error_budgets hL
  have hpole := (nearSquare_gamma_dyadic_pole_budgets hL hlogq).2
  have hu :=
    gamma_primitiveCharacter_sum_re_le_conductor_free_prefix hq χ hne hGRH hx 32
      Analysis.gammaResolvent_thirtyTwo_error_lt
  linarith only [hu, he.1, hpole]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- For odd n, 4n ≥ 20000, L ≥ 20 and log(4n) ≤ L+2, any positive x
with sqrt x ≥ 63L/100 and log(99x/40) ≤ 2 log L has original-level
prime-factor cost at most five. Transfer the elementary omega bound
to L+2 and cancel the logarithms. No fixed scale or factorization is required. -/
theorem gamma_uniform_prime_factor_cost_le_five_of_root_of_twenty_le {n : ℕ} (hn : Odd n)
    (hq : 20000 ≤ 4 * n) {L x : ℝ} (hL : 20 ≤ L) (hlogq : Real.log (4 * n : ℕ) ≤ L + 2) (hx : 0 < x)
    (hroot : (63 / 100 : ℝ) * L ≤ Real.sqrt x)
    (hcut : Real.log ((99 / 40 : ℝ) * x) ≤ 2 * Real.log L) :
    ((4 * n).primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x ≤ 5 := by
  have hn750 : 750 ≤ n := by linarith only [hq]
  have hL0 : 0 < L := by linarith only [hL]
  have hQe := exp_one_le_log_level hq
  have hratio := self_div_log_le_of_exp_one_le hQe hlogq
  have hω := AnalyticNumberTheory.Arithmetic.elementaryOmegaStatement n hn hn750
  change
    ((4 * n).primeFactors.card : ℝ) ≤
      (7 / 5 : ℝ) * Real.log (4 * n : ℕ) / Real.log (Real.log (4 * n : ℕ)) at hω
  have hr := mul_le_mul_of_nonneg_left hratio (by norm_num only : (0 : ℝ) ≤ 7 / 5)
  have hωT : ((4 * n).primeFactors.card : ℝ) ≤ (7 / 5 : ℝ) * (L + 2) / Real.log (L + 2) := by
    rw [← mul_div_assoc, ← mul_div_assoc] at hr
    exact hω.trans hr
  have hden := Real.log_pos (show (1 : ℝ) < L + 2 by linarith only [hL])
  have hωmul := (le_div_iff₀ hden).mp hωT
  have hlogs := Real.log_le_log hL0 (show L ≤ L + 2 by linarith only)
  have hm :=
    mul_le_mul_of_nonneg_left
      (show Real.log ((99 / 40 : ℝ) * x) ≤ 2 * Real.log (L + 2) by linarith only [hcut, hlogs])
      (Nat.cast_nonneg (4 * n).primeFactors.card : (0 : ℝ) ≤ (4 * n).primeFactors.card)
  have hbudget :
    ((4 * n).primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) ≤ (14 / 5 : ℝ) * (L + 2) := by
    nlinarith only [hm, hωmul]
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hx)]
  nlinarith only [hbudget, hroot, hL]

/-- For odd n, 4n ≥ 20000, L ≥ 1000 and log(4n) ≤ L+2, any positive x
with sqrt x ≥ 63L/100 and log(99x/40) ≤ 2 log L has original-level
prime-factor cost at most five. Transfer the elementary omega bound
to L+2 and cancel the logarithms. No fixed scale or factorization is required. -/
theorem gamma_uniform_prime_factor_cost_le_five_of_root {n : ℕ} (hn : Odd n) (hq : 20000 ≤ 4 * n)
    {L x : ℝ} (hL : 1000 ≤ L) (hlogq : Real.log (4 * n : ℕ) ≤ L + 2) (hx : 0 < x)
    (hroot : (63 / 100 : ℝ) * L ≤ Real.sqrt x)
    (hcut : Real.log ((99 / 40 : ℝ) * x) ≤ 2 * Real.log L) :
    ((4 * n).primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x ≤ 5 := by
  exact
    gamma_uniform_prime_factor_cost_le_five_of_root_of_twenty_le hn hq (by linarith only [hL]) hlogq
      hx hroot hcut

/-- At near-square scale x=(2/5)L², odd n, 4n ≥ 20000, L ≥ 20 and
log(4n) ≤ L+7/5, the conductor term plus the actual signed quadratic local
correction is at most M L+6. The logarithm of the quotient is absorbed before
the conductor is enlarged, and the generic prime-factor cost supplies five.
This includes the prime two and every square-part or ramified prime. -/
theorem gammaQuadraticLocalCorrection_absorbed_nearSquare_of_twenty_le {n : ℕ} (hn : Odd n)
    (χ : DirichletCharacter ℂ (4 * n)) (hquad : χ.IsQuadratic) (hq : 20000 ≤ 4 * n) {L : ℝ}
    (hL : 20 ≤ L) (hlogq : Real.log (4 * n : ℕ) ≤ L + 7 / 5) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    (11783423 / 25000000 : ℝ) * Real.log χ.conductor + gammaQuadraticLocalCorrection χ x ≤
      (11783423 / 25000000 : ℝ) * L + 6 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  let x := (2 / 5 : ℝ) * L ^ 2
  have hL0 : 0 < L := by linarith only [hL]
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 20)]
  have hx0 := zero_lt_one.trans_le hx
  have hroot : (63 / 100 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx0.le).mpr
    dsimp only [x]
    nlinarith only [sq_nonneg L]
  have hcut :=
    Real.log_le_log (mul_pos (by norm_num only : (0 : ℝ) < 99 / 40) hx0)
      (show (99 / 40 : ℝ) * x ≤ L ^ 2 by
        dsimp only [x]
        nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hcut
  norm_num only [Nat.cast_ofNat] at hcut
  have hcost :=
    gamma_uniform_prime_factor_cost_le_five_of_root_of_twenty_le hn hq hL
      (show Real.log (4 * n : ℕ) ≤ L + 2 by linarith only [hlogq]) hx0 hroot hcut
  have hM : (1 : ℝ) ≤ (11783423 / 25000000) * Real.sqrt x := by nlinarith only [hroot, hL]
  have hcorr :=
    gammaQuadraticLocalCorrection_absorb_conductor χ hquad hx0
      (show 1 ≤ (99 / 40 : ℝ) * x by linarith only [hx]) hM
  have hshift := mul_le_mul_of_nonneg_left hlogq (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  nlinarith only [hcorr, hcost, hshift]

/-- At near-square scale x=(2/5)L², odd n, 4n ≥ 20000, L ≥ 1000 and
log(4n) ≤ L+7/5, the conductor term plus the actual signed quadratic local
correction is at most M L+6. The logarithm of the quotient is absorbed before
the conductor is enlarged, and the generic prime-factor cost supplies five.
This includes the prime two and every square-part or ramified prime. -/
theorem gammaQuadraticLocalCorrection_absorbed_nearSquare_endpoint {n : ℕ} (hn : Odd n)
    (χ : DirichletCharacter ℂ (4 * n)) (hquad : χ.IsQuadratic) (hq : 20000 ≤ 4 * n) {L : ℝ}
    (hL : 1000 ≤ L) (hlogq : Real.log (4 * n : ℕ) ≤ L + 7 / 5) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    (11783423 / 25000000 : ℝ) * Real.log χ.conductor + gammaQuadraticLocalCorrection χ x ≤
      (11783423 / 25000000 : ℝ) * L + 6 := by
  exact
    gammaQuadraticLocalCorrection_absorbed_nearSquare_of_twenty_le hn χ hquad hq
      (by linarith only [hL]) hlogq

/-- Under GRH, a nonprincipal quadratic character at level 4n with odd n,
4n ≥ 20000, L ≥ 1000 and log(4n) ≤ L+7/5 cannot be one at all eligible
primes through (99/100)L². Combine the actual no-witness inequality,
conductor-retaining primitive bound and signed local absorption. Certified
principal/ramp errors close the strict gap on the entire half-line. -/
theorem gamma_ramp_prime_trivial_false_nearSquare_endpoint {n : ℕ} (hn : Odd n)
    (χ : DirichletCharacter ℂ (4 * n)) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hq : 20000 ≤ 4 * n)
    {L : ℝ} (hL : 1000 ≤ L) (hlogq : Real.log (4 * n : ℕ) ≤ L + 7 / 5)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ¬(∀ p : ℕ,
        p.Prime → ¬p ∣ 4 * n → (p : ℝ) ≤ (99 / 40 : ℝ) * ((2 / 5 : ℝ) * L ^ 2) → χ p = 1) := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  let x := (2 / 5 : ℝ) * L ^ 2
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 1000)]
  intro hsmall
  have hQ := gamma_ramp_no_witness_comparison χ hquad (zero_lt_one.trans_le hx) hsmall
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann hx
  have hT := gamma_ramp_sum_lower_variable hGRH.riemann hx
  have hC :=
    PaperStatements.gamma_primitiveCharacter_sum_re_le_nearSquare_conductor hq χ hne hGRH hL hlogq
  have hE := gammaQuadraticLocalCorrection_absorbed_nearSquare_endpoint hn χ hquad hq hL hlogq
  have he := PaperStatements.nearSquare_gamma_error_budgets hL
  nlinarith only [hQ, hP, hT, hC, hE, he.2.1, he.2.2.1, he.2.2.2.2, hL]

end PseudoPrime.LLS
