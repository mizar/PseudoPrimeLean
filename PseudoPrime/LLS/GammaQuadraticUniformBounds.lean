/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaQuadraticNoWitness

/-! # Uniform smoothed quadratic bounds below a common endpoint

The original level may be smaller than the scale-defining endpoint.
Monotonicity transfers the prime-factor cost before the no-witness contradiction.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- On inputs at least exp(1), t/log(t) is nondecreasing.
Apply the antitone log(t)/t theorem and clear the positive logarithm denominators.
This transfers the elementary prime-factor cost to a larger ambient logarithm. -/
theorem self_div_log_le_of_exp_one_le {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    a / Real.log a ≤ b / Real.log b := by
  have ha0 := (Real.exp_pos 1).trans_le ha
  have ha1 := (Real.one_lt_exp_iff.mpr (by norm_num only : (0 : ℝ) < 1)).trans_le ha
  have hb0 := ha0.trans_le hab
  have hla := Real.log_pos ha1
  have hlb := hla.trans_le (Real.log_le_log ha0 hab)
  have hanti :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (ha.trans hab)) hab
  have hcross := (div_le_div_iff₀ hb0 ha0).mp hanti
  apply (div_le_div_iff₀ hla hlb).mpr
  nlinarith only [hcross]

/-- At natural level q≥20000, log(q) is at least exp(1).
Compare with log(27)=3log(3) using certified logarithm and exponential constants.
This supplies the monotonicity domain of the prime-factor ratio. -/
theorem exp_one_le_log_level {q : ℕ} (hq : 20000 ≤ q) : Real.exp 1 ≤ Real.log q := by
  have h27 : (27 : ℝ) ≤ q := by exact_mod_cast (by linarith only [hq] : 27 ≤ q)
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 27) h27
  rw [show (27 : ℝ) = 3 ^ (3 : ℕ) by norm_num only, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  nlinarith only [hl, Real.log_three_gt_d9, Real.exp_one_lt_d9]

/-- For odd n with 4n≥20000, L≥46000 and log(4n)≤L+2, the prime-factor cost
at scale (32/99)L² is at most five. Monotonicity of t/log(t) transfers the
unconditional omega bound to L+2 before the cutoff logarithm is cancelled.
This covers inputs smaller than the endpoint defining the scale. -/
theorem gamma_uniform_prime_factor_cost_le_five {n : ℕ} (hn : Odd n) (hq : 20000 ≤ 4 * n) {L : ℝ}
    (hL : 46000 ≤ L) (hlogq : Real.log (4 * n : ℕ) ≤ L + 2) :
    ((4 * n).primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * ((32 / 99 : ℝ) * L ^ 2)) /
        Real.sqrt ((32 / 99 : ℝ) * L ^ 2) ≤
      5 := by
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
  have hT1 : 1 < L + 2 := by linarith only [hL]
  have hden := Real.log_pos hT1
  have hωmul := (le_div_iff₀ hden).mp hωT
  have hcut := ramp_cutoff_log_le_two_log hL0
  have hlogs := Real.log_le_log hL0 (show L ≤ L + 2 by linarith only)
  have hcutT : Real.log ((99 / 40 : ℝ) * ((32 / 99 : ℝ) * L ^ 2)) ≤ 2 * Real.log (L + 2) := by
    linarith only [hcut, hlogs]
  have hm :=
    mul_le_mul_of_nonneg_left hcutT
      (Nat.cast_nonneg (4 * n).primeFactors.card : (0 : ℝ) ≤ (4 * n).primeFactors.card)
  have hbudget :
    ((4 * n).primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * ((32 / 99 : ℝ) * L ^ 2)) ≤
      (14 / 5 : ℝ) * (L + 2) := by
    nlinarith only [hm, hωmul]
  have hroot := Analysis.ramp_scale_sqrt_lower hL0.le
  have hs : 0 < Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by linarith only [hroot, hL]
  rw [div_le_iff₀ hs]
  nlinarith only [hbudget, hroot, hL]

/-- For quadratic level 4n, odd n, 4n≥20000, L≥46000 and log(4n)≤L+2,
Mlog(conductor) plus the actual signed local correction at scale (32/99)L² is at most ML+6.
Use the uniform prime-factor cost and absorb the conductor quotient before the ambient shift. -/
theorem gammaQuadraticLocalCorrection_absorbed_uniform {n : ℕ} (hn : Odd n)
    (χ : DirichletCharacter ℂ (4 * n)) (hquad : χ.IsQuadratic) (hq : 20000 ≤ 4 * n) {L : ℝ}
    (hL : 46000 ≤ L) (hlogq : Real.log (4 * n : ℕ) ≤ L + 2) :
    (11783423 / 25000000 : ℝ) * Real.log χ.conductor +
        gammaQuadraticLocalCorrection χ ((32 / 99 : ℝ) * L ^ 2) ≤
      (11783423 / 25000000 : ℝ) * L + 6 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  have hx1 := Analysis.ramp_scale_ge_one hL
  have hxpos := zero_lt_one.trans_le hx1
  have hcut : (1 : ℝ) ≤ (99 / 40) * ((32 / 99 : ℝ) * L ^ 2) := by nlinarith only [hx1]
  have hroot := Analysis.ramp_scale_sqrt_lower (by linarith only [hL])
  have hM : (1 : ℝ) ≤ (11783423 / 25000000) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
    nlinarith only [hroot, hL]
  have hcorr := gammaQuadraticLocalCorrection_absorb_conductor χ hquad hxpos hcut hM
  have hcost := gamma_uniform_prime_factor_cost_le_five hn hq hL hlogq
  have hshift :
    (11783423 / 25000000 : ℝ) * Real.log (4 * n : ℕ) ≤ (11783423 / 25000000 : ℝ) * L + 1 := by
    have hm := mul_le_mul_of_nonneg_left hlogq (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
    nlinarith only [hm]
  nlinarith only [hcorr, hcost, hshift]

/-- Under GRH, a nonprincipal quadratic character of level 4n cannot be trivial
on all eligible primes through (99/40)(32/99)L² when n is odd, 4n≥20000,
L≥46000 and log(4n)≤L+2. Combine the actual no-witness comparison with uniform
local absorption and the principal and nonprincipal budgets.
The endpoint L may exceed log(n), permitting finite witness maxima. -/
theorem gamma_ramp_prime_trivial_false_uniform {n : ℕ} (hn : Odd n)
    (χ : DirichletCharacter ℂ (4 * n)) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hq : 20000 ≤ 4 * n)
    {L : ℝ} (hL : 46000 ≤ L) (hlogq : Real.log (4 * n : ℕ) ≤ L + 2)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ¬(∀ p : ℕ,
        p.Prime → ¬p ∣ 4 * n → (p : ℝ) ≤ (99 / 40 : ℝ) * ((32 / 99 : ℝ) * L ^ 2) → χ p = 1) := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  intro hsmall
  have hx := zero_lt_one.trans_le (Analysis.ramp_scale_ge_one hL)
  have hQ := gamma_ramp_no_witness_comparison χ hquad hx hsmall
  have hlo := gamma_ramp_sum_lower_seven hGRH.riemann hL
  have hP := PaperStatements.gamma_level_one_sum_upper_one_fifth hGRH.riemann hL
  have hC :=
    PaperStatements.gamma_primitiveCharacter_sum_re_le_smoothed_at_ramp_scale hq χ hne hGRH hL hlogq
  have hE := gammaQuadraticLocalCorrection_absorbed_uniform hn χ hquad hq hL hlogq
  apply Analysis.gamma_ramp_inequality_false_of_log_ge hL
  nlinarith only [hQ, hlo, hP, hC, hE]

end PseudoPrime.LLS
