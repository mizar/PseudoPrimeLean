/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaQuadraticLocalCorrection
public import PseudoPrime.Analysis.QuadraticGammaSmoothedNumerics
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaFiniteCertificates
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Fixed-scale signed quadratic local budget

The elementary prime-factor estimate controls the original level without Robin.
Conductor absorption yields an additive allowance of six at the fixed scale.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- For positive L, log((99/40)(32/99)L²) is at most 2log(L).
The cutoff equals (4/5)L²; the coefficient's logarithm is nonpositive.
This retains the logarithmic cancellation in the prime-factor cost. -/
theorem ramp_cutoff_log_le_two_log {L : ℝ} (hL : 0 < L) :
    Real.log ((99 / 40 : ℝ) * ((32 / 99 : ℝ) * L ^ 2)) ≤ 2 * Real.log L := by
  have he : (99 / 40 : ℝ) * ((32 / 99 : ℝ) * L ^ 2) = (4 / 5 : ℝ) * L ^ 2 := by ring
  rw [he, Real.log_mul (by norm_num only) (pow_ne_zero _ hL.ne'), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [Real.log_nonpos (by norm_num only : (0 : ℝ) ≤ 4 / 5)
      (by norm_num only : (4 / 5 : ℝ) ≤ 1)]

/-- For positive n, log(4n)=log(n)+log(4). The product-log identity records
the original-level shift before the final conductor comparison. -/
theorem log_original_quadratic_level {n : ℕ} (hn : 0 < n) :
    Real.log (4 * n : ℕ) = Real.log n + Real.log 4 := by
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num only) (Nat.cast_ne_zero.mpr hn.ne')]
  ring

/-- The logarithm of four is at most two. Write 4=2² and use the certified log(2) bound.
This supplies the additive original-level allowance. -/
theorem log_four_le_two : Real.log (4 : ℝ) ≤ 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num only, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [Real.log_two_lt_d9]

/-- For odd n with log(n)≥46000, the original-level prime-factor cost at the
fixed ramp scale is at most five. Apply the unconditional elementary omega bound,
retain its loglog denominator and use log(X)≤2log(log(n)) and the square-root bound.
The estimate includes prime two and square-part primes. -/
theorem gamma_quadratic_prime_factor_cost_le_five {n : ℕ} (hn : Odd n) (hL : 46000 ≤ Real.log n) :
    ((4 * n).primeFactors.card : ℝ) *
          Real.log ((99 / 40 : ℝ) * ((32 / 99 : ℝ) * (Real.log n) ^ 2)) /
        Real.sqrt ((32 / 99 : ℝ) * (Real.log n) ^ 2) ≤
      5 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Odd.pos hn
  have hn750 : 750 ≤ n := by
    have hself := Real.log_le_self hnR.le
    have hr : (750 : ℝ) ≤ n := by linarith only [hL, hself]
    exact_mod_cast hr
  have hL0 : 0 < Real.log n := by linarith only [hL]
  have hlogq := log_original_quadratic_level (Odd.pos hn)
  have hqlo : Real.log n ≤ Real.log (4 * n : ℕ) := by
    rw [hlogq]
    linarith only [Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 4)]
  have hqhi : Real.log (4 * n : ℕ) ≤ Real.log n + 2 := by
    rw [hlogq]
    linarith only [log_four_le_two]
  have hdpos : 0 < Real.log (Real.log (4 * n : ℕ)) := Real.log_pos (by linarith only [hqlo, hL])
  have hloglo := Real.log_le_log hL0 hqlo
  have hcut := ramp_cutoff_log_le_two_log hL0
  have hcutden :
    Real.log ((99 / 40 : ℝ) * ((32 / 99 : ℝ) * (Real.log n) ^ 2)) ≤
      2 * Real.log (Real.log (4 * n : ℕ)) := by
    linarith only [hcut, hloglo]
  have hw := AnalyticNumberTheory.Arithmetic.elementaryOmegaStatement n hn hn750
  change
    ((4 * n).primeFactors.card : ℝ) ≤
      (7 / 5 : ℝ) * Real.log (4 * n : ℕ) / Real.log (Real.log (4 * n : ℕ)) at hw
  have hwmul := (le_div_iff₀ hdpos).mp hw
  have hterm :=
    mul_le_mul_of_nonneg_left hcutden
      (Nat.cast_nonneg (4 * n).primeFactors.card : (0 : ℝ) ≤ (4 * n).primeFactors.card)
  have hbudget :
    ((4 * n).primeFactors.card : ℝ) *
        Real.log ((99 / 40 : ℝ) * ((32 / 99 : ℝ) * (Real.log n) ^ 2)) ≤
      (14 / 5 : ℝ) * Real.log (4 * n : ℕ) := by
    nlinarith only [hwmul, hterm]
  have hroot := Analysis.ramp_scale_sqrt_lower hL0.le
  have hs : 0 < Real.sqrt ((32 / 99 : ℝ) * (Real.log n) ^ 2) := by linarith only [hroot, hL]
  rw [div_le_iff₀ hs]
  nlinarith only [hbudget, hqhi, hroot, hL]

/-- For odd n with log(n)≥46000 and a quadratic character of level 4n,
Mlog(conductor) plus the actual signed local correction is at most Mlog(n)+6.
Absorb the conductor quotient first, then bound the prime-factor cost by five
and Mlog(4) by one. This is the local budget in the smoothed witness comparison. -/
theorem gammaQuadraticLocalCorrection_absorbed_at_ramp_scale {n : ℕ} (hn : Odd n)
    (χ : DirichletCharacter ℂ (4 * n)) (hquad : χ.IsQuadratic) (hL : 46000 ≤ Real.log n) :
    (11783423 / 25000000 : ℝ) * Real.log χ.conductor +
        gammaQuadraticLocalCorrection χ ((32 / 99 : ℝ) * (Real.log n) ^ 2) ≤
      (11783423 / 25000000 : ℝ) * Real.log n + 6 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  have hx1 := Analysis.ramp_scale_ge_one hL
  have hxpos := zero_lt_one.trans_le hx1
  have hcut : (1 : ℝ) ≤ (99 / 40) * ((32 / 99 : ℝ) * (Real.log n) ^ 2) := by nlinarith only [hx1]
  have hroot := Analysis.ramp_scale_sqrt_lower (by linarith only [hL])
  have hM : (1 : ℝ) ≤ (11783423 / 25000000) * Real.sqrt ((32 / 99 : ℝ) * (Real.log n) ^ 2) := by
    nlinarith only [hroot, hL]
  have hcorr := gammaQuadraticLocalCorrection_absorb_conductor χ hquad hxpos hcut hM
  have hcost := gamma_quadratic_prime_factor_cost_le_five hn hL
  have hfour : (11783423 / 25000000 : ℝ) * Real.log 4 ≤ 1 := by
    have hm :=
      mul_le_mul_of_nonneg_left log_four_le_two (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
    nlinarith only [hm]
  rw [log_original_quadratic_level (Odd.pos hn)] at hcorr
  nlinarith only [hcorr, hcost, hfour]

end PseudoPrime.LLS
