/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAbel570
import PseudoPrime.LLS.ClippedLogShiftPrincipalBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Centered endpoint error for the section 31 principal weight -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At the arithmetic cutoff the logarithmic derivative of the weight is -443/350
times the weight. The fifth power, exponential, and inverse square root each contribute. -/
theorem quarter_cutoff_deriv_570 {X : ℝ} (hx : 0 < X) :
    X * deriv (quarterWeight570 X) X = -(443 / 350) * quarterWeight570 X X := by
  let v := fun t : ℝ ↦ (2 * (7 / 5) - Real.log (t / X)) / (2 * (25 / 51))
  have hv : v X = 357 / 125 := by norm_num only [v, div_self hx.ne', Real.log_one, sub_zero]
  have hlog :=
    ((hasDerivAt_id X).div_const X).log
      (by simpa only [id_eq, div_self hx.ne'] using (one_ne_zero : (1 : ℝ) ≠ 0))
  have hd := ((hasDerivAt_const X (2 * (7 / 5 : ℝ))).sub hlog).div_const (2 * (25 / 51 : ℝ))
  have hvd : HasDerivAt v (-(51 / 50) / X) X := by
    apply hd.congr_deriv
    simp only [id_eq, div_self hx.ne', div_one]
    ring
  have hf :=
    ((hasDerivAt_const X (1 : ℝ)).div (Real.hasDerivAt_sqrt hx.ne') (Real.sqrt_pos.mpr hx).ne').mul
      (((hvd.pow 5).mul hvd.neg.exp).div_const 120)
  change X * deriv (fun t : ℝ ↦ 1 / Real.sqrt t * (v t ^ 5 * Real.exp (-v t) / 120)) X = _
  rw [show deriv (fun t : ℝ ↦ 1 / Real.sqrt t * (v t ^ 5 * Real.exp (-v t) / 120)) X = _ from
      hf.deriv]
  change _ = -(443 / 350) * (1 / Real.sqrt X * (v X ^ 5 * Real.exp (-v X) / 120))
  simp only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, hv]
  field_simp [hx.ne', (Real.sqrt_pos.mpr hx).ne']
  nlinarith only [Real.sq_sqrt hx.le]

/-- For r at least 278 under RH, the endpoint term in the centered Abel identity
has absolute value less than 1/40. The bound includes the factor four from the cutoff sum. -/
theorem quarter_endpoint_error_570 {r : ℝ} (hr : 278 ≤ r) (hRH : RiemannHypothesis) :
    let X := r ^ 2
    let E :=
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum X -
        (X - Real.log (2 * Real.pi) * Real.log X)
    |4 * (X * deriv (quarterWeight570 X) X) * E| < 1 / 40 := by
  intro X E
  have hr0 : 0 < r := by linarith only [hr]
  have hx : 0 < X := sq_pos_of_pos hr0
  have hx1 : 1 ≤ X :=
    (by norm_num only : (1 : ℝ) ≤ 278 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr 2)
  have he := LLS.clippedShiftError_abs_le hRH (x := 1) (u := X) zero_lt_one hx.le
  simp only [LLS.clippedShiftError, one_mul, div_one, Analysis.positiveLogRatio_eq_log hx1] at he
  have hE : |E| ≤ r / 20 + 21 / 20 := by
    dsimp only [E, X] at he ⊢
    rw [Real.sqrt_sq hr0.le] at he
    convert he using 2; ring
  have hw : quarterWeight570 X X = (quarterKernel570.transform 1).re / r := by
    rw [quarterKernel570, LLS.PaperStatements.rationalPole_transform _ _ _ _ zero_lt_one,
      Complex.ofReal_re]
    simp only [quarterWeight570, div_self hx.ne', Real.log_one, sub_zero,
      Analysis.rationalPoleProfile]
    dsimp only [X]
    rw [Real.sqrt_sq hr0.le]
    norm_num only [Nat.factorial, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat]
    ring_nf
    simp only [and_self, ite_true, mul_assoc]
  obtain ⟨hlo, hhi⟩ := quarter_unit_weight_570
  have hz : 0 ≤ (quarterKernel570.transform 1).re := by linarith only [hlo]
  rw [quarter_cutoff_deriv_570 hx, hw, abs_mul, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (div_nonneg hz hr0.le)]
  norm_num only [abs_div]
  have hm := mul_le_mul hhi.le hE (abs_nonneg E) (by norm_num only)
  field_simp [hr0.ne']
  nlinarith only [hm, hr]

/-- Under RH, replacing the residual endpoint by its certified absolute bound
leaves only the combined remainder integrals to estimate for radii at least 278. -/
theorem quarter_integral_lower_570 {r : ℝ} (hr : 278 ≤ r) (hRH : RiemannHypothesis) :
    let X := r ^ 2
    let B := X * Real.exp (14 / 5)
    let W := quarterWeight570 X
    let P := fun t ↦ t * deriv W t
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    let c := Real.log (2 * Real.pi)
    let E := fun t ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - (t - c * Real.log t)
    4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..B, W t) +
              (4 * (∫ t in (1 : ℝ)..X, E t * deriv P t) - (∫ t in (1 : ℝ)..B, E t * deriv P t)) +
              4 * W X * (Chebyshev.psi X - X + c) -
            3 * P 1 +
          3 * (1 - c) * W 1 -
        1 / 40 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  intro X B W P S c E
  have hx : 1 ≤ X :=
    (by norm_num only : (1 : ℝ) ≤ 278 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr 2)
  have he := (abs_lt.mp (quarter_endpoint_error_570 hr hRH)).2
  rw [quarter_centered_difference_570 hx]
  dsimp only [X, B, W, P, S, c, E] at *
  linarith only [he]

end PseudoPrime.PrimeTestBounds.MillerRabin
