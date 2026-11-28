/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMellinPhase656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMellinPhase656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseRemainder656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalCorrection644
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Lower-end cancellation for the section 132 Mellin moment -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The two physical lower-cutoff corrections for a zero at squared radius
`X`. The first restores the omitted moment and the second retains the
boundary term at physical argument one. -/
noncomputable def quarterPhaseCorrection656 (X : ℝ) (ρ : ℂ) : ℝ :=
  let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
  let p := (X : ℂ) ^ ρ / (Real.sqrt X : ℂ)
  let C := (11 / 10 : ℝ) ^ 5 * Real.exp (-(21 / 8 * (11 / 10))) / 120
  3 * C * (m * p * quarterMoment656 (ρ + 3 / 5) (1 / X)).re + 3 * (-m / ρ).re * quarterWeight656 X 1

/-- The cutoff phase cancels the phase of the lower-end power. Its
product is the real decay factor at the physical endpoint one. -/
private theorem lower_power_cancel {X : ℝ} (hX : 0 < X) (ρ : ℂ) :
    ((X : ℂ) ^ ρ / (Real.sqrt X : ℂ)) * ((1 / X : ℝ) : ℂ) ^ (ρ + 3 / 5) =
      (X ^ (-(11 / 10 : ℝ)) : ℝ) := by
  have hx : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hy : ((1 / X : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (one_div_pos.mpr hX).ne'
  have hpow : (X : ℂ) ^ ρ * ((1 / X : ℝ) : ℂ) ^ (ρ + 3 / 5) = (X ^ (-(3 / 5 : ℝ)) : ℝ) := by
    rw [Complex.cpow_def_of_ne_zero hx, Complex.cpow_def_of_ne_zero hy, Complex.ofReal_cpow hX.le,
      Complex.cpow_def_of_ne_zero hx, ← Complex.ofReal_log hX.le, ←
      Complex.ofReal_log (one_div_pos.mpr hX).le, one_div, Real.log_inv, Complex.ofReal_neg, ←
      Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  rw [div_mul_eq_mul_div, hpow, ← Complex.ofReal_div, Real.sqrt_eq_rpow, ← Real.rpow_sub hX]
  rw [show -(3 / 5 : ℝ) - 1 / 2 = -(11 / 10) by ring]

/-- The physical weight at one has the same decay factor and shifted
logarithm as the lower-end Mellin correction. -/
private theorem weight_one_power_656 {X : ℝ} (hX : 0 < X) :
    quarterWeight656 X 1 =
      ((11 / 10 : ℝ) ^ 5 * Real.exp (-(21 / 8 * (11 / 10))) / 120) *
        (X ^ (-(11 / 10 : ℝ)) * (21 / 8 + Real.log X) ^ 5) := by
  unfold quarterWeight656
  dsimp only
  rw [Real.sqrt_one, one_div_one, one_mul, one_div, Real.log_inv, sub_neg_eq_add]
  rw [Real.rpow_def_of_pos hX]
  have he :
    -((11 / 10) * (21 / 8 + Real.log X)) = -(21 / 8 * (11 / 10)) + Real.log X * -(11 / 10) := by
    ring
  rw [he, Real.exp_add]
  ring

/-- Both lower-end corrections in a zero contribution share a real decay
factor. The remaining expression uses the shifted logarithmic polynomial
and the reciprocal from the boundary value. -/
private theorem correction_formula {X : ℝ} (hX : 1 ≤ X) (ρ : ℂ) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let s := ρ + (3 / 5 : ℂ)
    let b := 21 / 8 + Real.log X
    let C := ((11 / 10 : ℝ) ^ 5 * Real.exp (-(21 / 8 * (11 / 10))) / 120 : ℝ)
    quarterPhaseCorrection656 X ρ =
      3 * C * X ^ (-(11 / 10 : ℝ)) *
        ((m *
              (∑ j ∈ Finset.range 6,
                (((5 : ℕ).choose j : ℂ) * (b : ℂ) ^ (5 - j)) *
                  ((j.factorial : ℂ) / s ^ (j + 1)))).re +
          (-m / ρ).re * b ^ 5) := by
  intro m s b C
  let p := (X : ℂ) ^ ρ / (Real.sqrt X : ℂ)
  have hx := zero_lt_one.trans_le hX
  let A :=
    ∑ j ∈ Finset.range 6,
      (((5 : ℕ).choose j : ℂ) * (b : ℂ) ^ (5 - j)) * ((j.factorial : ℂ) / s ^ (j + 1))
  have hM : quarterMoment656 s (1 / X) = ((1 / X : ℝ) : ℂ) ^ s * A := by
    unfold quarterMoment656
    rw [show (21 / 8 - Real.log (1 / X) : ℝ) = b
        by
        dsimp only [b]
        rw [one_div, Real.log_inv, sub_neg_eq_add]]
  have hP : p * ((1 / X : ℝ) : ℂ) ^ s = (X ^ (-(11 / 10 : ℝ)) : ℝ) := lower_power_cancel hx ρ
  change
    3 * C * (m * p * quarterMoment656 s (1 / X)).re + 3 * (-m / ρ).re * quarterWeight656 X 1 = _
  rw [hM, weight_one_power_656 hx]
  rw [show m * p * (((1 / X : ℝ) : ℂ) ^ s * A) = (p * ((1 / X : ℝ) : ℂ) ^ s) * (m * A) by ring, hP]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  dsimp only [C, b]
  ring

/-- The lower-end coefficient after the first reciprocal cancels with
the boundary term. Every remaining denominator has degree at least two. -/
noncomputable def quarterLowerKernel656 (b : ℝ) (ρ : ℂ) : ℂ :=
  let s := ρ + (3 / 5 : ℂ)
  (-((b : ℂ) ^ 5 * (3 / 5) / (ρ * s)) +
    (∑ j ∈ Finset.range 5,
      (((5 : ℕ).choose (j + 1) : ℂ) * (b : ℂ) ^ (5 - (j + 1))) *
        (((j + 1).factorial : ℂ) / s ^ ((j + 1) + 1))))

/-- The lower endpoint contributes the real part of the cancelled
coefficient times the real cutoff decay factor and the zero multiplicity. -/
theorem quarter_correction_cancel_656 {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hn : ρ ≠ 0)
    (hρ : 0 < ρ.re + 3 / 5) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let b := 21 / 8 + Real.log X
    let C := ((11 / 10 : ℝ) ^ 5 * Real.exp (-(21 / 8 * (11 / 10))) / 120 : ℝ)
    quarterPhaseCorrection656 X ρ =
      3 * C * X ^ (-(11 / 10 : ℝ)) * (m * quarterLowerKernel656 b ρ).re := by
  intro m b C
  let s := ρ + (3 / 5 : ℂ)
  have hs : s ≠ 0 := by
    have hre : 0 < s.re := by
      dsimp only [s]
      norm_num only [Complex.add_re, Complex.div_ofNat_re]
      exact hρ
    intro he
    rw [he, Complex.zero_re] at hre
    exact (lt_irrefl _ hre)
  have hdiff : (1 : ℂ) / s - 1 / ρ = -(3 / 5) / (ρ * s) := by
    field_simp [hn, hs]
    dsimp only [s]
    ring
  let A :=
    ∑ j ∈ Finset.range 6,
      (((5 : ℕ).choose j : ℂ) * (b : ℂ) ^ (5 - j)) * ((j.factorial : ℂ) / s ^ (j + 1))
  have hA : m * A + (-m / ρ) * (b : ℂ) ^ 5 = m * quarterLowerKernel656 b ρ := by
    unfold A quarterLowerKernel656
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, Nat.factorial_zero, Nat.zero_add,
      pow_one, one_mul, mul_one_div]
    change _ = m * (-((b : ℂ) ^ 5 * (3 / 5) / (ρ * s)) + _)
    rw [show -((b : ℂ) ^ 5 * (3 / 5) / (ρ * s)) = (b : ℂ) ^ 5 * (1 / s - 1 / ρ) by
        rw [hdiff]; ring]
    ring
  have h := correction_formula hX ρ
  change
    quarterPhaseCorrection656 X ρ =
      3 * C * X ^ (-(11 / 10 : ℝ)) * ((m * A).re + (-m / ρ).re * b ^ 5) at h
  rw [h]
  have hre : (((-m / ρ) * (b : ℂ) ^ 5)).re = (-m / ρ).re * b ^ 5 := by
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
  rw [← hre, ← Complex.add_re, hA]

/-- The cancelled lower kernel is bounded by 11/10 times the fifth power of the
shift divided by the squared ordinate, for shifts at least fourteen. -/
private theorem lower_kernel_bound {b : ℝ} (hb : 14 ≤ b) {ρ : ℂ} (ht : 1 ≤ |ρ.im|) :
    ‖quarterLowerKernel656 b ρ‖ ≤ (11 / 10) * b ^ 5 / |ρ.im| ^ 2 := by
  let t := |ρ.im|
  let s := ρ + (3 / 5 : ℂ)
  have hb0 : 0 ≤ b := by linarith only [hb]
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hρ : t ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have hs : t ≤ ‖s‖ := by
    have he : s.im = ρ.im := by
      dsimp only [s]
      rw [Complex.add_im, ← Complex.ofReal_ofNat, ← Complex.ofReal_ofNat, ← Complex.ofReal_div,
        Complex.ofReal_im, add_zero]
    rw [show t = |s.im| from congrArg abs he.symm]
    exact Complex.abs_im_le_norm s
  have hprod : t ^ 2 ≤ ‖ρ‖ * ‖s‖ := by
    rw [sq]
    exact mul_le_mul hρ hs ht0.le (norm_nonneg _)
  have hpow (n : ℕ) (h : 2 ≤ n) : t ^ 2 ≤ ‖s‖ ^ n :=
    (pow_le_pow_left₀ ht0.le hs 2).trans (pow_le_pow_right₀ (ht.trans hs) h)
  let F := fun j : ℕ ↦
    (((5 : ℕ).choose (j + 1) : ℂ) * (b : ℂ) ^ (5 - (j + 1))) *
      (((j + 1).factorial : ℂ) / s ^ ((j + 1) + 1))
  have hF (j : ℕ) :
    ‖F j‖ ≤
      (((5 : ℕ).choose (j + 1) : ℝ) * b ^ (5 - (j + 1)) * ((j + 1).factorial : ℝ)) / t ^ 2 := by
    simp only [F, norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg hb0, ← mul_div_assoc]
    exact
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ht0)
        (hpow _ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le j))))
  have hA : ‖-((b : ℂ) ^ 5 * (3 / 5) / (ρ * s))‖ ≤ b ^ 5 * (3 / 5) / t ^ 2 := by
    simp only [norm_neg, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hb0,
      Complex.norm_ofNat]
    exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ht0) hprod
  change ‖-((b : ℂ) ^ 5 * (3 / 5) / (ρ * s)) + ∑ j ∈ Finset.range 5, F j‖ ≤ _
  apply (norm_add_le _ _).trans
  refine (add_le_add hA ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hF j))).trans ?_
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
    Nat.choose, Nat.factorial, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, zero_add,
    add_zero, pow_zero, pow_one, mul_one, one_mul]
  change _ ≤ (11 / 10) * b ^ 5 / t ^ 2
  rw [← add_div, ← add_div, ← add_div, ← add_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have h₁ := mul_le_mul_of_nonneg_left hb (pow_nonneg hb0 4)
  have h₂ := mul_le_mul_of_nonneg_left hb (pow_nonneg hb0 3)
  have h₃ := mul_le_mul_of_nonneg_left hb (pow_nonneg hb0 2)
  have h₄ := mul_le_mul_of_nonneg_left hb hb0
  nlinarith only [h₁, h₂, h₃, h₄, hb]

/-- For shifted logarithm at least fourteen and ordinate modulus at least
one, the cancelled correction is bounded by 3.3 times the endpoint weight
times the multiplicity divided by the squared ordinate. -/
theorem quarter_correction_bound_656 {X : ℝ} (hX : 1 ≤ X) (hb : 14 ≤ 21 / 8 + Real.log X) {ρ : ℂ}
    (ht : 1 ≤ |ρ.im|) (hr : ρ.re = 1 / 2) :
    |quarterPhaseCorrection656 X ρ| ≤
      (33 / 10) * quarterWeight656 X 1 *
        ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) := by
  let m := AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ
  let b := 21 / 8 + Real.log X
  let C := (11 / 10 : ℝ) ^ 5 * Real.exp (-(21 / 8 * (11 / 10))) / 120
  let d := X ^ (-(11 / 10 : ℝ))
  have hn : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hr
    norm_num only at hr
  have hρ : 0 < ρ.re + 3 / 5 := by
    rw [hr]; norm_num only
  have he := quarter_correction_cancel_656 hX hn hρ
  change quarterPhaseCorrection656 X ρ = 3 * C * d * ((m : ℂ) * quarterLowerKernel656 b ρ).re at he
  rw [he, abs_mul,
    abs_of_nonneg
      (by
        dsimp only [C, d]; positivity)]
  have h := Complex.abs_re_le_norm ((m : ℂ) * quarterLowerKernel656 b ρ)
  rw [norm_mul, Complex.norm_natCast] at h
  have hh := h.trans (mul_le_mul_of_nonneg_left (lower_kernel_bound hb ht) (Nat.cast_nonneg m))
  refine
    (mul_le_mul_of_nonneg_left hh
          (by
            dsimp only [C, d]; positivity)).trans_eq
      ?_
  rw [weight_one_power_656 (zero_lt_one.trans_le hX)]
  change
    3 * C * d * ((m : ℝ) * ((11 / 10) * b ^ 5 / |ρ.im| ^ 2)) =
      33 / 10 * (C * (d * b ^ 5)) * ((m : ℝ) / |ρ.im| ^ 2)
  ring

private theorem correction_weight {r : ℝ} (hr : r ∈ Set.Icc 322 328) :
    quarterWeight656 (r ^ 2) 1 ≤ 0.0014 := by
  have hp := (by norm_num only : (0 : ℝ) < 322).trans_le hr.1
  have hU :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo :=
        5793013606044 / 1000000000000) (hi := 5793013610546 / 1000000000000) (by decide +kernel)).2
  simp only [Rat.cast_div, Rat.cast_ofNat] at hU
  let z := 21 / 8 + 2 * Real.log r
  have hlo : 14.174103 ≤ z := by
    dsimp only [z]
    linarith only [log_322_bounds.1, Real.log_le_log (by norm_num only : (0 : ℝ) < 322) hr.1]
  have hhi : z ≤ 14.25 := by
    dsimp only [z]
    linarith only [hU, Real.log_le_log hp hr.2]
  have hpow :=
    pow_le_pow_left₀ (by linarith only [hlo] : 0 ≤ (11 / 10) * z)
      (show (11 / 10) * z ≤ (11 / 10) * 14.25 by linarith only [hhi]) 5
  have h := mul_le_mul hpow (rem_exp_322 hlo) (Real.exp_pos _).le (by norm_num only)
  unfold quarterWeight656
  simp only [Real.sqrt_one, one_div, inv_one, one_mul, Real.log_inv, sub_neg_eq_add, Real.log_pow]
  change ((11 / 10) * z) ^ 5 * Real.exp (-((11 / 10) * z)) / 120 ≤ _
  rw [← neg_mul]
  linarith only [h]

/-- For every finite nontrivial zero family under RH, the physical
lower-end correction has total absolute contribution at most 0.000234
throughout the section 132 radius range. -/
theorem quarter_correction_sum_656 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 322 328)
    (S : Finset ℂ) (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ S, |quarterPhaseCorrection656 (r ^ 2) ρ|) ≤ 0.000234 := by
  have hp := (by norm_num only : (1 : ℝ) ≤ 322).trans hr.1
  have hX := one_le_pow₀ hp (n := 2)
  have hb : 14 ≤ 21 / 8 + Real.log (r ^ 2) := by
    rw [Real.log_pow]
    linarith only [log_322_bounds.1, Real.log_le_log (by norm_num only : (0 : ℝ) < 322) hr.1]
  have hS := finite_ordinate_mass hRH S hz hre
  calc
    _ ≤
        ∑ ρ ∈ S,
          (33 / 10) * 0.0014 *
            ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) :=
      by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hξ :=
        AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hz ρ hρ) (hre ρ hρ)
      have ht := AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH (hz ρ hρ) (hre ρ hρ)
      have hρr := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hξ
      refine
        (quarter_correction_bound_656 hX hb (by linarith only [ht, Real.pi_gt_three]) hρr).trans ?_
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (correction_weight hr) (by norm_num only)) (by positivity)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      linarith only [hS]

/-- For a complete truncation above height 100, add the actual two
lower-cutoff corrections to the normalized section 132 Mellin sum. -/
theorem quarter_corrected_truncation_656 (hRH : RiemannHypothesis) {r T : ℝ}
    (hr : r ∈ Set.Icc 322 328) (hT : 100 ≤ T) :
    (-0.002594 : ℝ) ≤
      ∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
        ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            ((((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ)) * quarterMellinPhase656 ρ).re +
          quarterPhaseCorrection656 (r ^ 2) ρ) := by
  let S := AnalyticNumberTheory.RiemannZeta.zerosUpTo T
  have h0 := (by norm_num only : (0 : ℝ) ≤ 100).trans hT
  have hm {ρ : ℂ} (hρ : ρ ∈ S) := (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo h0).mp hρ
  have hc := quarter_correction_sum_656 hRH hr S (fun _ hρ ↦ (hm hρ).1) (fun _ hρ ↦ (hm hρ).2.1)
  have hd :
    -(∑ ρ ∈ S, |quarterPhaseCorrection656 (r ^ 2) ρ|) ≤
      ∑ ρ ∈ S, quarterPhaseCorrection656 (r ^ 2) ρ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun ρ _ ↦ neg_abs_le _)
  have hb := quarter_phase_truncations_656 hRH hr hT
  have hM :
    (-0.00236 : ℝ) ≤
      ∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          ((((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ)) * quarterMellinPhase656 ρ).re := by
    have he :
      (∑ ρ ∈ S,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            ((((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ)) * quarterMellinPhase656 ρ).re) =
        ∑ ρ ∈ S,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            (Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) *
                quarterPhaseKernel656 ρ.im).re := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      have hx :=
        AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hm hρ).1 (hm hρ).2.1
      rw [quarter_mellin_cutoff_phase_656 ((by norm_num only : (0 : ℝ) < 322).trans_le hr.1)
          (AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hx)]
    rw [he]
    exact
      (show (-0.00236 : ℝ) = -(201 / 40000) + 2665 / 1000000 by norm_num only).le.trans
        (le_sub_iff_add_le.mp hb)
  rw [Finset.sum_add_distrib]
  linarith only [hM, hc, hd]

end PseudoPrime.PrimeTestBounds.MillerRabin
