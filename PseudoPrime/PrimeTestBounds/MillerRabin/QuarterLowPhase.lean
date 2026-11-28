/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipal600
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseCurvature
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalZeros
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaLedger
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Complex phase representation of the quarter-kernel zero coefficients -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Taking the real part of a complex exponential phase gives a cosine term
and a sine term with the negated imaginary coefficient. -/
theorem complex_phase_re (c : ℂ) (x : ℝ) :
    (c * Complex.exp ((x : ℂ) * Complex.I)).re = c.re * Real.cos x + (-c.im) * Real.sin x := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, sub_zero]
  ring

/-- Bound a finite sum of complex phases on a closed radius interval.
The coefficient and frequency bounds control the curvature uniformly.
Only the two endpoint sums need lower bounds. -/
theorem complex_phase_interval_lower {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ d H A B : ι → ℝ)
    {l r u M L U : ℝ} (hl : 0 < l) (hr : r ∈ Set.Icc l u) (hγ : ∀ j ∈ s, |γ j| ≤ H j)
    (hA : ∀ j ∈ s, |(c j).re| ≤ A j) (hB : ∀ j ∈ s, |(c j).im| ≤ B j)
    (hM : ∑ j ∈ s, (H j) ^ 2 * (A j + B j) ≤ M)
    (hL :
      L ≤ ∑ j ∈ s, (c j * Complex.exp (((γ j * (2 * Real.log l + d j) : ℝ) : ℂ) * Complex.I)).re)
    (hU :
      U ≤ ∑ j ∈ s, (c j * Complex.exp (((γ j * (2 * Real.log u + d j) : ℝ) : ℂ) * Complex.I)).re) :
    min L U - M * (u - l) ^ 2 / (2 * l ^ 2) ≤
      ∑ j ∈ s, (c j * Complex.exp (((γ j * (2 * Real.log r + d j) : ℝ) : ℂ) * Complex.I)).re := by
  have hc : ∑ j ∈ s, (γ j) ^ 2 * (|(c j).re| + |-(c j).im|) ≤ M := by
    apply (Finset.sum_le_sum (fun j hj ↦ ?_)).trans hM
    rw [abs_neg, ← sq_abs (γ j)]
    exact
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hγ j hj) 2) (add_le_add (hA j hj) (hB j hj))
        (add_nonneg (abs_nonneg _) (abs_nonneg _)) (sq_nonneg _)
  have h := finite_phase_lower s (fun j ↦ (c j).re) (fun j ↦ -(c j).im) γ d hl hr hc
  dsimp only at h
  simp_rw [complex_phase_re] at hL hU ⊢
  exact (sub_le_sub_right (min_le_min hL hU) _).trans h

/-- A positive real base to a complex exponent on a vertical line splits
into its real radial factor and a unit complex phase. -/
theorem vertical_cpow_split {X : ℝ} (hX : 0 < X) (a t : ℝ) :
    (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I) =
      (X ^ a : ℝ) * Complex.exp (((t * Real.log X : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne'), ← Complex.ofReal_log hX.le,
    mul_add, Complex.exp_add, Real.rpow_def_of_pos hX, Complex.ofReal_exp, Complex.ofReal_mul,
    Complex.ofReal_mul]
  congr 1
  congr 1
  ring

/-- After dividing by the square root, a critical-line power at the squared
radius is a complex phase with logarithmic argument twice the log radius. -/
theorem quarter_cutoff_phase_exp {r t : ℝ} (hr : 0 < r) :
    ((r ^ 2 : ℝ) : ℂ) ^ ((1 / 2 : ℝ) + (t : ℂ) * Complex.I) / (Real.sqrt (r ^ 2) : ℂ) =
      Complex.exp (((t * (2 * Real.log r) : ℝ) : ℂ) * Complex.I) := by
  rw [vertical_cpow_split (sq_pos_of_pos hr), ← Real.sqrt_eq_rpow, Real.log_pow, Nat.cast_ofNat,
    mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sq_pos_of_pos hr)).ne')]

/-- The unshifted coefficient of the sixth-pole kernel at a critical-line
ordinate. It retains the common numerator so interval evaluation preserves
the exact cancellations. -/
@[expose]
noncomputable def section99RatCoeff (t : ℝ) : ℂ :=
  let ρ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  let s := (51 / 50 : ℂ) + (t : ℂ) * Complex.I
  let C := (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) : ℝ)
  (C : ℂ) * (4 * section104Numerator s / (ρ * s ^ 6))

/-- The coefficient of the phase shifted by `14/5`. The positive real
exponential from the moment cancels the decaying exponential in its factor. -/
@[expose]
noncomputable def section99PoleCoeff (t : ℝ) : ℂ :=
  (51 / 50 : ℂ) ^ 5 / ((51 / 50 : ℂ) + (t : ℂ) * Complex.I) ^ 6

/-- The critical-line sixth-pole phase kernel splits into the rational term
and a phase shifted by `14/5`, with exactly the two coefficients used by
the finite ordinate certificates. -/
theorem section99_phase_coeff_split (t : ℝ) :
    section99PhaseKernel ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
      section99RatCoeff t +
        section99PoleCoeff t * Complex.exp (((t * (14 / 5) : ℝ) : ℂ) * Complex.I) := by
  let ρ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  let s := (51 / 50 : ℂ) + (t : ℂ) * Complex.I
  have hs : ρ + (13 / 25 : ℂ) = s := by
    dsimp only [ρ, s]
    ring
  have hne (a : ℝ) (ha : a ≠ 0) : (a : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    apply ha
    simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] using congrArg Complex.re h
  have hrho : ρ ≠ 0 := by
    simpa only [ρ, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      hne (1 / 2) (by norm_num only)
  have hs0 : ρ + (13 / 25 : ℂ) ≠ 0 := by
    rw [hs]
    simpa only [s, Complex.ofReal_div, Complex.ofReal_ofNat] using hne (51 / 50) (by norm_num only)
  have hp :
    (Real.exp (14 / 5) : ℂ) ^ s =
      (Real.exp (14 / 5 * (51 / 50)) : ℂ) * Complex.exp (((t * (14 / 5) : ℝ) : ℂ) * Complex.I) := by
    have h := vertical_cpow_split (Real.exp_pos (14 / 5)) (51 / 50) t
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at h
    simpa only [s, Complex.ofReal_div, Complex.ofReal_ofNat] using h
  change section99PhaseKernel ρ = _
  rw [section99_phase_kernel_rational hrho hs0]
  rw [hs, hp]
  have hC :
    ((Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120) : ℝ) : ℂ) *
        (Real.exp (14 / 5 * (51 / 50)) : ℂ) *
        120 =
      (51 / 50 : ℂ) ^ 5 := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ←
      Complex.ofReal_ofNat (n := 51), ← Complex.ofReal_ofNat (n := 50), ← Complex.ofReal_div, ←
      Complex.ofReal_pow]
    congr 1
    rw [div_mul_eq_mul_div, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    norm_num only
  change _ = _ + _
  dsimp only [section99RatCoeff, section99PoleCoeff]
  change _ = _ + (51 / 50 : ℂ) ^ 5 / s ^ 6 * _
  rw [← hC]
  ring

/-- The unshifted and shifted phase terms at a squared radius add to the
real normalized kernel value for one ordinate. -/
theorem section99_phase_re_split {r : ℝ} (hr : 0 < r) (t : ℝ) :
    let ρ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
    ((((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ)) * section99PhaseKernel ρ).re =
      (section99RatCoeff t * Complex.exp (((t * (2 * Real.log r) : ℝ) : ℂ) * Complex.I)).re +
        (section99PoleCoeff t *
            Complex.exp (((t * (2 * Real.log r + 14 / 5) : ℝ) : ℂ) * Complex.I)).re := by
  dsimp only
  have h := quarter_cutoff_phase_exp (t := t) hr
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  rw [h, section99_phase_coeff_split, mul_add, Complex.add_re]
  congr 1
  · rw [mul_comm]
  · congr 1
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    simp only [Complex.ofReal_mul, Complex.ofReal_add]
    ring

/-- The coefficient index separates the unshifted and shifted parts for each
of the 29 positive ordinates. Each coefficient includes the factor of two
for its conjugate partner. -/
@[expose]
noncomputable def quarterLowPhaseCoeff (g : Fin 29 → ℝ) (j : Fin 29 × Fin 2) : ℂ :=
  2 * (if j.2 = 0 then section99RatCoeff (g j.1) else section99PoleCoeff (g j.1))

/-- The two phase shifts are zero and the logarithmic support offset. -/
@[expose]
noncomputable def quarterLowPhaseShift (j : Fin 29 × Fin 2) : ℝ :=
  if j.2 = 0 then 0 else 14 / 5

/-- The low phase contribution at radius r, indexed by the positive zero ordinates.
The factor two accounts for the conjugate zeros when the list is complete. -/
@[expose]
noncomputable def quarterLowPhase (g : Fin 29 → ℝ) (r : ℝ) : ℝ :=
  ∑ i : Fin 29,
    2 *
      (let ρ := (1 / 2 : ℂ) + (g i : ℂ) * Complex.I
    ((((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ)) * section99PhaseKernel ρ).re)

/-- The doubled positive-ordinate phase sum is the finite complex sum used by
the curvature bound. The two summands per ordinate preserve the coefficient
bounds for the rational part and the phase-shifted pole separately. -/
theorem quarter_low_phase_sum {r : ℝ} (hr : 0 < r) (g : Fin 29 → ℝ) :
    quarterLowPhase g r =
      ∑ j : Fin 29 × Fin 2,
        (quarterLowPhaseCoeff g j *
            Complex.exp
              (((g j.1 * (2 * Real.log r + quarterLowPhaseShift j) : ℝ) : ℂ) * Complex.I)).re := by
  rw [quarterLowPhase, ← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  rw [section99_phase_re_split hr, Fin.sum_univ_two]
  simp only [quarterLowPhaseCoeff, quarterLowPhaseShift, ite_true,
    ite_eq_right (by decide : (1 : Fin 2) ≠ 0), add_zero, two_mul, add_mul, Complex.add_re]
  ring

/-- Endpoint certificates for the low phase control it throughout the radius
interval, given boxes for the two complex coefficients at each ordinate and
a certified upper bound for the sum of the curvature contributions. -/
theorem quarter_low_phase_interval (g : Fin 29 → ℝ) (H : Fin 29 → ℝ) (A B : Fin 29 × Fin 2 → ℝ)
    {l r u M L U : ℝ} (hl : 0 < l) (hr : r ∈ Set.Icc l u) (hg : ∀ i, |g i| ≤ H i)
    (hA : ∀ j, |(quarterLowPhaseCoeff g j).re| ≤ A j)
    (hB : ∀ j, |(quarterLowPhaseCoeff g j).im| ≤ B j)
    (hM : ∑ j : Fin 29 × Fin 2, (H j.1) ^ 2 * (A j + B j) ≤ M) (hL : L ≤ quarterLowPhase g l)
    (hU : U ≤ quarterLowPhase g u) :
    min L U - M * (u - l) ^ 2 / (2 * l ^ 2) ≤ quarterLowPhase g r := by
  rw [quarter_low_phase_sum hl] at hL
  rw [quarter_low_phase_sum (hl.trans_le (hr.1.trans hr.2))] at hU
  rw [quarter_low_phase_sum (hl.trans_le hr.1)]
  exact
    complex_phase_interval_lower Finset.univ (quarterLowPhaseCoeff g) (fun j ↦ g j.1)
      quarterLowPhaseShift (fun j ↦ H j.1) A B hl hr (fun j _ ↦ hg j.1) (fun j _ ↦ hA j)
      (fun j _ ↦ hB j) hM hL hU

/-- For a finite set of nontrivial zeta zeros above height 100, RH and the
certified exact zero count give a lower bound for the signed phase tail.
The bound is uniform at every positive cutoff. -/
theorem section99_phase_high_lower (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (ht : ∀ ρ ∈ S, 100 < |ρ.im|) {X : ℝ}
    (hX : 0 < X) :
    -0.0059776 ≤
      ∑ ρ ∈ S,
        ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
            ((X : ℂ) ^ ρ / (Real.sqrt X : ℂ)) *
            section99PhaseKernel ρ).re := by
  have hc := AnalyticNumberTheory.RiemannZeta.count_100_eq_58_of_RH hRH
  apply (neg_le_neg (section104_finite_high_bound hRH hc S hz hre ht)).trans
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro ρ hρ
  have hx := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hz ρ hρ) (hre ρ hρ)
  have hr := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hx
  exact (abs_le.mp (section99_phase_kernel_bound hX hr _)).1

end PseudoPrime.PrimeTestBounds.MillerRabin
