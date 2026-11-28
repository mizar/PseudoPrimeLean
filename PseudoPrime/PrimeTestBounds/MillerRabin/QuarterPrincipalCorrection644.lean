/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalPhase644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalPhase644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalLimit644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel644
import all PseudoPrime.Analysis.LogTaylorBounds
import all PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds

/-! # Cancellation and bounds for the physical cutoff corrections -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The cutoff phase cancels the phase of the lower-end power. Its
product is the real decay factor at the physical endpoint one. -/
private theorem lower_power_cancel {X : ℝ} (hX : 0 < X) (ρ : ℂ) :
    ((X : ℂ) ^ ρ / (Real.sqrt X : ℂ)) * ((1 / X : ℝ) : ℂ) ^ (ρ + 57 / 100) =
      (X ^ (-(107 / 100 : ℝ)) : ℝ) := by
  have hx : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hy : ((1 / X : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (one_div_pos.mpr hX).ne'
  have hpow : (X : ℂ) ^ ρ * ((1 / X : ℝ) : ℂ) ^ (ρ + 57 / 100) = (X ^ (-(57 / 100 : ℝ)) : ℝ) := by
    rw [Complex.cpow_def_of_ne_zero hx, Complex.cpow_def_of_ne_zero hy, Complex.ofReal_cpow hX.le,
      Complex.cpow_def_of_ne_zero hx, ← Complex.ofReal_log hX.le, ←
      Complex.ofReal_log (one_div_pos.mpr hX).le, one_div, Real.log_inv, Complex.ofReal_neg, ←
      Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [div_mul_eq_mul_div, hpow, ← Complex.ofReal_div, Real.sqrt_eq_rpow, ← Real.rpow_sub hX]
  rw [show -(57 / 100 : ℝ) - 1 / 2 = -(107 / 100) by ring]

/-- The physical weight at one has the same decay factor and shifted
logarithm as the lower-end Mellin correction. -/
private theorem weight_one_power {X : ℝ} (hX : 0 < X) :
    quarterWeight644 X 1 =
      ((107 / 100 : ℝ) ^ 5 * Real.exp (-(2687 / 1000 * (107 / 100))) / 120) *
        (X ^ (-(107 / 100 : ℝ)) * (2687 / 1000 + Real.log X) ^ 5) := by
  rw [quarterWeight644, Real.sqrt_one, one_div_one, one_mul, one_div, Real.log_inv, sub_neg_eq_add]
  rw [Real.rpow_def_of_pos hX]
  have he :
    -((107 / 100) * (2687 / 1000 + Real.log X)) =
      -(2687 / 1000 * (107 / 100)) + Real.log X * -(107 / 100) := by
    ring
  rw [he, Real.exp_add]
  ring

/-- Both lower-end corrections in a zero contribution share a real decay
factor. The remaining expression uses the shifted logarithmic polynomial
and the reciprocal from the boundary value. -/
private theorem correction_formula {X : ℝ} (hX : 1 ≤ X) (ρ : ℂ) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let s := ρ + (57 / 100 : ℂ)
    let b := 2687 / 1000 + Real.log X
    let C := ((107 / 100 : ℝ) ^ 5 * Real.exp (-(2687 / 1000 * (107 / 100))) / 120 : ℝ)
    quarterPhaseCorrection644 X ρ =
      3 * C * X ^ (-(107 / 100 : ℝ)) *
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
  have hM : quarterMoment644 s (1 / X) = ((1 / X : ℝ) : ℂ) ^ s * A := by
    unfold quarterMoment644
    rw [show (2687 / 1000 - Real.log (1 / X) : ℝ) = b
        by
        dsimp only [b]
        rw [one_div, Real.log_inv, sub_neg_eq_add]]
  have hP : p * ((1 / X : ℝ) : ℂ) ^ s = (X ^ (-(107 / 100 : ℝ)) : ℝ) := lower_power_cancel hx ρ
  change
    3 * C * (m * p * quarterMoment644 s (1 / X)).re + 3 * (-m / ρ).re * quarterWeight644 X 1 = _
  rw [hM, weight_one_power hx]
  rw [show m * p * (((1 / X : ℝ) : ℂ) ^ s * A) = (p * ((1 / X : ℝ) : ℂ) ^ s) * (m * A) by ring, hP]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  dsimp only [C, b]
  ring

/-- The lower-end coefficient after the first reciprocal cancels with
the boundary term. Every remaining denominator has degree at least two. -/
private noncomputable def lowerKernel (b : ℝ) (ρ : ℂ) : ℂ :=
  let s := ρ + (57 / 100 : ℂ)
  (-((b : ℂ) ^ 5 * (57 / 100) / (ρ * s)) +
    (∑ j ∈ Finset.range 5,
      (((5 : ℕ).choose (j + 1) : ℂ) * (b : ℂ) ^ (5 - (j + 1))) *
        (((j + 1).factorial : ℂ) / s ^ ((j + 1) + 1))))

/-- The lower endpoint contributes the real part of the cancelled
coefficient times the real cutoff decay factor and the zero multiplicity. -/
private theorem correction_cancel {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hn : ρ ≠ 0)
    (hρ : 0 < ρ.re + 57 / 100) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let b := 2687 / 1000 + Real.log X
    let C := ((107 / 100 : ℝ) ^ 5 * Real.exp (-(2687 / 1000 * (107 / 100))) / 120 : ℝ)
    quarterPhaseCorrection644 X ρ = 3 * C * X ^ (-(107 / 100 : ℝ)) * (m * lowerKernel b ρ).re := by
  intro m b C
  let s := ρ + (57 / 100 : ℂ)
  have hs : s ≠ 0 := by
    have hre : 0 < s.re := by
      dsimp only [s]
      norm_num only [Complex.add_re, Complex.div_ofNat_re]
      exact hρ
    intro he
    rw [he, Complex.zero_re] at hre
    exact (lt_irrefl _ hre)
  have hdiff : (1 : ℂ) / s - 1 / ρ = -(57 / 100) / (ρ * s) := by
    field_simp [hn, hs]
    dsimp only [s]
    ring
  let A :=
    ∑ j ∈ Finset.range 6,
      (((5 : ℕ).choose j : ℂ) * (b : ℂ) ^ (5 - j)) * ((j.factorial : ℂ) / s ^ (j + 1))
  have hA : m * A + (-m / ρ) * (b : ℂ) ^ 5 = m * lowerKernel b ρ := by
    unfold A lowerKernel
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, Nat.factorial_zero, Nat.zero_add,
      pow_one, one_mul, mul_one_div]
    change _ = m * (-((b : ℂ) ^ 5 * (57 / 100) / (ρ * s)) + _)
    rw [show -((b : ℂ) ^ 5 * (57 / 100) / (ρ * s)) = (b : ℂ) ^ 5 * (1 / s - 1 / ρ) by
        rw [hdiff]; ring]
    ring
  have h := correction_formula hX ρ
  change
    quarterPhaseCorrection644 X ρ =
      3 * C * X ^ (-(107 / 100 : ℝ)) * ((m * A).re + (-m / ρ).re * b ^ 5) at h
  rw [h]
  have hre : (((-m / ρ) * (b : ℂ) ^ 5)).re = (-m / ρ).re * b ^ 5 := by
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
  rw [← hre, ← Complex.add_re, hA]

/-- The cancelled lower kernel is bounded by 11/10 times the fifth power of the
shift divided by the squared ordinate, for shifts at least fourteen. -/
private theorem lower_kernel_bound {b : ℝ} (hb : 14 ≤ b) {ρ : ℂ} (ht : 1 ≤ |ρ.im|) :
    ‖lowerKernel b ρ‖ ≤ (11 / 10) * b ^ 5 / |ρ.im| ^ 2 := by
  let t := |ρ.im|
  let s := ρ + (57 / 100 : ℂ)
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
  have hA : ‖-((b : ℂ) ^ 5 * (57 / 100) / (ρ * s))‖ ≤ b ^ 5 * (57 / 100) / t ^ 2 := by
    simp only [norm_neg, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hb0,
      Complex.norm_ofNat]
    exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ht0) hprod
  change ‖-((b : ℂ) ^ 5 * (57 / 100) / (ρ * s)) + ∑ j ∈ Finset.range 5, F j‖ ≤ _
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
theorem quarter_correction_bound_644 {X : ℝ} (hX : 1 ≤ X) (hb : 14 ≤ 2687 / 1000 + Real.log X)
    {ρ : ℂ} (ht : 1 ≤ |ρ.im|) (hr : ρ.re = 1 / 2) :
    |quarterPhaseCorrection644 X ρ| ≤
      (33 / 10) * quarterWeight644 X 1 *
        ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) := by
  let m := AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ
  let b := 2687 / 1000 + Real.log X
  let C := (107 / 100 : ℝ) ^ 5 * Real.exp (-(2687 / 1000 * (107 / 100))) / 120
  let d := X ^ (-(107 / 100 : ℝ))
  have hn : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hr
    norm_num only at hr
  have hρ : 0 < ρ.re + 57 / 100 := by
    rw [hr]; norm_num only
  have he := correction_cancel hX hn hρ
  change quarterPhaseCorrection644 X ρ = 3 * C * d * ((m : ℂ) * lowerKernel b ρ).re at he
  rw [he, abs_mul,
    abs_of_nonneg
      (by
        dsimp only [C, d]; positivity)]
  have h := Complex.abs_re_le_norm ((m : ℂ) * lowerKernel b ρ)
  rw [norm_mul, Complex.norm_natCast] at h
  have hh := h.trans (mul_le_mul_of_nonneg_left (lower_kernel_bound hb ht) (Nat.cast_nonneg m))
  refine
    (mul_le_mul_of_nonneg_left hh
          (by
            dsimp only [C, d]; positivity)).trans_eq
      ?_
  rw [weight_one_power (zero_lt_one.trans_le hX)]
  change
    3 * C * d * ((m : ℝ) * ((11 / 10) * b ^ 5 / |ρ.im| ^ 2)) =
      33 / 10 * (C * (d * b ^ 5)) * ((m : ℝ) / |ρ.im| ^ 2)
  ring

private theorem finite_ordinate_mass (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ S, (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
      0.0505 := by
  have h := AnalyticNumberTheory.RiemannZeta.sum_zetaZeroMultiplicity_invNormSq_le hRH S hz hre
  have hm := AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth
  calc
    _ ≤
        ∑ ρ ∈ S,
          (101 / 100 : ℝ) *
            ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) /
              Complex.normSq ρ) :=
      by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hxi :=
        AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hz ρ hρ) (hre ρ hρ)
      have hr := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
      have ht := AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH (hz ρ hρ) (hre ρ hρ)
      have ht6 : 6 ≤ |ρ.im| := by linarith only [ht, Real.pi_gt_three]
      have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 6) ht6 2
      have hn : 0 < Complex.normSq ρ := by
        rw [Complex.normSq_apply, hr]
        nlinarith only [sq_nonneg ρ.im]
      have hd : Complex.normSq ρ ≤ (101 / 100) * |ρ.im| ^ 2 := by
        rw [Complex.normSq_apply, hr, sq_abs]
        rw [sq_abs] at hs
        nlinarith only [hs]
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith only [ht6])) hn).2
      have hh :=
        mul_le_mul_of_nonneg_left hd
          (Nat.cast_nonneg (α := ℝ)
            (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ))
      simpa only [mul_left_comm, mul_assoc] using hh
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      linarith only [h, hm]

private theorem correction_coordinates {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    1 ≤ r ^ 2 ∧ 14 ≤ 2687 / 1000 + Real.log (r ^ 2) ∧ quarterWeight644 (r ^ 2) 1 ≤ 0.0018 := by
  have h1 : 1 ≤ r := (by norm_num only : (1 : ℝ) ≤ 316).trans hr.1
  have hX := one_le_pow₀ h1 (n := 2)
  have hmin : (99856 : ℝ) ≤ r ^ 2 :=
    (show (99856 : ℝ) = 316 ^ 2 by norm_num only) ▸ pow_le_pow_left₀ (by norm_num only) hr.1 2
  have hmax : r ^ 2 ≤ (103684 : ℝ) :=
    (pow_le_pow_left₀ (zero_le_one.trans h1) hr.2 2).trans_eq (by norm_num only)
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 99856) (j := 16) (n := 20) (lo := 57 / 5) (hi :=
        12) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 103684) (j := 16) (n := 20) (lo := 11) (hi :=
        289 / 25) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl hu
  have hb : 14 ≤ 2687 / 1000 + Real.log (r ^ 2) := by
    linarith only [hl, Real.log_le_log (by norm_num only) hmin]
  have hb' : 2687 / 1000 + Real.log (r ^ 2) ≤ 57 / 4 := by
    linarith only [hu, Real.log_le_log (zero_lt_one.trans_le hX) hmax]
  have hd :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99856) (p := 107) (d :=
        100) (lo := 0) (hi := 448 / 100000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, neg_div] at hd
  have hpow :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 99856) hmin
          (by norm_num only : -(107 / 100 : ℝ) ≤ 0)).trans
      hd
  have he := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 287509 / 100000) 9
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at he
  have hc : Real.exp (-(2687 / 1000 * (107 / 100))) ≤ 0.057 := by
    rw [show -(2687 / 1000 * (107 / 100) : ℝ) = -(287509 / 100000) by norm_num only, Real.exp_neg,
      inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
    linarith only [he]
  refine ⟨hX, hb, ?_⟩
  rw [weight_one_power (zero_lt_one.trans_le hX)]
  have hlog :=
    pow_le_pow_left₀ (show 0 ≤ 2687 / 1000 + Real.log (r ^ 2) by linarith only [hb]) hb' 5
  have hp := mul_le_mul hpow hlog (by positivity) (by norm_num only)
  have hC :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ (107 / 100) ^ 5 by norm_num only))
      (show (0 : ℝ) ≤ 120 by norm_num only)
  exact (mul_le_mul hC hp (by positivity) (by norm_num only)).trans (by norm_num only)

/-- For radii from 316 to 322, the total physical cutoff correction of
any finite nontrivial-zero family is at least minus 0.0005 under RH.
Inverse-square mass bounds make the estimate uniform in truncation height. -/
theorem quarter_correction_sum_644 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 316 322)
    (S : Finset ℂ) (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    -0.0005 ≤ ∑ ρ ∈ S, quarterPhaseCorrection644 (r ^ 2) ρ := by
  obtain ⟨hX, hb, hw⟩ := correction_coordinates hr
  let M := fun ρ : ℂ ↦
    (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2
  have hterm (ρ : ℂ) (hρ : ρ ∈ S) :
    -(33 / 10 * 0.003 * M ρ) ≤ quarterPhaseCorrection644 (r ^ 2) ρ := by
    have hx := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hz ρ hρ) (hre ρ hρ)
    have hrho := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hx
    have ht := AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH (hz ρ hρ) (hre ρ hρ)
    have h :=
      (abs_le.mp
          (quarter_correction_bound_644 hX hb (by linarith only [ht, Real.pi_gt_three]) hrho)).1
    have hM : 0 ≤ M ρ := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hu :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hw.trans (by norm_num only : (0.0018 : ℝ) ≤ 0.003))
          (by norm_num only : (0 : ℝ) ≤ 33 / 10))
        hM
    exact (neg_le_neg hu).trans h
  have hs := Finset.sum_le_sum hterm
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at hs
  have hm : ∑ ρ ∈ S, M ρ ≤ 0.0505 := finite_ordinate_mass hRH S hz hre
  linarith only [hs, hm]

/-- RH gives the four physical zero-contribution lower bounds for section 122.
The uniform loss 0.0005 accounts for the physical endpoint corrections. -/
theorem quarter_zero_abel_rows_644 (hRH : RiemannHypothesis) :
    let F := fun r : ℝ ↦
      quarterAbelAction644 (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re)
    (∀ r ∈ Set.Icc 316 320, -0.007131 ≤ F r) ∧
      (∀ r ∈ Set.Icc 320 (1287 / 4), -0.003750 ≤ F r) ∧
      (∀ r ∈ Set.Icc (1287 / 4) (1609 / 5), -0.002563 ≤ F r) ∧
      (∀ r ∈ Set.Icc (1609 / 5) 322, -0.002549 ≤ F r) := by
  have h :=
    quarter_abel_phase_rows_644 hRH (D := 0.0005)
      (fun r hr S hz hre ↦ quarter_correction_sum_644 hRH hr S hz hre)
  norm_num only at h ⊢
  exact h

/-- The terms of the principal explicit formula outside the nontrivial-zero
action at cutoff `X`. The trivial-zero action is included with its minus sign. -/
noncomputable def quarterPrincipalBase644 (X : ℝ) : ℝ :=
  let W := quarterWeight644 X
  4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..X * Real.exp (2687 / 1000), W t) +
      4 * W X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) +
      3 * W 1 -
    quarterAbelAction644 X AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries -
    3 * Real.log (2 * Real.pi) * W 1

/-- The principal expression needed for the section 122 witness comparison.
It is four physical prefixes minus the full principal sum at cutoff `X`. -/
noncomputable def quarterPrincipalGap644 (X : ℝ) : ℝ :=
  let S := fun n : ℕ ↦ (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) X n).re
  4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - ∑' n : ℕ, S n

private theorem principal_gap_of_zero {X z : ℝ} (hX : 1 ≤ X)
    (hz :
      z ≤
        quarterAbelAction644 X
          (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re)) :
    quarterPrincipalBase644 X + z ≤ quarterPrincipalGap644 X := by
  have h := quarter_principal_explicit_644 hX
  dsimp only [quarterPrincipalBase644, quarterPrincipalGap644]
  dsimp only at h
  linarith only [hz, h]

/-- The four certified nontrivial-zero bounds give lower bounds for the
principal gap under RH. The integrated weights, psi endpoint and trivial
zero term remain explicit in the base term. -/
theorem quarter_principal_rows_644 (hRH : RiemannHypothesis) :
    let F := fun r : ℝ ↦ quarterPrincipalBase644 (r ^ 2)
    let G := fun r : ℝ ↦ quarterPrincipalGap644 (r ^ 2)
    (∀ r ∈ Set.Icc 316 320, F r - 0.007131 ≤ G r) ∧
      (∀ r ∈ Set.Icc 320 (1287 / 4), F r - 0.003750 ≤ G r) ∧
      (∀ r ∈ Set.Icc (1287 / 4) (1609 / 5), F r - 0.002563 ≤ G r) ∧
      (∀ r ∈ Set.Icc (1609 / 5) 322, F r - 0.002549 ≤ G r) := by
  intro F G
  have h := quarter_zero_abel_rows_644 hRH
  have step {r z : ℝ} (hr : 1 ≤ r)
    (hz :
      -z ≤
        quarterAbelAction644 (r ^ 2)
          (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re)) :
    F r - z ≤ G r := by exact sub_eq_add_neg (F r) z ▸ principal_gap_of_zero (one_le_pow₀ hr) hz
  exact
    ⟨fun r hr ↦ step ((by norm_num only : (1 : ℝ) ≤ 316).trans hr.1) (h.1 r hr), fun r hr ↦
      step ((by norm_num only : (1 : ℝ) ≤ 320).trans hr.1) (h.2.1 r hr), fun r hr ↦
      step ((by norm_num only : (1 : ℝ) ≤ 1287 / 4).trans hr.1) (h.2.2.1 r hr), fun r hr ↦
      step ((by norm_num only : (1 : ℝ) ≤ 1609 / 5).trans hr.1) (h.2.2.2 r hr)⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
