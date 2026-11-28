/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCutoffZeroCredit
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FiniteZeroSums
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Real phase formula for the signed cutoff credit -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem cutoff_cpow {y : ℝ} (hy : 0 < y) {ρ : ℂ} (hr : ρ.re = 1 / 2) :
    ((y ^ 2 : ℝ) : ℂ) ^ ρ =
      (y : ℂ) * Complex.exp (Complex.I * ((2 * Real.log y * ρ.im : ℝ) : ℂ)) := by
  have hy₂ := sq_pos_of_pos hy
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy₂.ne'), ← Complex.ofReal_log hy₂.le,
    Real.log_pow]
  have harg :
    ((↑(2 * Real.log y) : ℂ) * ρ) =
      (Real.log y : ℂ) + Complex.I * ((2 * Real.log y * ρ.im : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, zero_add, add_zero,
        sub_zero, one_mul, hr]
    ring
  simp only [Nat.cast_ofNat]
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hy]

/-- A positive cutoff radius and a critical-line zero give a real expression
for the improvement over the unsigned estimate. Both the phase and the norm
are scaled by the zero's multiplicity. -/
theorem gaussian_zero_credit_phase (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 < y) {ρ : ℂ}
    (hz : riemannZeta ρ = 0) (hr : ρ.re = 1 / 2) :
    let g := ρ.im
    let θ := 2 * Real.log y * g
    let d := (1 / 4 : ℝ) + g ^ 2
    let z := AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm (y ^ 2) ρ
    z.re + ‖z‖ =
      y * (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
        (((g ^ 2 - 1 / 4) * Real.cos θ - g * Real.sin θ + d) / d ^ 2) := by
  intro g θ d z
  have hre : 0 ≤ ρ.re := by
    rw [hr]; norm_num only
  have hnorm : Complex.normSq ρ = d := by
    simp only [Complex.normSq_apply, hr, d, g]
    ring
  have hd : 0 < d := by
    dsimp only [d]; positivity
  have hz' : z = AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution (y ^ 2) ρ := by
    simp only [z, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, hz, hre, and_self,
      ↓reduceIte]
  have hn : ‖z‖ = y * (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / d := by
    rw [hz',
      AnalyticNumberTheory.RiemannZeta.norm_riemannZetaLogZeroContribution_of_rh hRH
        (sq_pos_of_pos hy) hz hre,
      Real.sqrt_sq hy.le, hnorm]
  rw [hn, hz', AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution, cutoff_cpow hy hr]
  simp only [Complex.div_re, pow_two, Complex.normSq_mul, hnorm, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
    Complex.natCast_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, zero_add, add_zero,
    sub_zero, neg_zero, one_mul, hr, Complex.exp_re, Complex.exp_im, Real.exp_zero]
  dsimp only [θ, g]
  field_simp [hd.ne']
  ring

/-- A cosine lower bound on the ordinate bracket gives a lower bound on
one signed credit. The same estimate applies to either conjugate sign. -/
theorem gaussian_phase_credit_lower (hRH : RiemannHypothesis) {y a b c : ℝ} (hy : 0 < y)
    (ha : 1 / 2 ≤ a) (hc : 0 ≤ c) {ρ : ℂ} (hz : riemannZeta ρ = 0) (hr : ρ.re = 1 / 2)
    (hg : |ρ.im| ∈ Set.Icc a b) (hcos : c ≤ Real.cos (2 * Real.log y * ρ.im)) :
    let z := AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm (y ^ 2) ρ
    y * (((a ^ 2 - 1 / 4) * c - b + (1 / 4 + a ^ 2)) / (1 / 4 + b ^ 2) ^ 2) ≤ z.re + ‖z‖ := by
  intro z
  have h0 : 0 ≤ a := by linarith only [ha]
  have hb := h0.trans (hg.1.trans hg.2)
  have hlow := pow_le_pow_left₀ h0 hg.1 2
  have hhi := pow_le_pow_left₀ (abs_nonneg _) hg.2 2
  rw [sq_abs] at hlow hhi
  have hq : 0 ≤ a ^ 2 - 1 / 4 := by
    have h := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 1 / 2) ha 2
    linarith only [h]
  have hs : ρ.im * Real.sin (2 * Real.log y * ρ.im) ≤ b := by
    rw [← mul_one b]
    apply (le_abs_self _).trans
    rw [abs_mul]
    exact mul_le_mul hg.2 (Real.abs_sin_le_one _) (abs_nonneg _) hb
  let A := (a ^ 2 - 1 / 4) * c - b + (1 / 4 + a ^ 2)
  let D := (1 / 4 : ℝ) + ρ.im ^ 2
  let N :=
    (ρ.im ^ 2 - 1 / 4) * Real.cos (2 * Real.log y * ρ.im) -
        ρ.im * Real.sin (2 * Real.log y * ρ.im) +
      D
  have hN : A ≤ N := by
    have h :=
      mul_le_mul (sub_le_sub_right hlow (1 / 4)) hcos hc (hq.trans (sub_le_sub_right hlow (1 / 4)))
    dsimp only [A, N, D]
    linarith only [h, hs, hlow]
  have hD : 0 < D := by
    dsimp only [D]; positivity
  have hρ : ρ ≠ 1 := by
    intro he
    rw [he, Complex.one_re] at hr
    norm_num only at hr
  have hm : (1 : ℝ) ≤ AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ := by
    exact_mod_cast AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity_pos hρ hz
  by_cases hA : 0 ≤ A
  · have hDb : D ≤ (1 / 4 : ℝ) + b ^ 2 := by
      dsimp only [D]; linarith only [hhi]
    have hquot :=
      (div_le_div_of_nonneg_left hA (sq_pos_of_pos hD) (pow_le_pow_left₀ hD.le hDb 2)).trans
        (div_le_div_of_nonneg_right hN (sq_nonneg D))
    have hh :=
      mul_le_mul (mul_le_mul_of_nonneg_left hm hy.le) hquot (div_nonneg hA (sq_nonneg _))
        (mul_nonneg hy.le (zero_le_one.trans hm))
    rw [mul_one] at hh
    exact hh.trans_eq (gaussian_zero_credit_phase hRH hy hz hr).symm
  · have hzpos : 0 ≤ z.re + ‖z‖ := by linarith only [(abs_le.mp (Complex.abs_re_le_norm z)).1]
    exact
      (mul_nonpos_of_nonneg_of_nonpos hy.le
            (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hA) (sq_nonneg _))).trans
        hzpos

private theorem cutoff_log_bracket {y : ℝ} (hy : y ∈ Set.Icc (663 / 2 : ℝ) (1329 / 4)) :
    5.80362 ≤ Real.log y ∧ Real.log y ≤ 5.80589 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 27) (lo := 5.80362)
        (hi := 6) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1329 / 4) (j := 9) (n := 27) (lo := 5) (hi :=
        5.80589) (by decide +kernel)).2
  norm_num only [Rat.cast_ofScientific, Rat.cast_div, Rat.cast_ofNat] at hl hu
  have hp : 0 < y := by linarith only [hy.1]
  exact
    ⟨by linarith only [hl, Real.log_le_log (by norm_num only) hy.1], by
      linarith only [hu, Real.log_le_log hp hy.2]⟩

/-- Rational upper and lower brackets for a reduced phase bound the cosine
throughout the cutoff interval. The reflected ordinate gives the same cosine. -/
theorem gaussian_cutoff_cos_of_bracket {y a b R c : ℝ} (k : ℕ)
    (hy : y ∈ Set.Icc (663 / 2 : ℝ) (1329 / 4)) {g : ℝ} (hg : |g| ∈ Set.Icc a b) (ha : 0 ≤ a)
    (hl : -R ≤ 2 * 5.80362 * a - (k : ℝ) * (2 * 3.14159266))
    (hu : 2 * 5.80589 * b - (k : ℝ) * (2 * 3.14159265) ≤ R)
    (hc : c ≤ 1 - R ^ 2 / 2 ∨ (c ≤ 0 ∧ R ≤ Real.pi / 2)) : c ≤ Real.cos (2 * Real.log y * g) := by
  have hp := cutoff_log_bracket hy
  have hlog : 0 ≤ Real.log y := by linarith only [hp.1]
  have hθlo := mul_le_mul hp.1 hg.1 ha hlog
  have hθhi := mul_le_mul hp.2 hg.2 (abs_nonneg g) (by norm_num only : (0 : ℝ) ≤ 5.80589)
  have hπlo : (3.14159265 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d20]
  have hπhi : Real.pi ≤ (3.14159266 : ℝ) := by linarith only [Real.pi_lt_d20]
  let θ := 2 * Real.log y * |g| - (k : ℝ) * (2 * Real.pi)
  have hθ : |θ| ≤ R := by
    apply abs_le.mpr
    dsimp only [θ]
    exact
      ⟨by linarith only [hl, hθlo, mul_le_mul_of_nonneg_left hπhi (Nat.cast_nonneg k)], by
        linarith only [hu, hθhi, mul_le_mul_of_nonneg_left hπlo (Nat.cast_nonneg k)]⟩
  have he : Real.cos θ = Real.cos (2 * Real.log y * g) := by
    dsimp only [θ]
    rw [Real.cos_sub_nat_mul_two_pi]
    by_cases h : 0 ≤ g
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), mul_neg, Real.cos_neg]
  rw [← he]
  rcases hc with hc | ⟨hc, hR⟩
  · have hs := pow_le_pow_left₀ (abs_nonneg θ) hθ 2
    rw [sq_abs] at hs
    linarith only [hc, hs, Real.one_sub_sq_div_two_le_cos (x := θ)]
  · exact hc.trans (Real.cos_nonneg_of_mem_Icc (abs_le.mp (hθ.trans hR)))

/-- A zero in ordinate bracket 1 contributes at least 2.55 for either sign. -/
theorem gaussian_credit_ordinate_1 (hRH : RiemannHypothesis) {y : ℝ}
    (hy : y ∈ Set.Icc (663 / 2 : ℝ) (1329 / 4)) {ρ : ℂ} (hz : riemannZeta ρ = 0) (hr : ρ.re = 1 / 2)
    (hg : |ρ.im| ∈ Set.Icc (14473 / 1024) (14473 / 1024 + 1 / 100)) :
    let z := AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm (y ^ 2) ρ
    2.55 ≤ z.re + ‖z‖ := by
  intro z
  have hp : 0 < y := by linarith only [hy.1]
  have hcos :=
    gaussian_cutoff_cos_of_bracket (R := 0.87176) (c := 0.62) 26 hy hg (by norm_num only)
      (by norm_num only) (by norm_num only) (Or.inl (by norm_num only))
  have h := gaussian_phase_credit_lower hRH hp (by norm_num only) (by norm_num only) hz hr hg hcos
  dsimp only at h
  linarith only [h, hy.1]

/-- A zero in ordinate bracket 2 contributes at least 1.025 for either sign. -/
theorem gaussian_credit_ordinate_2 (hRH : RiemannHypothesis) {y : ℝ}
    (hy : y ∈ Set.Icc (663 / 2 : ℝ) (1329 / 4)) {ρ : ℂ} (hz : riemannZeta ρ = 0) (hr : ρ.re = 1 / 2)
    (hg : |ρ.im| ∈ Set.Icc (10763 / 512) (10763 / 512 + 1 / 100)) :
    let z := AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm (y ^ 2) ρ
    1.025 ≤ z.re + ‖z‖ := by
  intro z
  have hp : 0 < y := by linarith only [hy.1]
  have hcos :=
    gaussian_cutoff_cos_of_bracket (R := 1.044) (c := 0.45) 39 hy hg (by norm_num only)
      (by norm_num only) (by norm_num only) (Or.inl (by norm_num only))
  have h := gaussian_phase_credit_lower hRH hp (by norm_num only) (by norm_num only) hz hr hg hcos
  dsimp only at h
  linarith only [h, hy.1]

/-- A zero in ordinate bracket 3 contributes at least 0.5 for either sign. -/
theorem gaussian_credit_ordinate_3 (hRH : RiemannHypothesis) {y : ℝ}
    (hy : y ∈ Set.Icc (663 / 2 : ℝ) (1329 / 4)) {ρ : ℂ} (hz : riemannZeta ρ = 0) (hr : ρ.re = 1 / 2)
    (hg : |ρ.im| ∈ Set.Icc (25611 / 1024) (25611 / 1024 + 1 / 100)) :
    let z := AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm (y ^ 2) ρ
    0.5 ≤ z.re + ‖z‖ := by
  intro z
  have hp : 0 < y := by linarith only [hy.1]
  have hcos :=
    gaussian_cutoff_cos_of_bracket (R := 1.509) (c := 0) 46 hy hg (by norm_num only)
      (by norm_num only) (by norm_num only) (Or.inr ⟨le_rfl, by linarith only [Real.pi_gt_d20]⟩)
  have h := gaussian_phase_credit_lower hRH hp (by norm_num only) (by norm_num only) hz hr hg hcos
  dsimp only at h
  linarith only [h, hy.1]

/-- A zero in ordinate bracket 5 contributes at least 0.425 for either sign. -/
theorem gaussian_credit_ordinate_5 (hRH : RiemannHypothesis) {y : ℝ}
    (hy : y ∈ Set.Icc (663 / 2 : ℝ) (1329 / 4)) {ρ : ℂ} (hz : riemannZeta ρ = 0) (hr : ρ.re = 1 / 2)
    (hg : |ρ.im| ∈ Set.Icc (33725 / 1024) (33725 / 1024 + 1 / 100)) :
    let z := AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm (y ^ 2) ρ
    0.425 ≤ z.re + ‖z‖ := by
  intro z
  have hp : 0 < y := by linarith only [hy.1]
  have hcos :=
    gaussian_cutoff_cos_of_bracket (R := 0.996) (c := 0.49) 61 hy hg (by norm_num only)
      (by norm_num only) (by norm_num only) (Or.inl (by norm_num only))
  have h := gaussian_phase_credit_lower hRH hp (by norm_num only) (by norm_num only) hz hr hg hcos
  dsimp only at h
  linarith only [h, hy.1]

end PseudoPrime.PrimeTestBounds.MillerRabin
