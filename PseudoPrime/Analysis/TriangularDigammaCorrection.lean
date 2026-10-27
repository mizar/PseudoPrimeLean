/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.DigammaVerticalCorrection
public import PseudoPrime.Analysis.TriangularDigammaMoments
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Integrated positive digamma correction for a triangular kernel

The real-axis digamma baseline is retained for later signed Gamma bounds.
The normalized positive vertical correction is at most nine.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For positive r and real t,w, the half-height digamma correction term equals
a constant multiple of the Cauchy moment at scale 2r. Cross-multiply explicitly
nonzero denominators and use ring arithmetic.
This puts each Gamma correction term into the proved integrable moment interface. -/
theorem triangular_digamma_correction_term_eq_moment {r t w : ℝ} (hr : 0 < r) :
    (1 / 2 : ℝ) * ((t / 2) ^ 2 / (r * (r ^ 2 + (t / 2) ^ 2))) * w =
      (1 / (2 * r)) * (t ^ 2 * w / ((2 * r) ^ 2 + t ^ 2)) := by
  have hs : 0 < r ^ 2 + (t / 2) ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) (sq_nonneg _)
  have hl : 0 < (2 * r) ^ 2 + t ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos (mul_pos (by norm_num only) hr)) (sq_nonneg _)
  rw [← mul_div_assoc, div_mul_eq_mul_div, div_mul_div_comm, one_mul]
  apply (div_eq_div_iff (mul_pos hr hs).ne' (mul_pos (mul_pos (by norm_num only) hr) hl).ne').mpr
  ring

/-- For positive real a, the inverse squares shifted by a form a summable sequence.
Use the natural inverse-square majorant away from zero.
This controls the integrated norms of the digamma correction series. -/
theorem summable_shifted_inverse_squares {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ ↦ ((a + n) ^ 2)⁻¹) := by
  have hs : Summable (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := by
    simpa only [Real.rpow_two] using
      (Real.summable_nat_rpow_inv.mpr (by norm_num only : (1 : ℝ) < 2))
  apply Summable.of_norm_bounded_eventually_nat hs
  filter_upwards [Nat.eventually_pos] with n hn
  have hnn : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hp : (n : ℝ) ^ 2 ≤ (a + n) ^ 2 := by nlinarith only [ha, hnn]
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hnn) hp

/-- For nonzero triangular parameter a and positive r, the half-height positive
digamma correction term is integrable and has raw integral at most pi/r^2.
Apply the Cauchy moment estimate after the exact term identity.
This supplies the norm-summability budget for interchanging the series and integral. -/
theorem triangular_digamma_correction_term_integrable_and_bound {a r : ℝ} (ha : a ≠ 0)
    (hr : 0 < r) :
    let F := fun t : ℝ ↦
      (1 / 2 : ℝ) * ((t / 2) ^ 2 / (r * (r ^ 2 + (t / 2) ^ 2))) *
        ‖triangularMellinFunction a (Complex.I * t)‖
    MeasureTheory.Integrable F ∧ (∫ t : ℝ, F t) ≤ Real.pi * (r ^ 2)⁻¹ := by
  let F := fun t : ℝ ↦
    (1 / 2 : ℝ) * ((t / 2) ^ 2 / (r * (r ^ 2 + (t / 2) ^ 2))) *
      ‖triangularMellinFunction a (Complex.I * t)‖
  have hm :=
    triangular_digamma_moment_integrable_and_bound ha (mul_pos (by norm_num only : (0 : ℝ) < 2) hr)
  have he (t : ℝ) :
    F t =
      (1 / (2 * r)) *
        (t ^ 2 * ‖triangularMellinFunction a (Complex.I * t)‖ / ((2 * r) ^ 2 + t ^ 2)) :=
    triangular_digamma_correction_term_eq_moment hr
  have hi : MeasureTheory.Integrable F :=
    (hm.1.const_mul (1 / (2 * r))).congr (Filter.Eventually.of_forall (fun t ↦ (he t).symm))
  have hb :=
    mul_le_mul_of_nonneg_left hm.2
      (div_nonneg (by norm_num only : (0 : ℝ) ≤ 1) (mul_pos (by norm_num only : (0 : ℝ) < 2) hr).le)
  have hn : (1 / (2 * r)) * (4 * Real.pi / (2 * r)) = Real.pi * (r ^ 2)⁻¹ := by
    rw [div_mul_div_comm, one_mul, show (2 * r) * (2 * r) = 4 * r ^ 2 by ring]
    rw [mul_div_mul_left Real.pi (r ^ 2) (by norm_num only : (4 : ℝ) ≠ 0)]
    rfl
  rw [hn] at hb
  have hiEq :=
    MeasureTheory.integral_congr_ae (μ := MeasureTheory.volume) (Filter.Eventually.of_forall he)
  rw [MeasureTheory.integral_const_mul] at hiEq
  exact ⟨hi, hiEq.trans_le hb⟩

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- For nonzero a and positive b, the normalized integrated vertical digamma
correction is at most half the shifted inverse-square sum. Its terms have
summable integrated norms, so interchange the Euler series and integral.
This keeps the real-axis baseline available for a signed Gamma-factor estimate. -/
theorem triangular_digamma_correction_integral_le_series {a b : ℝ} (ha : a ≠ 0) (hb : 0 < b) :
    (∫ t : ℝ,
          (1 / 2 : ℝ) *
            ((Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re - (Complex.digamma (b : ℂ)).re) *
            ‖triangularMellinFunction a (Complex.I * t)‖) /
        (2 * Real.pi) ≤
      (1 / 2 : ℝ) * (∑' n : ℕ, ((b + n) ^ 2)⁻¹) := by
  let F := fun n : ℕ ↦ fun t : ℝ ↦
    (1 / 2 : ℝ) * ((t / 2) ^ 2 / ((b + n) * ((b + n) ^ 2 + (t / 2) ^ 2))) *
      ‖triangularMellinFunction a (Complex.I * t)‖
  have hp (n : ℕ) : 0 < b + n := add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)
  have hF0 (n : ℕ) (t : ℝ) : 0 ≤ F n t := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2)
          (div_nonneg (sq_nonneg _)
            (mul_nonneg (hp n).le (add_nonneg (sq_nonneg _) (sq_nonneg _)))))
        (norm_nonneg _)
  have hf (n : ℕ) : MeasureTheory.Integrable (F n) :=
    (triangular_digamma_correction_term_integrable_and_bound ha (hp n)).1
  have hbound (n : ℕ) : (∫ t : ℝ, F n t) ≤ Real.pi * ((b + n) ^ 2)⁻¹ :=
    (triangular_digamma_correction_term_integrable_and_bound ha (hp n)).2
  have heNorm (n : ℕ) : (∫ t : ℝ, ‖F n t‖) = ∫ t : ℝ, F n t :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun t ↦ Real.norm_of_nonneg (hF0 n t)))
  have hs := (summable_shifted_inverse_squares hb).mul_left Real.pi
  have hsNorm : Summable (fun n : ℕ ↦ ∫ t : ℝ, ‖F n t‖) :=
    hs.of_nonneg_of_le (fun n ↦ MeasureTheory.integral_nonneg (fun t ↦ norm_nonneg _))
      (fun n ↦ by
        rw [heNorm]; exact hbound n)
  have hsInt : Summable (fun n : ℕ ↦ ∫ t : ℝ, F n t) :=
    hs.of_nonneg_of_le (fun n ↦ MeasureTheory.integral_nonneg (hF0 n)) hbound
  have hsum := Summable.tsum_le_tsum hbound hsInt hs
  rw [tsum_mul_left] at hsum
  have he := MeasureTheory.integral_tsum_of_summable_integral_norm hf hsNorm
  have hpoint (t : ℝ) :
    (∑' n : ℕ, F n t) =
      (1 / 2 : ℝ) *
        ((Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re - (Complex.digamma (b : ℂ)).re) *
        ‖triangularMellinFunction a (Complex.I * t)‖ := by
    dsimp only [F]
    rw [tsum_mul_right, tsum_mul_left, ←
      AnalyticNumberTheory.Gamma.digamma_vertical_re_sub_eq_tsum hb]
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)] at he
  rw [he] at hsum
  apply (div_le_iff₀ (mul_pos (by norm_num only) Real.pi_pos)).mpr
  nlinarith only [hsum]

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- For b at least one quarter, the shifted inverse-square sum is at most eighteen.
The zero term is at most sixteen and the remaining terms are bounded by the
certified inverse-square tail. This gives a uniform budget for both character parities. -/
theorem shifted_inverse_square_sum_le_eighteen {b : ℝ} (hb : (1 / 4 : ℝ) ≤ b) :
    (∑' n : ℕ, ((b + n) ^ 2)⁻¹) ≤ 18 := by
  have hp : 0 < b := lt_of_lt_of_le (by norm_num only) hb
  have hs := summable_shifted_inverse_squares hp
  have hbase : Summable (fun n : ℕ ↦ (((n : ℝ) + 1) ^ 2)⁻¹) := by
    simpa only [add_comm] using summable_shifted_inverse_squares (a := 1) (by norm_num only)
  have htail : Summable (fun n : ℕ ↦ ((b + (n + 1)) ^ 2)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      summable_shifted_inverse_squares (a := b + 1) (add_pos hp (by norm_num only))
  have hn (n : ℕ) : ((b + (n + 1)) ^ 2)⁻¹ ≤ (((n : ℝ) + 1) ^ 2)⁻¹ := by
    have h : ((n : ℝ) + 1) ^ 2 ≤ (b + (n + 1)) ^ 2 := by
      nlinarith only [hp, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hpos : 0 < ((n : ℝ) + 1) ^ 2 :=
      sq_pos_of_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num only))
    simpa only [one_div] using one_div_le_one_div_of_le hpos h
  have ht := Summable.tsum_le_tsum hn htail hbase
  have he := AnalyticNumberTheory.Gamma.digammaLogErrorBound_le_eight
  unfold AnalyticNumberTheory.Gamma.digammaLogErrorBound at he
  simp only [div_eq_mul_inv] at he
  rw [tsum_mul_left] at he
  have hzero : (b ^ 2)⁻¹ ≤ 16 := by
    have hsq := mul_self_le_mul_self (by norm_num only : (0 : ℝ) ≤ 1 / 4) hb
    have hz :=
      one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < (1 / 4) ^ 2)
        (by simpa only [pow_two] using hsq)
    norm_num only [one_div] at hz
    simpa only [pow_two] using hz
  rw [hs.tsum_eq_zero_add]
  norm_num only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  linarith only [he, ht, hzero]

/-- For nonzero triangular parameter and Gamma argument b at least one quarter,
the normalized positive vertical digamma correction is at most nine.
Apply the series-integral bound and the uniform inverse-square sum estimate.
This bounds the correction alone; the real-axis Gamma baseline is not discarded. -/
theorem triangular_digamma_correction_integral_le_nine {a b : ℝ} (ha : a ≠ 0)
    (hb : (1 / 4 : ℝ) ≤ b) :
    (∫ t : ℝ,
          (1 / 2 : ℝ) *
            ((Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re - (Complex.digamma (b : ℂ)).re) *
            ‖triangularMellinFunction a (Complex.I * t)‖) /
        (2 * Real.pi) ≤
      9 := by
  have hp : 0 < b := lt_of_lt_of_le (by norm_num only) hb
  have hg := triangular_digamma_correction_integral_le_series ha hp
  have hbnd := shifted_inverse_square_sum_le_eighteen hb
  linarith only [hg, hbnd]

end PseudoPrime.Analysis
