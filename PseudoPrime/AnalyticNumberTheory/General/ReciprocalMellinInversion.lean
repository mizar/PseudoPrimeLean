/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ReciprocalResolventMellin

/-!
# Reciprocal Mellin inversion for coefficient L-series

Absolute convergence on a positive vertical line permits termwise inversion for the kernel
`x^z / (z (z + 1))`. The multiplier `z / (z + 1)` transfers integrability from the logarithmic
kernel. Real coefficient shifts and finite support of the Mellin weight give smoothed
reciprocal sums, independently of any character or Euler product.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The nth reciprocal Mellin integrand for coefficients `a`, cutoff `x` and vertical coordinate
`τ`: multiply `a n * n^(-z)` by `x^z / (z (z + 1))`, where `z = τ + iy`. Positive `x,τ`
and `a 0 = 0` will permit inversion and integration of the coefficient series. -/
noncomputable def reciprocalMellinTerm (a : ℕ → ℂ) (x τ : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  a n * (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
    (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1))

/-- The vertical argument `τ + iy` has real part `τ`. Expand the real and imaginary parts.
This supplies the nonvanishing and multiplier estimates on a positive vertical line. -/
private theorem reciprocalVertical_re (τ y : ℝ) : ((τ : ℂ) + y * Complex.I).re = τ := by
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- For `τ > 0`, the vertical argument is nonzero. Its real part is strictly positive,
so complex division by this argument is valid in the kernel identity. -/
private theorem reciprocalVertical_ne_zero {τ : ℝ} (hτ : 0 < τ) (y : ℝ) :
    (τ : ℂ) + y * Complex.I ≠ 0 := by
  apply Complex.ne_zero_of_re_pos
  rwa [reciprocalVertical_re]

/-- For `τ > 0`, the shifted vertical argument `τ + iy + 1` is nonzero.
Its positive real part ensures continuity of the reciprocal multiplier. -/
private theorem reciprocalVertical_add_one_ne_zero {τ : ℝ} (hτ : 0 < τ) (y : ℝ) :
    (τ : ℂ) + y * Complex.I + 1 ≠ 0 := by
  apply Complex.ne_zero_of_re_pos
  rw [Complex.add_re, reciprocalVertical_re, Complex.one_re]
  exact add_pos hτ zero_lt_one

/-- For `τ > 0`, the multiplier `z / (z + 1)` has norm at most one on `z = τ + iy`.
The real-part condition gives `norm z ≤ norm (z + 1)`, and the denominator is nonzero.
This transfers the logarithmic kernel's integrable majorant to the reciprocal kernel. -/
theorem verticalReciprocalMultiplier_norm_le {τ : ℝ} (hτ : 0 < τ) (y : ℝ) :
    ‖((τ : ℂ) + y * Complex.I) / ((τ : ℂ) + y * Complex.I + 1)‖ ≤ 1 := by
  rw [norm_div]
  apply (div_le_one (norm_pos_iff.mpr (reciprocalVertical_add_one_ne_zero hτ y))).mpr
  apply norm_le_norm_add_one_of_re_nonneg
  rw [reciprocalVertical_re]
  exact hτ.le

/-- For a positive vertical coordinate, the reciprocal coefficient term equals its logarithmic
term multiplied by `z / (z + 1)`. Cancel the nonzero vertical denominators algebraically.
This identifies the integrable factor used in reciprocal series inversion. -/
theorem reciprocalMellinTerm_eq_logarithmicMellinTerm_mul (a : ℕ → ℂ) (x : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (n : ℕ) (y : ℝ) :
    reciprocalMellinTerm a x τ n y =
      logarithmicMellinTerm a x τ n y *
        (((τ : ℂ) + y * Complex.I) / ((τ : ℂ) + y * Complex.I + 1)) := by
  have hz := reciprocalVertical_ne_zero hτ y
  have hw := reciprocalVertical_add_one_ne_zero hτ y
  unfold reciprocalMellinTerm logarithmicMellinTerm
  field_simp (disch := simp only [hz, hw, ne_eq, not_false_eq_true])

/-- For `τ > 0`, any coefficient term in the reciprocal kernel is bounded in norm by its
logarithmic counterpart. Multiply the logarithmic term by the multiplier of norm at most one.
This provides the termwise integral-norm majorant. -/
theorem norm_reciprocalMellinTerm_le (a : ℕ → ℂ) (x : ℝ) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) (y : ℝ) :
    ‖reciprocalMellinTerm a x τ n y‖ ≤ ‖logarithmicMellinTerm a x τ n y‖ := by
  rw [reciprocalMellinTerm_eq_logarithmicMellinTerm_mul a x hτ, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (verticalReciprocalMultiplier_norm_le hτ y)

/-- For `a 0 = 0` and `x,τ > 0`, every reciprocal coefficient integrand is integrable.
The logarithmic term is integrable and the reciprocal multiplier is continuous and bounded.
This justifies termwise integration before summing the coefficients. -/
theorem integrable_reciprocalMellinTerm (a : ℕ → ℂ) (ha : a 0 = 0) {x τ : ℝ} (hx : 0 < x)
    (hτ : 0 < τ) (n : ℕ) : MeasureTheory.Integrable (reciprocalMellinTerm a x τ n) := by
  have hc : Continuous (fun y : ℝ ↦ ((τ : ℂ) + y * Complex.I) / ((τ : ℂ) + y * Complex.I + 1)) :=
    (continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I)).div
      ((continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I)).add continuous_const)
      (reciprocalVertical_add_one_ne_zero hτ)
  have hi :=
    (integrable_logarithmicMellinTerm a ha hx hτ n).mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (verticalReciprocalMultiplier_norm_le hτ))
  exact
    hi.congr
      (Filter.Eventually.of_forall
        (fun y ↦ (reciprocalMellinTerm_eq_logarithmicMellinTerm_mul a x hτ n y).symm))

/-- If `a 0 = 0`, `x,τ > 0`, and the coefficient L-series converges absolutely at `τ`, the
reciprocal terms have summable integral norms. Compare each integral with its logarithmic
majorant and use absolute coefficient convergence. This permits exchanging series and integral. -/
theorem summable_integral_norm_reciprocalMellinTerm (a : ℕ → ℂ) (ha : a 0 = 0) {x τ : ℝ}
    (hx : 0 < x) (hτ : 0 < τ) (hsum : LSeriesSummable a (τ : ℂ)) :
    Summable (fun n : ℕ ↦ ∫ y : ℝ, ‖reciprocalMellinTerm a x τ n y‖) := by
  apply
    Summable.of_nonneg_of_le (fun n ↦ MeasureTheory.integral_nonneg (fun y ↦ norm_nonneg _)) _
      (summable_integral_norm_logarithmicMellinTerm a ha hx hsum)
  intro n
  exact
    MeasureTheory.integral_mono (integrable_reciprocalMellinTerm a ha hx hτ n).norm
      (integrable_logarithmicMellinTerm a ha hx hτ n).norm (norm_reciprocalMellinTerm_le a x hτ n)

/-- For coefficients vanishing at zero, the total reciprocal integrand is the L-series times
`x^z / (z (z + 1))`. Extract the constant power and denominator from the total sum and rewrite
negative complex powers. This algebraic identity does not require convergence. -/
theorem tsum_reciprocalMellinTerm (a : ℕ → ℂ) (ha : a 0 = 0) (x τ y : ℝ) :
    (∑' n : ℕ, reciprocalMellinTerm a x τ n y) =
      LSeries a ((τ : ℂ) + y * Complex.I) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
        (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1)) := by
  unfold reciprocalMellinTerm
  rw [tsum_div_const, tsum_mul_right, LSeries_def₀ ha]
  congr 2
  apply tsum_congr
  intro n
  rw [Complex.cpow_neg, div_eq_mul_inv]

/-- For positive `x,τ` and nonzero `n`, the coefficient weighted by `w₁(n/x)` equals its
normalized reciprocal Mellin integral. Invert the Mellin weight and split the positive ratio's
complex power, then pull out the coefficient. This evaluates each term of the series. -/
theorem reciprocalMellinTerm_integral (a : ℕ → ℂ) {x τ : ℝ} (hx : 0 < x) (hτ : 0 < τ) {n : ℕ}
    (hn : n ≠ 0) :
    a n * mellinWeightOne ((n : ℝ) / x) =
      (2 * Real.pi : ℝ)⁻¹ • ∫ y : ℝ, reciprocalMellinTerm a x τ n y := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hm := mellinInv_mellinWeightOne_eq (σ := τ) hτ (div_pos hnpos hx)
  have hw :
    mellinWeightOne ((n : ℝ) / x) =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ,
          (((n : ℝ) / x : ℝ) : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) *
            (1 / (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1))) := by
    rw [← hm]
    simp only [mellinInv, smul_eq_mul, one_div]
  rw [hw, mul_smul_comm]
  congr 1
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  rw [cpow_div_eq_cpow_mul_cpow_neg hnpos.le hx, neg_neg, Complex.ofReal_natCast]
  unfold reciprocalMellinTerm
  ring

/-- For `a 0 = 0`, `x,τ > 0` and absolute convergence at `τ`, the `w₁`-weighted coefficient
series equals the normalized vertical L-series integral with denominator `z (z + 1)`.
Termwise inversion and summable integral norms justify interchange. This is reciprocal Perron
inversion for arbitrary coefficient sequences. -/
theorem mellinWeightOne_tsum_eq_integral_LSeries (a : ℕ → ℂ) (ha : a 0 = 0) {x τ : ℝ} (hx : 0 < x)
    (hτ : 0 < τ) (hsum : LSeriesSummable a (τ : ℂ)) :
    (∑' n : ℕ, a n * mellinWeightOne ((n : ℝ) / x)) =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ,
          LSeries a ((τ : ℂ) + y * Complex.I) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1)) := by
  have hterm :
    ∀ n : ℕ,
      a n * mellinWeightOne ((n : ℝ) / x) =
        (2 * Real.pi : ℝ)⁻¹ • ∫ y : ℝ, reciprocalMellinTerm a x τ n y := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [ha, zero_mul, reciprocalMellinTerm, zero_div, MeasureTheory.integral_zero,
        smul_zero]
    · exact reciprocalMellinTerm_integral a hx hτ hn
  rw [tsum_congr hterm, tsum_const_smul'' (2 * Real.pi : ℝ)⁻¹,
    (MeasureTheory.hasSum_integral_of_summable_integral_norm
        (integrable_reciprocalMellinTerm a ha hx hτ)
        (summable_integral_norm_reciprocalMellinTerm a ha hx hτ hsum)).tsum_eq]
  congr 1
  exact
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (tsum_reciprocalMellinTerm a ha x τ))

/-- Under absolute convergence at `σ + τ`, with `a 0 = 0` and `x,τ > 0`, weighting coefficients
by `n^(-σ) w₁(n/x)` shifts the L-series argument in the reciprocal Mellin integral to
`σ + τ + iy`. Apply unshifted inversion to the real-shifted coefficients and translate their
series. This supports the ordinary logarithmic derivative on its right half-plane. -/
theorem mellinWeightOne_shifted_tsum_eq_integral_LSeries (a : ℕ → ℂ) (ha : a 0 = 0) (σ : ℝ)
    {x τ : ℝ} (hx : 0 < x) (hτ : 0 < τ) (hsum : LSeriesSummable a ((σ + τ : ℝ) : ℂ)) :
    (∑' n : ℕ, a n * (n : ℂ) ^ (-(σ : ℂ)) * mellinWeightOne ((n : ℝ) / x)) =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ,
          LSeries a (((σ + τ : ℝ) : ℂ) + y * Complex.I) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1)) := by
  have ha0 : shiftedLSeriesCoefficient a σ 0 = 0 := by
    rw [shiftedLSeriesCoefficient, ha, zero_mul]
  have hs : LSeriesSummable (shiftedLSeriesCoefficient a σ) (τ : ℂ) :=
    (LSeriesSummable_shiftedLSeriesCoefficient a σ (τ : ℂ)).mpr
      (by
        simpa only [Complex.ofReal_add] using hsum
        )
  rw [show
      (fun n ↦ a n * (n : ℂ) ^ (-(σ : ℂ)) * mellinWeightOne ((n : ℝ) / x)) =
        (fun n ↦ shiftedLSeriesCoefficient a σ n * mellinWeightOne ((n : ℝ) / x))
      from rfl,
    mellinWeightOne_tsum_eq_integral_LSeries _ ha0 hx hτ hs]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  simp only [LSeries_shiftedLSeriesCoefficient, Complex.ofReal_add, add_assoc]

/-- The finite smoothed coefficient sum over `0 < n ≤ floor x`, with weight `1 - n/x`.
The coefficients may already include a reciprocal power of `n`. This is the arithmetic side
of reciprocal Mellin inversion. -/
noncomputable def reciprocalWeightedSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n * ((1 - (n : ℝ) / x : ℝ) : ℂ)

/-- For `x > 0` and coefficients vanishing at zero, the `w₁`-weighted total sum is the finite
smoothed sum. Outside the cutoff the Mellin weight vanishes; within it the weight is `1 - n/x`.
Collapse the finitely supported series. No analytic convergence assumption is needed. -/
theorem mellinWeightOne_tsum_eq_reciprocalWeightedSum (a : ℕ → ℂ) (ha : a 0 = 0) {x : ℝ}
    (hx : 0 < x) : (∑' n : ℕ, a n * mellinWeightOne ((n : ℝ) / x)) = reciprocalWeightedSum a x := by
  have hvanish : ∀ n ∉ Finset.Ioc 0 ⌊x⌋₊, a n * mellinWeightOne ((n : ℝ) / x) = 0 := by
    intro n hn
    simp only [Finset.mem_Ioc, not_and, not_le] at hn
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · rw [hn0, ha, zero_mul]
    · have hnxlt : x < n := (Nat.floor_lt hx.le).mp (hn hn0)
      have ht : 0 < (n : ℝ) / x := div_pos (Nat.cast_pos.mpr hn0) hx
      rw [mellinWeightOne_eq_ofReal_max ht,
        max_eq_right (sub_nonpos.mpr ((one_le_div hx).mpr hnxlt.le)), Complex.ofReal_zero, mul_zero]
  rw [tsum_eq_sum hvanish, reciprocalWeightedSum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn0, hnx⟩ := Finset.mem_Ioc.mp hn
  have ht : 0 < (n : ℝ) / x := div_pos (Nat.cast_pos.mpr hn0) hx
  rw [mellinWeightOne_eq_ofReal_max ht,
    max_eq_left (sub_nonneg.mpr ((div_le_one hx).mpr ((Nat.le_floor_iff hx.le).mp hnx)))]

/-- For `a 0 = 0`, `x,τ > 0` and absolute convergence at `σ + τ`, the finite sum with
coefficients shifted by `n^(-σ)` equals the normalized reciprocal L-series integral.
Combine finite-support collapse with shifted Mellin inversion. This supplies the arithmetic
identity for the general reciprocal explicit formula. -/
theorem reciprocalWeightedSum_shifted_eq_integral_LSeries (a : ℕ → ℂ) (ha : a 0 = 0) (σ : ℝ)
    {x τ : ℝ} (hx : 0 < x) (hτ : 0 < τ) (hsum : LSeriesSummable a ((σ + τ : ℝ) : ℂ)) :
    reciprocalWeightedSum (shiftedLSeriesCoefficient a σ) x =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ,
          LSeries a (((σ + τ : ℝ) : ℂ) + y * Complex.I) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1)) := by
  have ha0 : shiftedLSeriesCoefficient a σ 0 = 0 := by rw [shiftedLSeriesCoefficient, ha, zero_mul]
  rw [← mellinWeightOne_tsum_eq_reciprocalWeightedSum _ ha0 hx]
  exact mellinWeightOne_shifted_tsum_eq_integral_LSeries a ha σ hx hτ hsum

/-- For `a 0 = 0`, positive `x,τ` and absolute convergence at `τ`, the reciprocal L-series
integrand is integrable. The coefficient terms have summable integral norms, so their sum is
integrable; identify it with the L-series kernel. This permits splitting contour integrals. -/
theorem integrable_reciprocalMellin_LSeries (a : ℕ → ℂ) (ha : a 0 = 0) {x τ : ℝ} (hx : 0 < x)
    (hτ : 0 < τ) (hsum : LSeriesSummable a (τ : ℂ)) :
    MeasureTheory.Integrable
      (fun y : ℝ ↦
        LSeries a ((τ : ℂ) + y * Complex.I) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
          (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1))) := by
  have hi :=
    Analysis.integrable_tsum_of_summable_integral_norm (fun n ↦ reciprocalMellinTerm a x τ n)
      (integrable_reciprocalMellinTerm a ha hx hτ)
      (summable_integral_norm_reciprocalMellinTerm a ha hx hτ hsum)
  exact hi.congr (Filter.Eventually.of_forall (tsum_reciprocalMellinTerm a ha x τ))

/-- For coefficients vanishing at zero, `x,τ > 0` and convergence at `σ + τ`, the reciprocal
L-series integrand shifted by `σ` is integrable. Apply unshifted integrability to shifted
coefficients and translate their L-series. This controls the ordinary logarithmic derivative. -/
theorem integrable_reciprocalMellin_shiftedLSeries (a : ℕ → ℂ) (ha : a 0 = 0) (σ : ℝ)
    {x τ : ℝ} (hx : 0 < x) (hτ : 0 < τ) (hsum : LSeriesSummable a ((σ + τ : ℝ) : ℂ)) :
    MeasureTheory.Integrable (fun y : ℝ ↦
      LSeries a (((σ + τ : ℝ) : ℂ) + y * Complex.I) *
        (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
        (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1))) := by
  have ha0 : shiftedLSeriesCoefficient a σ 0 = 0 := by
    rw [shiftedLSeriesCoefficient, ha, zero_mul]
  have hs : LSeriesSummable (shiftedLSeriesCoefficient a σ) (τ : ℂ) :=
    (LSeriesSummable_shiftedLSeriesCoefficient a σ (τ : ℂ)).mpr
      (by
        simpa only [Complex.ofReal_add] using hsum
        )
  have hi := integrable_reciprocalMellin_LSeries _ ha0 hx hτ hs
  apply hi.congr
  filter_upwards with y
  simp only [LSeries_shiftedLSeriesCoefficient, Complex.ofReal_add, add_assoc]

end PseudoPrime.AnalyticNumberTheory.General
