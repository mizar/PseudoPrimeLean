/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.ShiftedPoleMellin
public import PseudoPrime.AnalyticNumberTheory.General.ReciprocalResolventMellin

/-!
# Reciprocal Mellin residues of gamma poles

For shifts with nonnegative real part, integrate the poles `-1 - κ - 2n` against the reciprocal
Mellin kernel. The pole at `-1` contributes `-log x / x`; all other terms are bounded by
a summable coefficient times `1 / x`. This gives the gamma remainder for the general L-function
reciprocal formula.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- The gamma pole shifted by the reciprocal formula's center at one: `-1 - κ - 2n`.
For `Re κ ≥ 0` it lies strictly in the left half-plane. These are the poles used in the
completion-factor Mellin expansion. -/
noncomputable def reciprocalGammaPole (κ : ℂ) (n : ℕ) : ℂ :=
  -(1 + κ + 2 * (n : ℂ))

/-- The reciprocal Mellin residue at `-1 - κ - 2n`, for a real cutoff `x`.
At the repeated pole `-1` use `-log x / x`; otherwise use `(x^α - 1/x)/(α (α + 1))`.
This definition treats the zero gamma shift without division by a vanishing denominator. -/
noncomputable def reciprocalGammaResidue (κ : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  if reciprocalGammaPole κ n = -1 then -(Real.log x : ℂ) / (x : ℂ)
  else
    ((x : ℂ) ^ reciprocalGammaPole κ n - (x : ℂ)⁻¹) /
      (reciprocalGammaPole κ n * (reciprocalGammaPole κ n + 1))

/-- For a gamma shift with nonnegative real part, every pole `-1 - κ - 2n` has negative real
part. Expand real parts and use nonnegativity of the natural index. This permits Mellin
inversion and integration of the pole series. -/
theorem reciprocalGammaPole_re_neg {κ : ℂ} (hκ : 0 ≤ κ.re) (n : ℕ) :
    (reciprocalGammaPole κ n).re < 0 := by
  simp only [reciprocalGammaPole, Complex.neg_re, Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.re_ofNat, Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero]
  linarith only [hκ, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

/-- For `Re κ ≥ 0`, the shifted poles have summable inverse-three-halves norm mass.
Apply the general gamma-pole power bound at center one. This gives the absolute integral-norm
control required to exchange the reciprocal pole series and vertical integral. -/
theorem summable_reciprocalGammaPole_mass {κ : ℂ} (hκ : 0 ≤ κ.re) :
    Summable (fun n : ℕ ↦ (1 : ℝ) / ‖reciprocalGammaPole κ n‖ ^ (3 / 2 : ℝ)) := by
  simpa only [reciprocalGammaPole, Complex.ofReal_one] using
    (summable_gammaPole_power_mass hκ (σ := 1) le_rfl
      (show (1 : ℝ) < 3 / 2 by
        norm_num only
        ))

/-- For `Re κ ≥ 0`, `τ > 0` and `x > 1`, the normalized reciprocal integral at the nth gamma
pole equals its residue. Separate the repeated pole at `-1` from simple poles and apply the
corresponding scalar Mellin evaluations. This evaluates every term before integration of
the full gamma family. -/
theorem integral_reciprocalGammaPole_eq {κ : ℂ} (hκ : 0 ≤ κ.re) {τ x : ℝ} (hτ : 0 < τ) (hx : 1 < x)
    (n : ℕ) :
    (2 * Real.pi)⁻¹ • (∫ y : ℝ, General.reciprocalResolventKernel (reciprocalGammaPole κ n) x τ y) =
      reciprocalGammaResidue κ n x := by
  by_cases he : reciprocalGammaPole κ n = -1
  · rw [reciprocalGammaResidue, ite_eq_left he, he]
    exact General.integral_reciprocalResolventKernel_neg_one hτ hx
  · rw [reciprocalGammaResidue, ite_eq_right he]
    exact General.integral_reciprocalResolventKernel_eq (reciprocalGammaPole_re_neg hκ n) he hτ hx

/-- For `Re κ ≥ 0` and `x,τ > 0`, the reciprocal gamma-pole series is integrable on the
vertical line. Its summable three-halves pole mass supplies the generic resolvent majorant.
This justifies splitting the completion-factor contribution from the ordinary integral. -/
theorem integrable_reciprocalGammaPoleSeries {κ : ℂ} (hκ : 0 ≤ κ.re)
    {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x) :
    MeasureTheory.Integrable (fun y : ℝ ↦
      ∑' n : ℕ, General.reciprocalResolventKernel (reciprocalGammaPole κ n) x τ y) := by
  have hi := General.integrable_tsum_reciprocalResolventKernel (reciprocalGammaPole κ)
    (fun _ ↦ 1) (reciprocalGammaPole_re_neg hκ) hτ hx
    (by
      simpa only [Nat.cast_one] using summable_reciprocalGammaPole_mass hκ
      )
  simpa only [Nat.cast_one, one_mul] using hi

/-- For `Re κ ≥ 0`, `τ > 0` and `x > 1`, the normalized integral of the reciprocal gamma
pole series is the sum of its residues. Absolute integral-norm control permits termwise
integration, including the repeated pole. This computes one gamma factor's contribution. -/
theorem integral_tsum_reciprocalGammaPole_eq {κ : ℂ} (hκ : 0 ≤ κ.re)
    {τ x : ℝ} (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ • (∫ y : ℝ,
      ∑' n : ℕ, General.reciprocalResolventKernel (reciprocalGammaPole κ n) x τ y) =
        ∑' n : ℕ, reciprocalGammaResidue κ n x := by
  have hi := General.integral_tsum_reciprocalResolventKernel (reciprocalGammaPole κ)
    (fun _ ↦ 1) (reciprocalGammaPole_re_neg hκ) hτ (zero_lt_one.trans hx)
    (by
      simpa only [Nat.cast_one] using summable_reciprocalGammaPole_mass hκ
      )
  simp only [Nat.cast_one, one_mul] at hi
  rw [hi, ← tsum_const_smul'' (2 * Real.pi : ℝ)⁻¹]
  exact tsum_congr (integral_reciprocalGammaPole_eq hκ hτ hx)

end PseudoPrime.AnalyticNumberTheory.Gamma

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- The nonnegative coefficient `2/(norm α * norm (α + 1))` at `α = -1 - κ - 2n`.
Away from the repeated pole, it bounds the residue after multiplying by `x`. The totalized
value at the repeated pole is zero; its logarithmic contribution is handled separately. -/
noncomputable def reciprocalGammaCoefficient (κ : ℂ) (n : ℕ) : ℝ :=
  2 / (‖reciprocalGammaPole κ n‖ * ‖reciprocalGammaPole κ n + 1‖)

/-- For `Re κ ≥ 0`, the norm of `α + 1 = -κ - 2n` is at least `2n`.
Take real parts and compare with the complex norm. This excludes repeated poles at positive
indices and controls the tail denominators. -/
theorem reciprocalGammaPole_add_one_norm_lower {κ : ℂ} (hκ : 0 ≤ κ.re) (n : ℕ) :
    2 * (n : ℝ) ≤ ‖reciprocalGammaPole κ n + 1‖ := by
  have he : reciprocalGammaPole κ n + 1 = -(κ + 2 * (n : ℂ)) := by
    unfold reciprocalGammaPole
    ring
  rw [he, norm_neg]
  have hr := Complex.re_le_norm (κ + 2 * (n : ℂ))
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re, Complex.im_ofNat,
    Complex.natCast_im, mul_zero, sub_zero] at hr
  linarith only [hr, hκ]

/-- For `Re κ ≥ 0` and a positive natural index, the reciprocal coefficient is at most
`4 / norm α²`. The shifted pole norm is at most twice the adjacent denominator's norm;
clear positive real denominators. This compares the coefficient tail with a summable
inverse-square gamma-pole series. -/
theorem reciprocalGammaCoefficient_le {κ : ℂ} (hκ : 0 ≤ κ.re) {n : ℕ} (hn : n ≠ 0) :
    reciprocalGammaCoefficient κ n ≤ 4 / ‖reciprocalGammaPole κ n‖ ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn)
  have hb := reciprocalGammaPole_add_one_norm_lower hκ n
  have ha : 0 < ‖reciprocalGammaPole κ n‖ := by
    have hl := gammaPole_norm_lower hκ (σ := 1) le_rfl n
    simp only [Complex.ofReal_one] at hl
    change (n : ℝ) + 1 ≤ ‖reciprocalGammaPole κ n‖ at hl
    linarith only [hl, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  have hbn : 0 < ‖reciprocalGammaPole κ n + 1‖ := by linarith only [hb, hn1]
  have ht := norm_sub_le (reciprocalGammaPole κ n + 1) (1 : ℂ)
  rw [add_sub_cancel_right, norm_one] at ht
  have hcomp : ‖reciprocalGammaPole κ n‖ ≤ 2 * ‖reciprocalGammaPole κ n + 1‖ := by
    linarith only [ht, hb, hn1]
  unfold reciprocalGammaCoefficient
  apply (div_le_div_iff₀ (mul_pos ha hbn) (pow_pos ha 2)).mpr
  nlinarith only [mul_nonneg ha.le (sub_nonneg.mpr hcomp)]

/-- For a shift with nonnegative real part, the reciprocal coefficients are summable.
Discard the single index zero and dominate the positive tail by the inverse-square pole
series. This gives a finite constant for the reciprocal remainder bound. -/
theorem summable_reciprocalGammaCoefficient {κ : ℂ} (hκ : 0 ≤ κ.re) :
    Summable (reciprocalGammaCoefficient κ) := by
  have hs : Summable (fun n : ℕ ↦ 4 / ‖reciprocalGammaPole κ n‖ ^ 2) := by
    simpa only [reciprocalGammaPole, Complex.ofReal_one, Real.rpow_two,
      mul_one_div] using
      (summable_gammaPole_power_mass hκ (σ := 1) le_rfl
        (show (1 : ℝ) < 2 by
          norm_num only
          )).mul_left 4
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le
    (fun n ↦ div_nonneg (by norm_num only) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) _
    ((summable_nat_add_iff 1).mpr hs)
  intro n
  exact reciprocalGammaCoefficient_le hκ (Nat.succ_ne_zero n)

end PseudoPrime.AnalyticNumberTheory.Gamma

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- For `Re κ ≥ 0`, `x > 1` and a pole different from `-1`, the residue norm is at most
its reciprocal coefficient divided by `x`. The real exponent is at most `-1`, so both
numerator terms have norm at most `1/x`. This controls all simple poles. -/
theorem norm_reciprocalGammaResidue_le_of_ne {κ : ℂ} (hκ : 0 ≤ κ.re) {x : ℝ} (hx : 1 < x)
    {n : ℕ} (he : reciprocalGammaPole κ n ≠ -1) :
    ‖reciprocalGammaResidue κ n x‖ ≤ reciprocalGammaCoefficient κ n / x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hr : (reciprocalGammaPole κ n).re ≤ -1 := by
    simp only [reciprocalGammaPole, Complex.neg_re, Complex.add_re, Complex.one_re,
      Complex.mul_re, Complex.re_ofNat, Complex.natCast_re, Complex.im_ofNat,
      Complex.natCast_im, mul_zero, sub_zero]
    linarith only [hκ, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  have hp : ‖(x : ℂ) ^ reciprocalGammaPole κ n‖ ≤ x⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx.le hr
  have hi : ‖(x : ℂ)⁻¹‖ = x⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  have hd : ‖(x : ℂ) ^ reciprocalGammaPole κ n - (x : ℂ)⁻¹‖ ≤ 2 / x := by
    have hb := norm_sub_le ((x : ℂ) ^ reciprocalGammaPole κ n) (x : ℂ)⁻¹
    rw [hi] at hb
    rw [div_eq_mul_inv]
    linarith only [hb, hp]
  rw [reciprocalGammaResidue, ite_eq_right he, norm_div, norm_mul]
  apply le_trans (div_le_div_of_nonneg_right hd (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  exact le_of_eq (by
    unfold reciprocalGammaCoefficient
    ring
    )

/-- For `Re κ ≥ 0`, a gamma pole can equal `-1` only at index zero.
The adjacent pole norm vanishes, while its lower bound is `2n`; hence `n = 0`.
This isolates the logarithmic contribution in the residue-series estimate. -/
theorem reciprocalGammaPole_eq_neg_one_index {κ : ℂ} (hκ : 0 ≤ κ.re) {n : ℕ}
    (he : reciprocalGammaPole κ n = -1) : n = 0 := by
  have hb := reciprocalGammaPole_add_one_norm_lower hκ n
  simp only [he, neg_add_cancel, norm_zero] at hb
  apply Nat.cast_eq_zero.mp (show (n : ℝ) = 0 from ?_)
  linarith only [hb, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

/-- For `Re κ ≥ 0` and `x > 1`, bound each residue by a summable coefficient times
`(log x + 1)/x`, with an extra unit coefficient only at index zero. Separate the repeated
pole, whose norm is `log x/x`, and dominate every simple pole by the reciprocal coefficient.
This provides a common nonnegative majorant for the whole gamma series. -/
theorem norm_reciprocalGammaResidue_le {κ : ℂ} (hκ : 0 ≤ κ.re) {x : ℝ} (hx : 1 < x) (n : ℕ) :
    ‖reciprocalGammaResidue κ n x‖ ≤
      (reciprocalGammaCoefficient κ n + if n = 0 then 1 else 0) * ((Real.log x + 1) / x) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hl : 0 ≤ Real.log x := (Real.log_pos hx).le
  have hc : 0 ≤ reciprocalGammaCoefficient κ n :=
    div_nonneg (by norm_num only) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  by_cases he : reciprocalGammaPole κ n = -1
  · have hn := reciprocalGammaPole_eq_neg_one_index hκ he
    rw [reciprocalGammaResidue, ite_eq_left he, norm_div, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hl, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, hn,
      ite_eq_left rfl]
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hx0.le
    rw [hn] at hc
    nlinarith only [hc, hl, mul_nonneg hc hl]
  · have hb := norm_reciprocalGammaResidue_le_of_ne hκ hx he
    apply hb.trans
    have hw : 0 ≤ (if n = 0 then (1 : ℝ) else 0) := by split_ifs <;> norm_num only
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hx0.le
    nlinarith only [hc, hl, hw, mul_nonneg hc hl, mul_nonneg hw hl]

end PseudoPrime.AnalyticNumberTheory.Gamma

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- For `Re κ ≥ 0` and `x > 1`, the gamma residues are absolutely summable.
Use the common residue majorant and the summable coefficient series, adding the single
index-zero term. This permits norm estimates of the total residue sum. -/
theorem summable_norm_reciprocalGammaResidue {κ : ℂ} (hκ : 0 ≤ κ.re) {x : ℝ} (hx : 1 < x) :
    Summable (fun n : ℕ ↦ ‖reciprocalGammaResidue κ n x‖) := by
  have hs := (summable_reciprocalGammaCoefficient hκ).add ((hasSum_ite_eq 0 (1 : ℝ)).summable)
  exact
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (norm_reciprocalGammaResidue_le hκ hx)
      (hs.mul_right ((Real.log x + 1) / x))

/-- For `Re κ ≥ 0` and `x > 1`, the norm of the gamma residue sum is bounded by the total
reciprocal coefficient plus one, multiplied by `(log x + 1)/x`. Sum the pointwise majorant
and use the triangle inequality for absolutely convergent series. The constant may depend
on the fixed gamma shift; this is enough for the fixed-function asymptotic statement. -/
theorem norm_tsum_reciprocalGammaResidue_le {κ : ℂ} (hκ : 0 ≤ κ.re) {x : ℝ} (hx : 1 < x) :
    ‖∑' n : ℕ, reciprocalGammaResidue κ n x‖ ≤
      ((∑' n : ℕ, reciprocalGammaCoefficient κ n) + 1) * ((Real.log x + 1) / x) := by
  have hsn := summable_norm_reciprocalGammaResidue hκ hx
  have hsc := summable_reciprocalGammaCoefficient hκ
  have hs := hsc.add ((hasSum_ite_eq 0 (1 : ℝ)).summable)
  apply (norm_tsum_le_tsum_norm hsn).trans
  have hb :=
    Summable.tsum_le_tsum (norm_reciprocalGammaResidue_le hκ hx) hsn
      (hs.mul_right ((Real.log x + 1) / x))
  simpa only [tsum_mul_right, hsc.tsum_add ((hasSum_ite_eq 0 (1 : ℝ)).summable), tsum_ite_eq] using
    hb

end PseudoPrime.AnalyticNumberTheory.Gamma
