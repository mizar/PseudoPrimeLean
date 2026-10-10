/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ShiftedZeroBounds
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Shifted gamma residues

For gamma shifts with nonnegative real parts, inverse-square bounds justify
summation and integration of residues and give a degree-dependent error bound.
Shifts with real part at least two yield the sharper zeta trivial-zero error
`1/(3 x³ (log x)²)` after logarithmic normalization, for `x > 1`.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The term `x^(-σ-κ-2m) / (σ+κ+2m)²` for the shifted gamma pole -κ-2m.
It is defined for real x and σ, complex κ, and natural m, with totalized division.
When x > 1, σ ≥ 1, and Re κ ≥ 0, its norm has a summable inverse-square majorant.
These terms form the gamma contribution to the shifted logarithmic formula. -/
noncomputable def gammaShiftResidue (x : ℝ) (κ : ℂ) (σ : ℝ) (m : ℕ) : ℂ :=
  (x : ℂ) ^ (-((σ : ℂ) + κ + 2 * (m : ℂ))) / ((σ : ℂ) + κ + 2 * (m : ℂ)) ^ 2

/-- For x>1, sigma>=1 and Re kappa>=0, bound each shifted gamma residue by
x^(-sigma)/(m+1)^2. The real part controls the denominator and the complex power. -/
theorem norm_gammaShiftResidue_le {x σ : ℝ} {κ : ℂ} (hx : 1 < x) (hσ : 1 ≤ σ) (hκ : 0 ≤ κ.re)
    (m : ℕ) : ‖gammaShiftResidue x κ σ m‖ ≤ x ^ (-σ) * (1 / ((m : ℝ) + 1) ^ 2) := by
  let w : ℂ := (σ : ℂ) + κ + 2 * (m : ℂ)
  have hre : w.re = σ + κ.re + 2 * (m : ℝ) := by
    simp only [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
      Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hr : (m : ℝ) + 1 ≤ w.re := by
    rw [hre]; linarith only [hσ, hκ, hm]
  have hpos : 0 < ((m : ℝ) + 1) ^ 2 := sq_pos_of_pos (by linarith only [hm])
  have hsquare : ((m : ℝ) + 1) ^ 2 ≤ ‖w‖ ^ 2 := by
    have hprod : 0 ≤ (w.re - ((m : ℝ) + 1)) * (w.re + ((m : ℝ) + 1)) :=
      mul_nonneg (sub_nonneg.mpr hr) (by linarith only [hr, hm])
    have hn := Complex.re_sq_le_normSq w
    rw [← Complex.norm_mul_self_eq_normSq] at hn
    nlinarith only [hprod, hn]
  have hp : x ^ (-w.re) ≤ x ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le hx.le
      (by
        rw [hre]; linarith only [hκ, hm])
  have hd :=
    div_le_div_of_nonneg_left (Real.rpow_nonneg (zero_lt_one.trans hx).le (-w.re)) hpos hsquare
  have hu := div_le_div_of_nonneg_right hp (sq_nonneg ((m : ℝ) + 1))
  calc
    ‖gammaShiftResidue x κ σ m‖ = x ^ (-w.re) / ‖w‖ ^ 2 := by
      rw [gammaShiftResidue, norm_div, norm_pow,
        Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
      simp only [Complex.neg_re]
      rfl
    _ ≤ x ^ (-σ) / ((m : ℝ) + 1) ^ 2 := hd.trans hu
    _ = _ := by ring

/-- The real inverse-square majorant `1/(m+1)²` has sum `π²/6`.
Shift the Basel series by one; its zero-index term vanishes. This supplies the
summable majorant for each gamma pole family. -/
theorem hasSum_gammaShiftMajorant :
    HasSum (fun m : ℕ ↦ (1 : ℝ) / ((m : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h :=
    (hasSum_nat_add_iff (f := fun m : ℕ ↦ (1 : ℝ) / (m : ℝ) ^ 2) (g := Real.pi ^ 2 / 6) 1).mpr
      (by
        simpa only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by norm_num only : 2 ≠ 0),
          div_zero, add_zero] using hasSum_zeta_two)
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The inverse-square majorant has total mass at most two.
Use the explicit upper bound on pi to obtain the constant in the gamma error. -/
theorem gammaShiftMajorantMass_le_two : Real.pi ^ 2 / 6 ≤ 2 := by
  have h := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d2
  nlinarith only [h]

/-- The countable sum of gammaShiftResidue over natural m for a single complex shift κ.
The definition accepts all real x and σ; absolute convergence is proved for
x > 1, σ ≥ 1, and Re κ ≥ 0. This collects the pole sequence of one gamma factor
before integration over σ > 1. -/
noncomputable def gammaShiftSum (x : ℝ) (κ : ℂ) (σ : ℝ) : ℂ :=
  ∑' m : ℕ, gammaShiftResidue x κ σ m

/-- For x > 1, σ ≥ 1, and a complex shift with Re κ ≥ 0, the gamma residue series
is absolutely summable. Compare each norm with `x^(-σ)/(m+1)²` and use the shifted
Basel series. This justifies the countable gamma pole sum in the shifted formula. -/
theorem summable_gammaShiftResidues {x σ : ℝ} {κ : ℂ} (hx : 1 < x) (hσ : 1 ≤ σ) (hκ : 0 ≤ κ.re) :
    Summable (gammaShiftResidue x κ σ) :=
  (hasSum_gammaShiftMajorant.summable.mul_left (x ^ (-σ))).of_norm_bounded
    (norm_gammaShiftResidue_le hx hσ hκ)

/-- For x > 1, σ ≥ 1, and Re κ ≥ 0, the gamma residue sum has norm at most `2 x^(-σ)`.
Apply the triangle inequality to the absolutely convergent series, sum the inverse-square
majorant, and bound its Basel mass by two. This supplies the integrable gamma majorant. -/
theorem norm_gammaShiftSum_le {x σ : ℝ} {κ : ℂ} (hx : 1 < x) (hσ : 1 ≤ σ) (hκ : 0 ≤ κ.re) :
    ‖gammaShiftSum x κ σ‖ ≤ 2 * x ^ (-σ) := by
  have hb := norm_gammaShiftResidue_le hx hσ hκ
  have hm := hasSum_gammaShiftMajorant.summable.mul_left (x ^ (-σ))
  have hn : Summable (fun m : ℕ ↦ ‖gammaShiftResidue x κ σ m‖) :=
    Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _) hb hm
  calc
    _ ≤ ∑' m : ℕ, ‖gammaShiftResidue x κ σ m‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' m : ℕ, x ^ (-σ) * (1 / ((m : ℝ) + 1) ^ 2) := Summable.tsum_le_tsum hb hn hm
    _ = x ^ (-σ) * (Real.pi ^ 2 / 6) := by rw [tsum_mul_left, hasSum_gammaShiftMajorant.tsum_eq]
    _ ≤ x ^ (-σ) * 2 :=
      mul_le_mul_of_nonneg_left gammaShiftMajorantMass_le_two
        (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
    _ = _ := mul_comm _ _

/-- For x>1, each gamma residue is measurable in sigma.
Continuity of its complex-power numerator and measurability of division suffice. -/
theorem measurable_gammaShiftResidue {x : ℝ} (hx : 1 < x) (κ : ℂ) (m : ℕ) :
    Measurable (fun σ : ℝ ↦ gammaShiftResidue x κ σ m) := by
  have hw : Continuous (fun σ : ℝ ↦ (σ : ℂ) + κ + 2 * (m : ℂ)) :=
    (Complex.continuous_ofReal.add continuous_const).add continuous_const
  have hp := hw.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'))
  exact hp.measurable.div (hw.measurable.pow_const 2)

/-- For x>1, the gamma residue sum is measurable in sigma.
Apply measurability of countable sums to the individual residues. -/
theorem measurable_gammaShiftSum {x : ℝ} (hx : 1 < x) (κ : ℂ) : Measurable (gammaShiftSum x κ) :=
  Measurable.tsum (fun m ↦ measurable_gammaShiftResidue hx κ m)

/-- For x > 1 and Re κ ≥ 0, each gamma residue is integrable as a function of real σ
on σ > 1. Measurability and the bound `x^(-σ)/(m+1)²` give integrability.
This permits integrating individual gamma poles before summing their contributions. -/
theorem integrableOn_gammaShiftResidue {x : ℝ} {κ : ℂ} (hx : 1 < x) (hκ : 0 ≤ κ.re) (m : ℕ) :
    MeasureTheory.IntegrableOn (fun σ : ℝ ↦ gammaShiftResidue x κ σ m) (Set.Ioi 1) := by
  apply
    ((integrableOn_rpow_neg hx).mul_const (1 / ((m : ℝ) + 1) ^ 2)).mono'
      (measurable_gammaShiftResidue hx κ m).aestronglyMeasurable
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with σ hσ
  exact norm_gammaShiftResidue_le hx hσ.le hκ m

/-- For x > 1 and Re κ ≥ 0, the countable gamma residue sum is integrable on real σ > 1.
Its measurable norm is bounded by the integrable function `2 x^(-σ)`.
This supplies the gamma contribution's integrability in the logarithmic L-value formula. -/
theorem integrableOn_gammaShiftSum {x : ℝ} {κ : ℂ} (hx : 1 < x) (hκ : 0 ≤ κ.re) :
    MeasureTheory.IntegrableOn (gammaShiftSum x κ) (Set.Ioi 1) := by
  apply
    ((integrableOn_rpow_neg hx).const_mul 2).mono'
      (measurable_gammaShiftSum hx κ).aestronglyMeasurable
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with σ hσ
  exact norm_gammaShiftSum_le hx hσ.le hκ

/-- For x > 1, Re κ ≥ 0, and natural m, the integral over σ > 1 of the gamma residue's
norm is at most `x⁻¹ / (log x (m+1)²)`. Integrate the pointwise exponential majorant.
The resulting summable bounds justify interchanging the pole series and the shift integral. -/
theorem integral_norm_gammaShiftResidue_le {x : ℝ} {κ : ℂ} (hx : 1 < x) (hκ : 0 ≤ κ.re) (m : ℕ) :
    (∫ σ : ℝ in Set.Ioi 1, ‖gammaShiftResidue x κ σ m‖) ≤
      x⁻¹ / Real.log x * (1 / ((m : ℝ) + 1) ^ 2) := by
  have hb :
    ∀ᵐ σ : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi 1),
      ‖gammaShiftResidue x κ σ m‖ ≤ x ^ (-σ) * (1 / ((m : ℝ) + 1) ^ 2) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with σ hσ
    exact norm_gammaShiftResidue_le hx hσ.le hκ m
  have hi :=
    MeasureTheory.integral_mono_ae (integrableOn_gammaShiftResidue hx hκ m).norm
      ((integrableOn_rpow_neg hx).mul_const _) hb
  rwa [MeasureTheory.integral_mul_const, integral_rpow_neg hx] at hi

/-- For x > 1 and Re κ ≥ 0, integrating the gamma residue series over real σ > 1
agrees with summing the integrals of its terms. Individual integrability and summability
of their norm integrals give the Bochner sum-integral interchange.
This expresses the integrated gamma contribution through individual poles. -/
theorem integral_tsum_gammaShiftResidues {x : ℝ} {κ : ℂ} (hx : 1 < x) (hκ : 0 ≤ κ.re) :
    (∫ σ : ℝ in Set.Ioi 1, gammaShiftSum x κ σ) =
      ∑' m : ℕ, ∫ σ : ℝ in Set.Ioi 1, gammaShiftResidue x κ σ m := by
  have hn : Summable (fun m : ℕ ↦ ∫ σ : ℝ in Set.Ioi 1, ‖gammaShiftResidue x κ σ m‖) :=
    Summable.of_nonneg_of_le (fun m ↦ MeasureTheory.integral_nonneg (fun σ ↦ norm_nonneg _))
      (integral_norm_gammaShiftResidue_le hx hκ)
      (hasSum_gammaShiftMajorant.summable.mul_left (x⁻¹ / Real.log x))
  exact
    (MeasureTheory.hasSum_integral_of_summable_integral_norm (integrableOn_gammaShiftResidue hx hκ)
        hn).tsum_eq.symm

/-- For x > 1 and Re κ ≥ 0, the integral over σ > 1 of the gamma residue sum has norm
at most `2 / (x log x)`. Apply the integral triangle inequality with the exponential
majorant and evaluate its half-line integral. This bounds the unnormalized gamma error. -/
theorem norm_integral_gammaShiftSum_le {x : ℝ} {κ : ℂ} (hx : 1 < x) (hκ : 0 ≤ κ.re) :
    ‖∫ σ : ℝ in Set.Ioi 1, gammaShiftSum x κ σ‖ ≤ 2 / (x * Real.log x) := by
  have hb :
    ∀ᵐ σ : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi 1), ‖gammaShiftSum x κ σ‖ ≤ 2 * x ^ (-σ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with σ hσ
    exact norm_gammaShiftSum_le hx hσ.le hκ
  have hi := MeasureTheory.norm_integral_le_of_norm_le ((integrableOn_rpow_neg hx).const_mul 2) hb
  rw [MeasureTheory.integral_const_mul, integral_rpow_neg hx] at hi
  convert hi using 1
  ring

/-- For x > 1 and Re κ ≥ 0, the gamma residue sum integrated over σ > 1 and divided
by log x has norm at most `2 / (x (log x)²)`. Divide the integral norm bound by
the positive logarithm. This gives the normalized error from one complex gamma shift. -/
theorem norm_integrated_gammaShiftSum_div_log_le {x : ℝ} {κ : ℂ} (hx : 1 < x) (hκ : 0 ≤ κ.re) :
    ‖(∫ σ : ℝ in Set.Ioi 1, gammaShiftSum x κ σ) / (Real.log x : ℂ)‖ ≤
      2 / (x * (Real.log x) ^ 2) := by
  have hlog := Real.log_pos hx
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  calc
    _ ≤ (2 / (x * Real.log x)) / Real.log x :=
      div_le_div_of_nonneg_right (norm_integral_gammaShiftSum_le hx hκ) hlog.le
    _ = _ := by ring

/-- The finite sum of gammaShiftSum over a family κ : Fin d → ℂ.
It is defined for every natural d and real x and σ, and equals zero when d = 0.
Each family member contributes its countable pole series; this combines the gamma
factors before the degree-dependent integrated error estimate. -/
noncomputable def gammaShiftFamilySum {d : ℕ} (κ : Fin d → ℂ) (x σ : ℝ) : ℂ :=
  ∑ j : Fin d, gammaShiftSum x (κ j) σ

/-- For x>1 and shifts with nonnegative real parts, the finite gamma family
is integrable on sigma>1. Sum the individual integrability statements. -/
theorem integrableOn_gammaShiftFamilySum {d : ℕ} (κ : Fin d → ℂ) {x : ℝ} (hx : 1 < x)
    (hκ : ∀ j, 0 ≤ (κ j).re) : MeasureTheory.IntegrableOn (gammaShiftFamilySum κ x) (Set.Ioi 1) :=
  MeasureTheory.integrable_finsetSum Finset.univ (fun j _ ↦ integrableOn_gammaShiftSum hx (hκ j))

/-- For x>1 and shifts with nonnegative real parts, integration commutes with
the finite family and each countable residue series, by absolute integrability. -/
theorem integral_gammaShiftFamilySum_eq_sum_tsum {d : ℕ} (κ : Fin d → ℂ) {x : ℝ} (hx : 1 < x)
    (hκ : ∀ j, 0 ≤ (κ j).re) :
    (∫ σ : ℝ in Set.Ioi 1, gammaShiftFamilySum κ x σ) =
      ∑ j : Fin d, ∑' m : ℕ, ∫ σ : ℝ in Set.Ioi 1, gammaShiftResidue x (κ j) σ m := by
  unfold gammaShiftFamilySum
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ ↦ integrableOn_gammaShiftSum hx (hκ j))]
  exact Finset.sum_congr rfl (fun j _ ↦ integral_tsum_gammaShiftResidues hx (hκ j))

/-- For x>1 and d shifts with nonnegative real parts, the normalized integrated
gamma family has norm at most 2*d/(x*log(x)^2). Sum the individual norm bounds.
This supplies the gamma-error estimate for the generalized logarithmic formula. -/
theorem norm_integrated_gammaShiftFamilySum_div_log_le {d : ℕ} (κ : Fin d → ℂ) {x : ℝ} (hx : 1 < x)
    (hκ : ∀ j, 0 ≤ (κ j).re) :
    ‖(∫ σ : ℝ in Set.Ioi 1, gammaShiftFamilySum κ x σ) / (Real.log x : ℂ)‖ ≤
      2 * (d : ℝ) / (x * (Real.log x) ^ 2) := by
  unfold gammaShiftFamilySum
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ ↦ integrableOn_gammaShiftSum hx (hκ j)),
    Finset.sum_div]
  calc
    _ ≤ ∑ j : Fin d, ‖(∫ σ : ℝ in Set.Ioi 1, gammaShiftSum x (κ j) σ) / (Real.log x : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin d, 2 / (x * (Real.log x) ^ 2) :=
      Finset.sum_le_sum (fun j _ ↦ norm_integrated_gammaShiftSum_div_log_le hx (hκ j))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The inverse-square weight `1/9` at zero and `1/(4(n+1)²)` at positive indices.
It majorizes gamma pole denominators for shifts with real part at least two.
A correction to one quarter of the Basel series gives total mass at most one third. -/
private noncomputable def gammaShiftTwoWeight (n : ℕ) : ℝ :=
  (1 / 4) * (1 / ((n : ℝ) + 1) ^ 2) - if n = 0 then 5 / 36 else 0

/-- The refined gamma-pole majorant sums to pi^2/24-5/36. Subtract the single
zero-index correction from one quarter of the Basel family. -/
private theorem hasSum_gammaShiftTwoWeight :
    HasSum gammaShiftTwoWeight ((1 / 4) * (Real.pi ^ 2 / 6) - 5 / 36) := by
  exact (hasSum_gammaShiftMajorant.mul_left (1 / 4)).sub (hasSum_ite_eq 0 (5 / 36 : ℝ))

/-- The refined gamma-pole majorant has mass at most one third. Use the certified
upper bound on pi and a rational comparison. This fixes the trivial-zero constant. -/
private theorem gammaShiftTwoWeight_mass_le_third :
    (1 / 4) * (Real.pi ^ 2 / 6) - 5 / 36 ≤ (1 / 3 : ℝ) := by
  have h := mul_self_le_mul_self Real.pi_pos.le Real.pi_lt_d4.le
  norm_num only at h
  nlinarith only [h]

/-- For x > 1, sigma >= 1 and Re kappa >= 2, bound each gamma residue by
x^(-sigma-2) times the refined inverse-square majorant. The first denominator
is at least three; later denominators are at least 2(n+1). -/
private theorem norm_gammaShiftResidue_le_of_two_le_re {x σ : ℝ} {κ : ℂ} (hx : 1 < x) (hσ : 1 ≤ σ)
    (hκ : 2 ≤ κ.re) (n : ℕ) :
    ‖gammaShiftResidue x κ σ n‖ ≤ x ^ (-σ - 2) * gammaShiftTwoWeight n := by
  let w : ℂ := (σ : ℂ) + κ + 2 * (n : ℂ)
  have hre : w.re = σ + κ.re + 2 * (n : ℝ) := by
    simp only [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
      Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero]
  have hr : σ + 2 + 2 * (n : ℝ) ≤ ‖w‖ := by
    have h := Complex.re_le_norm w
    rw [hre] at h
    linarith only [h, hκ]
  have hp : x ^ (-w.re) ≤ x ^ (-σ - 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hx.le
    rw [hre]
    linarith only [hκ, Nat.cast_nonneg (α := ℝ) n]
  have hnorm : ‖gammaShiftResidue x κ σ n‖ = x ^ (-w.re) / ‖w‖ ^ 2 := by
    rw [gammaShiftResidue, norm_div, norm_pow,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
    simp only [Complex.neg_re]
    rfl
  rw [hnorm]
  have hnum := Real.rpow_nonneg (zero_lt_one.trans hx).le (-σ - 2)
  have hd := div_le_div_of_nonneg_right hp (sq_nonneg ‖w‖)
  apply hd.trans
  by_cases hn : n = 0
  · have h3 : (3 : ℝ) ≤ ‖w‖ := by
      rw [hn, Nat.cast_zero, mul_zero, add_zero] at hr
      linarith only [hr, hσ]
    have hsquare := mul_self_le_mul_self (by norm_num only : (0 : ℝ) ≤ 3) h3
    have hb :=
      div_le_div_of_nonneg_left hnum (show (0 : ℝ) < 9 by norm_num only)
        (show (9 : ℝ) ≤ ‖w‖ ^ 2 by nlinarith only [hsquare])
    have hw : gammaShiftTwoWeight 0 = (1 / 9 : ℝ) := by
      norm_num only [gammaShiftTwoWeight, ite_true, Nat.cast_zero, zero_add, one_pow, div_one]
    rw [hn, hw]
    exact hb.trans_eq (by ring)
  · have hbase : 2 * ((n : ℝ) + 1) ≤ ‖w‖ := by linarith only [hr, hσ]
    have hpos : 0 < ((n : ℝ) + 1) := by linarith only [Nat.cast_nonneg (α := ℝ) n]
    have hsquare := mul_self_le_mul_self (by linarith only [hpos] : 0 ≤ 2 * ((n : ℝ) + 1)) hbase
    have hb :=
      div_le_div_of_nonneg_left hnum
        (show 0 < 4 * ((n : ℝ) + 1) ^ 2 by nlinarith only [sq_pos_of_pos hpos])
        (show 4 * ((n : ℝ) + 1) ^ 2 ≤ ‖w‖ ^ 2 by nlinarith only [hsquare])
    rw [gammaShiftTwoWeight, ite_eq_right hn, sub_zero]
    exact
      hb.trans_eq
        (by
          rw [div_eq_mul_inv, mul_inv_rev]; ring)

/-- For x > 1, sigma >= 1 and Re kappa >= 2, the gamma residue sum has norm at
most x^(-sigma-2)/3. Sum the refined inverse-square majorant and bound its mass.
This retains the extra x^(-2) decay of the zeta trivial zeros. -/
theorem norm_gammaShiftSum_le_of_two_le_re {x σ : ℝ} {κ : ℂ} (hx : 1 < x) (hσ : 1 ≤ σ)
    (hκ : 2 ≤ κ.re) : ‖gammaShiftSum x κ σ‖ ≤ x ^ (-σ - 2) / 3 := by
  have hb := norm_gammaShiftResidue_le_of_two_le_re hx hσ hκ
  have hm := hasSum_gammaShiftTwoWeight.summable.mul_left (x ^ (-σ - 2))
  have hn := (summable_gammaShiftResidues hx hσ (le_trans (by norm_num only : (0 : ℝ) ≤ 2) hκ)).norm
  calc
    _ ≤ ∑' n : ℕ, ‖gammaShiftResidue x κ σ n‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, x ^ (-σ - 2) * gammaShiftTwoWeight n := Summable.tsum_le_tsum hb hn hm
    _ = x ^ (-σ - 2) * ((1 / 4) * (Real.pi ^ 2 / 6) - 5 / 36) := by
      rw [tsum_mul_left, hasSum_gammaShiftTwoWeight.tsum_eq]
    _ ≤ x ^ (-σ - 2) * (1 / 3) :=
      mul_le_mul_of_nonneg_left gammaShiftTwoWeight_mass_le_third
        (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
    _ = _ := by ring

/-- For x > 1 and Re kappa >= 2, the integral of the shifted gamma residues over
sigma > 1 has norm at most 1/(3 x^3 log x). Integrate the sharper exponential
majorant. This provides the trivial-zero error before logarithmic normalization. -/
theorem norm_integral_gammaShiftSum_le_of_two_le_re {x : ℝ} {κ : ℂ} (hx : 1 < x) (hκ : 2 ≤ κ.re) :
    ‖∫ σ : ℝ in Set.Ioi 1, gammaShiftSum x κ σ‖ ≤ 1 / (3 * x ^ 3 * Real.log x) := by
  have hb :
    ∀ᵐ σ : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi 1),
      ‖gammaShiftSum x κ σ‖ ≤ (x ^ (-2 : ℝ) / 3) * x ^ (-σ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with σ hσ
    have h := norm_gammaShiftSum_le_of_two_le_re hx hσ.le hκ
    rw [sub_eq_add_neg, Real.rpow_add (zero_lt_one.trans hx)] at h
    exact h.trans_eq (by ring)
  have h :=
    MeasureTheory.norm_integral_le_of_norm_le
      ((integrableOn_rpow_neg hx).const_mul (x ^ (-2 : ℝ) / 3)) hb
  rw [MeasureTheory.integral_const_mul, integral_rpow_neg hx] at h
  apply h.trans_eq
  rw [Real.rpow_neg (zero_lt_one.trans hx).le, Real.rpow_two, show x ^ 3 = x * x * x by ring,
    pow_two]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- For x > 1 and Re kappa >= 2, the integrated gamma residues divided by log x
have norm at most 1/(3 x^3 (log x)^2). Divide the integrated norm bound by the
positive logarithm. At kappa=2 this is the error constant in Lemma 2.6. -/
theorem norm_integrated_gammaShiftSum_div_log_le_of_two_le_re {x : ℝ} {κ : ℂ} (hx : 1 < x)
    (hκ : 2 ≤ κ.re) :
    ‖(∫ σ : ℝ in Set.Ioi 1, gammaShiftSum x κ σ) / (Real.log x : ℂ)‖ ≤
      1 / (3 * x ^ 3 * (Real.log x) ^ 2) := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.log_pos hx)]
  have h :=
    div_le_div_of_nonneg_right (norm_integral_gammaShiftSum_le_of_two_le_re hx hκ)
      (Real.log_pos hx).le
  exact
    h.trans_eq
      (by
        rw [div_div, pow_two]; ring)

end PseudoPrime.AnalyticNumberTheory.General
