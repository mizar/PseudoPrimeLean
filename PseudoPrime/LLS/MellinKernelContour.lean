/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelBounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.Boundary
public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.VerticalLimits
public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.LocalResidueAssembly

/-! # Contour shift and two-sided bounds for Mellin kernels

Quadratic decay gives absolute convergence on strip lines avoiding the pole.
Holomorphic regularization computes the residue across `-1/2`; quadratic
horizontal decay gives the inverse-Mellin contour shift. The resulting
two-sided transform bound controls the smoothed Mangoldt summands.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- On every strip line avoiding the possible pole, the kernel is absolutely
integrable. Holomorphy gives continuity; fixed distance from the pole and
quadratic decay give an inverse-square majorant. This supplies shifted lines. -/
theorem integrable_line_in_strip (K : MellinKernel) {c : ℝ} (hc : -1 / 2 - K.delta < c)
    (hc' : c ≤ 1 / 2 + K.delta) (hne : c ≠ -1 / 2) :
    MeasureTheory.Integrable (fun t : ℝ ↦ K.function ((c : ℂ) + Complex.I * t)) := by
  have hr (t : ℝ) : ((c : ℂ) + Complex.I * t).re = c := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hm (t : ℝ) : ((c : ℂ) + Complex.I * t).im = t := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_mul, zero_add]
  have hs (t : ℝ) : (c : ℂ) + Complex.I * t ∈ K.region \ {(-1 / 2 : ℂ)} := by
    refine
      ⟨K.strip_subset
          (by
            rw [Set.mem_ofPred_eq, hr]; exact ⟨hc, hc'⟩),
        ?_⟩
    intro hz
    apply hne
    have he := congrArg Complex.re (Set.mem_singleton_iff.mp hz)
    simpa only [hr, Complex.div_ofNat_re, Complex.neg_re, Complex.one_re] using he
  have hcont : Continuous (fun t : ℝ ↦ K.function ((c : ℂ) + Complex.I * t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have ht : ContinuousAt (fun y : ℝ ↦ (c : ℂ) + Complex.I * y) t :=
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousAt
    exact
      (K.holomorphic.differentiableAt
            ((K.region_open.sdiff isClosed_singleton).mem_nhds (hs t))).continuousAt.comp
        (f := fun y : ℝ ↦ (c : ℂ) + Complex.I * y) ht
  have hη : 0 < |c + 1 / 2| :=
    abs_pos.mpr
      (by
        intro he
        apply hne
        linarith only [he])
  obtain ⟨C, hC, hb⟩ := K.decay |c + 1 / 2| hη
  apply (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
  exact
    Filter.Eventually.of_forall
      (fun t ↦ by
        have hd : |c + 1 / 2| ≤ ‖(c : ℂ) + Complex.I * t + 1 / 2‖ := by
          have h := Complex.abs_re_le_norm ((c : ℂ) + Complex.I * t + 1 / 2)
          simpa only [Complex.add_re, hr, Complex.div_ofNat_re, Complex.one_re] using h
        have ht := Complex.abs_im_le_norm ((c : ℂ) + Complex.I * t)
        rw [hm] at ht
        have hsq := mul_self_le_mul_self (abs_nonneg t) ht
        rw [← pow_two, ← pow_two, sq_abs] at hsq
        have hn := hb _ (hs t).1 hd
        have hden : 1 + t ^ 2 ≤ 1 + ‖(c : ℂ) + Complex.I * t‖ ^ 2 := by nlinarith only [hsq]
        simpa only [div_eq_mul_inv] using
          hn.trans (div_le_div_of_nonneg_left hC.le (by positivity : 0 < 1 + t ^ 2) hden))

/-- For a positive argument, the inverse-Mellin integrand is absolutely
integrable on every strip line avoiding the pole. Its power factor has constant
norm on the line. This extends integrability to the left side of the pole. -/
theorem integrable_inverse_in_strip (K : MellinKernel) {c u : ℝ} (hc : -1 / 2 - K.delta < c)
    (hc' : c ≤ 1 / 2 + K.delta) (hne : c ≠ -1 / 2) (hu : 0 < u) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        K.function ((c : ℂ) + Complex.I * t) * (u : ℂ) ^ (-((c : ℂ) + Complex.I * t))) := by
  have hp : Continuous (fun t : ℝ ↦ (u : ℂ) ^ (-((c : ℂ) + Complex.I * t))) :=
    (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hu.ne'))
  apply (integrable_line_in_strip K hc hc' hne).mul_bdd (c := u ^ (-c)) hp.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t ↦ (norm_mellin_power (t := t) hu).le)

/-- For a positive argument, any rectangle contained in the kernel region
and enclosing the possible pole has inverse-Mellin boundary integral
2*pi*i times K.regularized(-1/2) times u^(1/2). The regularized integrand is
analytic near the pole; the local simple-pole certificate and singleton
residue assembly evaluate the boundary integral. This supplies finite
contours across the pole without an external contour library. -/
theorem inverse_mellin_rectangle (K : MellinKernel) {u : ℝ} (hu : 0 < u) {z w : ℂ}
    (hz : z.re ≤ w.re) (hw : z.im ≤ w.im) (hsub : Complex.Rectangle z w ⊆ K.region)
    (hp : Complex.Rectangle z w ∈ nhds (-1 / 2 : ℂ)) :
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
        (fun s : ℂ ↦ K.function s * (u : ℂ) ^ (-s)) z w =
      2 * Real.pi * Complex.I * (K.regularized (-1 / 2) * (u : ℂ) ^ (1 / 2 : ℂ)) := by
  let f : ℂ → ℂ := fun s ↦ K.function s * (u : ℂ) ^ (-s)
  let h : ℂ → ℂ := fun s ↦ K.regularized s * (u : ℂ) ^ (-s)
  have hc : (-1 / 2 : ℂ) ∈ K.region := hsub (mem_of_mem_nhds hp)
  have hd : Differentiable ℂ (fun s : ℂ ↦ (u : ℂ) ^ (-s)) :=
    differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hu.ne'))
  have ha : AnalyticAt ℂ h (-1 / 2) :=
    ((K.regularized_holomorphic.analyticOnNhd K.region_open) _ hc).mul (hd.analyticAt _)
  have ho' : (-1 / 2 : ℂ) ∈ Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im := by
    have hi := mem_interior_iff_mem_nhds.mpr hp
    simpa only [Complex.Rectangle, Complex.interior_reProdIm, Set.uIcc_of_le hz, Set.uIcc_of_le hw,
      interior_Icc] using hi
  have ho : (-1 / 2 : ℂ) ∈ AnalyticNumberTheory.RectangleGeometry.rectangleOpenBox z w := by
    simpa only [AnalyticNumberTheory.RectangleGeometry.rectangleOpenBox, min_eq_left hz,
      max_eq_right hz, min_eq_left hw, max_eq_right hw] using ho'
  have heq :
    Filter.EventuallyEq (nhdsWithin (-1 / 2 : ℂ) {(-1 / 2 : ℂ)}ᶜ) (fun s ↦ (s - (-1 / 2)) * f s)
      h := by
    have hr :=
      Filter.Eventually.filter_mono (nhdsWithin_le_nhds (s := {(-1 / 2 : ℂ)}ᶜ))
        (K.region_open.mem_nhds hc)
    filter_upwards [hr, self_mem_nhdsWithin] with s hs hn
    have hn' : s ≠ (-1 / 2 : ℂ) := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hn
    dsimp only [f, h]
    rw [show s - (-1 / 2 : ℂ) = s + 1 / 2 by ring, K.regularized_eq s hs hn']
    ring
  have hdiff :
    ∀ p ∈ AnalyticNumberTheory.Rectangle.rectangleClosedBox z w,
      p ≠ (-1 / 2 : ℂ) → DifferentiableAt ℂ f p := by
    intro p hp' hn
    exact
      (K.holomorphic.differentiableAt
            ((K.region_open.sdiff isClosed_singleton).mem_nhds
              ⟨hsub hp', by simpa only [Set.mem_singleton_iff] using hn⟩)).mul
        (hd p)
  have hb :=
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral_eq_of_simple_regularization
      (ho'.1.1.trans ho'.1.2) (ho'.2.1.trans ho'.2.2) ho hdiff ha heq
  simpa only [h, show -(-1 / 2 : ℂ) = (1 / 2 : ℂ) by ring] using hb

/-- Uniform quadratic decay of the inverse-Mellin integrand on a bounded
horizontal strip, away from the pole. Bound its power factor independently
of the height; this controls the two horizontal sides of expanding contours. -/
private theorem inverse_horizontal_bound (K : MellinKernel) {c u : ℝ} (hc : -1 / 2 - K.delta < c)
    (hc0 : c ≤ 0) (hu : 0 < u) :
    ∃ D : ℝ,
      0 < D ∧
        ∀ (x t : ℝ),
          x ∈ Set.uIoc c 0 →
            1 ≤ |t| →
            ‖K.function ((x : ℂ) + t * Complex.I) * (u : ℂ) ^ (-((x : ℂ) + t * Complex.I))‖ ≤
              D / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := K.decay 1 (by norm_num only)
  refine ⟨C * Real.exp (|Real.log u| * (-c)), mul_pos hC (Real.exp_pos _), ?_⟩
  intro x t hx ht
  have hx' : c < x ∧ x ≤ 0 := by simpa only [Set.uIoc_of_le hc0, Set.mem_Ioc] using hx
  have hr : ((x : ℂ) + t * Complex.I).re = x := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hm : ((x : ℂ) + t * Complex.I).im = t := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
  have hs : (x : ℂ) + t * Complex.I ∈ K.region :=
    K.strip_subset
      (by
        rw [Set.mem_ofPred_eq, hr]
        exact ⟨hc.trans hx'.1, hx'.2.trans (by linarith only [K.delta_pos])⟩)
  have hd : 1 ≤ ‖(x : ℂ) + t * Complex.I + 1 / 2‖ :=
    ht.trans
      (by
        simpa only [Complex.add_im, hm, Complex.div_ofNat_im, Complex.one_im, zero_div,
          add_zero] using Complex.abs_im_le_norm ((x : ℂ) + t * Complex.I + 1 / 2))
  have hi := Complex.abs_im_le_norm ((x : ℂ) + t * Complex.I)
  rw [hm] at hi
  have hsq := mul_self_le_mul_self (abs_nonneg t) hi
  rw [← pow_two, ← pow_two, sq_abs] at hsq
  have hk :=
    (hb _ hs hd).trans
      (div_le_div_of_nonneg_left hC.le (by positivity : 0 < 1 + t ^ 2)
        (by linarith only [hsq] : 1 + t ^ 2 ≤ 1 + ‖(x : ℂ) + t * Complex.I‖ ^ 2))
  have hp : ‖(u : ℂ) ^ (-((x : ℂ) + t * Complex.I))‖ ≤ Real.exp (|Real.log u| * (-c)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.neg_re, hr, Real.rpow_def_of_pos hu]
    apply Real.exp_le_exp.mpr
    have hl := le_abs_self (Real.log u * (-x))
    rw [abs_mul, abs_neg, abs_of_nonpos hx'.2] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left (neg_le_neg hx'.1.le) (abs_nonneg _))
  rw [norm_mul]
  calc
    _ ≤ C / (1 + t ^ 2) * Real.exp (|Real.log u| * (-c)) :=
      mul_le_mul hk hp (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- A uniform quadratic height bound forces the horizontal integrals at
heights `±(n+1)` to tend to zero. The integral norm is bounded by the interval
length times `D/(n+1)`, which tends to zero. -/
private theorem horizontal_limit_of_decay {f : ℂ → ℂ} {c D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ (x t : ℝ), x ∈ Set.uIoc c 0 → 1 ≤ |t| → ‖f ((x : ℂ) + t * Complex.I)‖ ≤ D / (1 + t ^ 2))
    (e : ℝ) (he : e = 1 ∨ e = -1) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ x in c..0, f ((x : ℂ) + ((e * ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun n : ℕ ↦ D / ((n : ℝ) + 1) * |0 - c|)
  · intro n
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have ht : 1 ≤ |e * ((n : ℝ) + 1)| := by
      rcases he with rfl | rfl
      · rw [one_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
        exact le_add_of_nonneg_left (Nat.cast_nonneg n)
      · rw [neg_one_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
        exact le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hn : (n : ℝ) + 1 ≤ 1 + (e * ((n : ℝ) + 1)) ^ 2 := by
      rcases he with rfl | rfl
      · rw [one_mul]
        nlinarith only [Nat.cast_nonneg (α := ℝ) n]
      · rw [neg_one_mul, neg_sq]
        nlinarith only [Nat.cast_nonneg (α := ℝ) n]
    exact (hb x _ hx ht).trans (div_le_div_of_nonneg_left hD (by positivity : 0 < (n : ℝ) + 1) hn)
  · have hl : Filter.Tendsto (fun n : ℕ ↦ D / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, one_mul, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul D
    simpa only [zero_mul] using hl.mul_const |0 - c|

/-- For a line left of the pole and positive height, the rectangle joining
that line to the imaginary axis encloses the pole and stays in the kernel
region. Apply the finite residue formula to this expanding contour. -/
private theorem inverse_boundary_shift (K : MellinKernel) {c u T : ℝ} (hc : -1 / 2 - K.delta < c)
    (hc' : c < -1 / 2) (hu : 0 < u) (hT : 0 < T) :
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
        (fun s : ℂ ↦ K.function s * (u : ℂ) ^ (-s)) ((c : ℂ) - T * Complex.I)
        ((0 : ℂ) + T * Complex.I) =
      2 * Real.pi * Complex.I * (K.regularized (-1 / 2) * (u : ℂ) ^ (1 / 2 : ℂ)) := by
  have hc0 : c < 0 := lt_trans hc' (by norm_num only)
  have hre : ((c : ℂ) - T * Complex.I).re = c := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero]
  have hrez : ((0 : ℂ) + T * Complex.I).re = 0 := by
    simp only [zero_add, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero]
  have him : ((c : ℂ) - T * Complex.I).im = -T := by
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, add_zero, zero_sub]
  have himz : ((0 : ℂ) + T * Complex.I).im = T := by
    simp only [zero_add, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, zero_mul, add_zero]
  apply
    inverse_mellin_rectangle K hu
      (by
        rw [hre, hrez]; exact hc0.le)
      (by
        rw [him, himz]; linarith only [hT])
  · intro s hs
    have hs' : c ≤ s.re ∧ s.re ≤ 0 := by
      simpa only [Complex.Rectangle, hre, hrez, Set.uIcc_of_le hc0.le, Set.mem_preimage,
        Set.mem_Icc] using hs.1
    apply K.strip_subset
    exact ⟨hc.trans_le hs'.1, hs'.2.trans (by linarith only [K.delta_pos])⟩
  · change AnalyticNumberTheory.Rectangle.rectangleClosedBox _ _ ∈ nhds _
    rw [AnalyticNumberTheory.Rectangle.rectangleClosedBox_mem_nhds_iff]
    change (-1 / 2 : ℂ).re ∈ Set.uIoo _ _ ∧ (-1 / 2 : ℂ).im ∈ Set.uIoo _ _
    rw [hre, hrez, him, himz, Set.uIoo_of_lt hc0, Set.uIoo_of_lt (by linarith only [hT] : -T < T)]
    simp only [Set.mem_Ioo, Complex.div_ofNat_re, Complex.neg_re, Complex.one_re,
      Complex.div_ofNat_im, Complex.neg_im, Complex.one_im, zero_div, neg_zero]
    exact ⟨⟨hc', by norm_num only⟩, ⟨by linarith only [hT], hT⟩⟩

/-- For a positive argument and a line left of the pole, the difference of
vertical inverse-Mellin integrals is `2πi` times the pole contribution.
Quadratic decay removes both horizontal sides; integrability identifies the
remaining limits. This is the unnormalized contour-shift identity. -/
private theorem inverse_line_residue (K : MellinKernel) {c u : ℝ} (hc : -1 / 2 - K.delta < c)
    (hc' : c < -1 / 2) (hu : 0 < u) :
    Complex.I *
        ((∫ t : ℝ, K.function ((0 : ℂ) + t * Complex.I) * (u : ℂ) ^ (-((0 : ℂ) + t * Complex.I))) -
          ∫ t : ℝ, K.function ((c : ℂ) + t * Complex.I) * (u : ℂ) ^ (-((c : ℂ) + t * Complex.I))) =
      2 * Real.pi * Complex.I * (K.regularized (-1 / 2) * (u : ℂ) ^ (1 / 2 : ℂ)) := by
  obtain ⟨D, hD, hb⟩ := inverse_horizontal_bound K hc (lt_trans hc' (by norm_num only)).le hu
  have ht :=
    horizontal_limit_of_decay (f := fun s : ℂ ↦ K.function s * (u : ℂ) ^ (-s)) (c := c) hD.le hb 1
      (Or.inl rfl)
  have hbottom :=
    horizontal_limit_of_decay (f := fun s : ℂ ↦ K.function s * (u : ℂ) ^ (-s)) (c := c) hD.le hb
      (-1) (Or.inr rfl)
  have hl :=
    integrable_inverse_in_strip K hc (by linarith only [hc', K.delta_pos]) (ne_of_lt hc') hu
  have hr :=
    integrable_inverse_in_strip K (by linarith only [K.delta_pos] : -1 / 2 - K.delta < (0 : ℝ))
      (by linarith only [K.delta_pos] : (0 : ℝ) ≤ 1 / 2 + K.delta)
      (by norm_num only : (0 : ℝ) ≠ -1 / 2) hu
  have hlim :=
    AnalyticNumberTheory.RectangleGeometry.tendsto_rectangleBoundaryIntegral_of_horizontal_limits
      (K := fun s : ℂ ↦ K.function s * (u : ℂ) ^ (-s)) (a := c) (b := 0) (fun n : ℕ ↦ (n : ℝ) + 1)
      (Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop)
      (by
        simpa only [neg_one_mul, one_mul, Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using
          hbottom)
      (by simpa only [one_mul] using ht) (by simpa only [mul_comm] using hl)
      (by simpa only [mul_comm] using hr)
  apply tendsto_nhds_unique hlim
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  exact
    Filter.Eventually.of_forall
      (fun n ↦ (inverse_boundary_shift K hc hc' hu (by positivity : 0 < (n : ℝ) + 1)).symm)

/-- For a positive argument, shifting the inverse-Mellin integral to a line
left of `-1/2` adds `K.regularized(-1/2) u^(1/2)`. Divide the vertical residue
identity by `2πi`. This gives the small-argument decay estimate for the transform. -/
theorem inverse_mellin_left_of_pole (K : MellinKernel) {c u : ℝ} (hc : -1 / 2 - K.delta < c)
    (hc' : c < -1 / 2) (hu : 0 < u) :
    inverseMellin K.function 0 u =
      inverseMellin K.function c u + K.regularized (-1 / 2) * (u : ℂ) ^ (1 / 2 : ℂ) := by
  have h := inverse_line_residue K hc hc' hu
  have hd :
    (∫ t : ℝ, K.function ((0 : ℂ) + t * Complex.I) * (u : ℂ) ^ (-((0 : ℂ) + t * Complex.I))) -
        (∫ t : ℝ, K.function ((c : ℂ) + t * Complex.I) * (u : ℂ) ^ (-((c : ℂ) + t * Complex.I))) =
      (2 * Real.pi : ℂ) * (K.regularized (-1 / 2) * (u : ℂ) ^ (1 / 2 : ℂ)) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    calc
      _ = _ := h
      _ = _ := by ring
  have hs := congrArg (fun z : ℂ ↦ (↑(1 / (2 * Real.pi) : ℝ) : ℂ) * z) hd
  simp only [one_div, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_sub] at hs
  have hn : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num only) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul] at hs
  unfold inverseMellin
  simpa only [one_div, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_zero, mul_comm, add_comm, sub_eq_iff_eq_add] using hs

/-- For a positive argument, the norm of any inverse-Mellin line integral
is bounded by its kernel norm integral times `u^(-c)/(2π)`. Use the integral
triangle inequality and the constant norm of the power factor on that line. -/
theorem norm_inverse_mellin_le_line (K : MellinKernel) {c u : ℝ} (hu : 0 < u) :
    ‖inverseMellin K.function c u‖ ≤
      (1 / (2 * Real.pi)) * (∫ t : ℝ, ‖K.function ((c : ℂ) + Complex.I * t)‖) * u ^ (-c) := by
  rw [inverseMellin, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi))]
  calc
    _ ≤
        (1 / (2 * Real.pi)) *
          ∫ t : ℝ,
            ‖K.function ((c : ℂ) + Complex.I * t) * (u : ℂ) ^ (-((c : ℂ) + Complex.I * t))‖ :=
      mul_le_mul_of_nonneg_left (MeasureTheory.norm_integral_le_integral_norm _) (by positivity)
    _ = _ := by
      simp only [norm_mul, norm_mellin_power hu, MeasureTheory.integral_mul_const, mul_assoc]

/-- For every admissible kernel, its transform is bounded by `C sqrt(u)` on
`0 < u ≤ 1`. Shift to `c=-1/2-delta/2`; bound the remaining line integral
and the pole contribution separately. This is the small-argument part of (6.1). -/
theorem exists_norm_transform_le_sqrt (K : MellinKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → u ≤ 1 → ‖K.transform u‖ ≤ C * Real.sqrt u := by
  let c : ℝ := -1 / 2 - K.delta / 2
  let A : ℝ := (1 / (2 * Real.pi)) * (∫ t : ℝ, ‖K.function ((c : ℂ) + Complex.I * t)‖)
  have hc : -1 / 2 - K.delta < c := by
    dsimp only [c]; linarith only [K.delta_pos]
  have hc' : c < -1 / 2 := by
    dsimp only [c]; linarith only [K.delta_pos]
  refine ⟨|A| + ‖K.regularized (-1 / 2)‖ + 1, by positivity, ?_⟩
  intro u hu hu1
  rw [transform, inverse_mellin_left_of_pole K hc hc' hu]
  have hb := norm_inverse_mellin_le_line K (c := c) hu
  have hp : u ^ (-c) ≤ Real.sqrt u := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hu hu1 (by linarith only [hc'])
  have hA : 0 ≤ A :=
    mul_nonneg (by positivity) (MeasureTheory.integral_nonneg (fun t ↦ norm_nonneg _))
  have hr : ‖(u : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt u := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu, Real.sqrt_eq_rpow]
    simp only [Complex.div_ofNat_re, Complex.one_re]
  calc
    _ ≤ ‖inverseMellin K.function c u‖ + ‖K.regularized (-1 / 2) * (u : ℂ) ^ (1 / 2 : ℂ)‖ :=
      norm_add_le _ _
    _ ≤ A * Real.sqrt u + ‖K.regularized (-1 / 2)‖ * Real.sqrt u := by
      rw [norm_mul, hr]
      exact add_le_add (hb.trans (mul_le_mul_of_nonneg_left hp hA)) (le_refl _)
    _ ≤ _ := by nlinarith only [le_abs_self A, Real.sqrt_nonneg u]

/-- The transform of every admissible kernel satisfies the two-sided bound
`C min(sqrt(u), 1/sqrt(u))` for positive `u`, as in (6.1). Combine the left
contour shift with the line `c=1/2`; this controls primitive-character corrections. -/
theorem exists_norm_transform_le_min (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧ ∀ u : ℝ, 0 < u → ‖K.transform u‖ ≤ C * min (Real.sqrt u) (1 / Real.sqrt u) := by
  obtain ⟨A, hA, hsmall⟩ := exists_norm_transform_le_sqrt K
  let B : ℝ := (1 / (2 * Real.pi)) * (∫ t : ℝ, ‖K.function (((1 / 2 : ℝ) : ℂ) + Complex.I * t)‖)
  refine ⟨max A |B|, lt_of_lt_of_le hA (le_max_left _ _), ?_⟩
  intro u hu
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hlarge : ‖K.transform u‖ ≤ |B| * (1 / Real.sqrt u) := by
    have hb :=
      norm_transform_le_line K (c := 1 / 2) (by norm_num only) (by linarith only [K.delta_pos]) hu
    rw [Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow] at hb
    simpa only [one_div] using
      hb.trans (mul_le_mul_of_nonneg_right (le_abs_self B) (inv_nonneg.mpr (Real.sqrt_nonneg u)))
  by_cases hu1 : u ≤ 1
  · have hs1 : Real.sqrt u ≤ 1 := (Real.sqrt_le_sqrt hu1).trans_eq Real.sqrt_one
    have hmin : min (Real.sqrt u) (1 / Real.sqrt u) = Real.sqrt u :=
      min_eq_left ((le_div_iff₀ hs).mpr (by nlinarith only [hs1, hs.le]))
    rw [hmin]
    exact (hsmall u hu hu1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hs.le)
  · have hs1 : 1 ≤ Real.sqrt u := Real.sqrt_one ▸ Real.sqrt_le_sqrt (le_of_not_ge hu1)
    have hmin : min (Real.sqrt u) (1 / Real.sqrt u) = 1 / Real.sqrt u :=
      min_eq_right ((div_le_iff₀ hs).mpr (by nlinarith only [hs1]))
    rw [hmin]
    exact hlarge.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- A two-sided transform majorant bounds each nonzero smoothed Mangoldt
summand by the corresponding positive profile weight. The character norm is
at most one. This estimate supplies prime-power and conductor-error majorants. -/
theorem norm_summand_le_min_of_transform_bound (K : MellinKernel) {C : ℝ}
    (hb : ∀ u : ℝ, 0 < u → ‖K.transform u‖ ≤ C * min (Real.sqrt u) (1 / Real.sqrt u)) {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    ‖K.summand χ x n‖ ≤
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (C * min (Real.sqrt ((n : ℝ) / x)) (1 / Real.sqrt ((n : ℝ) / x))) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hv : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hu := hb ((n : ℝ) / x) (div_pos hnpos hx)
  have hχ := χ.norm_le_one n
  rw [summand, ite_eq_right hn, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hv hsn.le)]
  have hw :
    (ArithmeticFunction.vonMangoldt n / Real.sqrt n * ‖χ n‖) ≤
      ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hχ (div_nonneg hv hsn.le)
  calc
    _ ≤
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (C * min (Real.sqrt ((n : ℝ) / x)) (1 / Real.sqrt ((n : ℝ) / x))) :=
      mul_le_mul hw hu (norm_nonneg _) (div_nonneg hv hsn.le)

/-- Every admissible kernel admits one positive profile constant valid for
all characters, positive cutoffs, and nonzero indices. Apply (6.1) and the
pointwise character estimate; no GRH assumption is needed. -/
theorem exists_norm_summand_le_min (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ},
          0 < x →
            ∀ {n : ℕ},
              n ≠ 0 →
                ‖K.summand χ x n‖ ≤
                  (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
                    (C * min (Real.sqrt ((n : ℝ) / x)) (1 / Real.sqrt ((n : ℝ) / x))) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_transform_le_min K
  refine ⟨C, hC, ?_⟩
  intro q _ χ x hx n hn
  exact norm_summand_le_min_of_transform_bound K hb χ hx hn

end PseudoPrime.LLS.PaperStatements.MellinKernel
