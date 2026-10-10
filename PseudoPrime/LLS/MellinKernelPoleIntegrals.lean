/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelHorizontal
public import PseudoPrime.LLS.MellinKernelVerticalIntegrability
public import PseudoPrime.LLS.MellinKernelFiniteContour
public import PseudoPrime.LLS.MellinKernelZeros
public import PseudoPrime.LLS.MellinKernelContourGeometry

/-! # Elementary pole integrals for general Mellin kernels

Quadratic kernel decay removes horizontal edges of real-pole contours.
Central vertical integrals are bounded uniformly in the positive Mellin scale.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- For any real pole location and a fixed interval in the kernel strip, both
signed horizontal pole integrals tend to zero at heights `n+1`, for `x ≥ 1`.
The pole factor has norm at most one there, and quadratic kernel decay gives
a vanishing inverse-square majorant. This supports moving elementary pole contours. -/
theorem tendsto_pole_horizontalIntegral (K : MellinKernel) {a b x : ℝ} (hab : a ≤ b)
    (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta) (hx : 1 ≤ x) (p e : ℝ)
    (he : e = 1 ∨ e = -1) :
    let T := fun n : ℕ => (n : ℝ) + 1
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ σ in a..b,
          (1 / (((σ : ℂ) + ((e * T n : ℝ) : ℂ) * Complex.I) - (p : ℂ))) *
            K.function ((σ : ℂ) + ((e * T n : ℝ) : ℂ) * Complex.I) *
            (x : ℂ) ^ ((σ : ℂ) + ((e * T n : ℝ) : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  let T := fun n : ℕ => (n : ℝ) + 1
  have ht (n : ℕ) : 1 ≤ T n := by
    dsimp only [T]
    linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hpos (n : ℕ) : 0 < T n := zero_lt_one.trans_le (ht n)
  have hsign (n : ℕ) : |e * T n| = T n := by
    rcases he with rfl | rfl
    · rw [one_mul, abs_of_pos (hpos n)]
    · rw [neg_one_mul, abs_neg, abs_of_pos (hpos n)]
  apply
    tendsto_horizontalIntegral_of_scaled_bound K hab ha hb hx (fun n => e * T n)
      (fun n => (T n)⁻¹ ^ 2) (F := fun s : ℂ => 1 / (s - (p : ℂ)))
  · intro n
    rw [hsign]
    exact ht n
  · intro n
    exact sq_nonneg _
  · have hT : Filter.Tendsto T Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hi : Filter.Tendsto (fun n => (T n)⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp hT
    simpa only [Function.comp_apply, zero_pow (by norm_num only : (2 : ℕ) ≠ 0)] using hi.pow 2
  · intro n σ _
    have hden := Complex.abs_im_le_norm (((σ : ℂ) + ((e * T n : ℝ) : ℂ) * Complex.I) - (p : ℂ))
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add, sub_zero, hsign] at hden
    have hn := inv_le_one_of_one_le₀ ((ht n).trans hden)
    have hsq : (e * T n) ^ 2 = (T n) ^ 2 := by
      rcases he with rfl | rfl
      · rw [one_mul]
      · rw [neg_one_mul, neg_sq]
    rw [one_div, norm_inv, hsq, ← mul_pow, inv_mul_cancel₀ (hpos n).ne', one_pow]
    exact hn

/-- At every nonzero real pole location, a positive constant bounds the normalized
central-line pole integral for all positive scales. The Mellin phase has unit norm;
the real-part distance bounds the pole factor. Integrate against the absolutely
integrable kernel norm. This gives the residual term after a pole contour shift. -/
theorem exists_norm_central_poleIntegral_le (K : MellinKernel) {p : ℝ} (hp : p ≠ 0) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {x : ℝ},
          0 < x →
            ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ,
                    (1 / (Complex.I * t - (p : ℂ))) *
                      (K.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))‖ ≤
              C := by
  have hc : -1 / 2 - K.delta < (0 : ℝ) := by linarith only [K.delta_pos]
  have hc' : (0 : ℝ) ≤ 1 / 2 + K.delta := by linarith only [K.delta_pos]
  have hn : (0 : ℝ) ≠ -1 / 2 := by norm_num only
  have hiK := integrable_line_in_strip K hc hc' hn
  let D := (1 / |p|) * (∫ t : ℝ, ‖K.function (Complex.I * t)‖)
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  refine ⟨1 + ‖d‖ * max D 0, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (norm_nonneg _) (le_max_right _ _))
  · intro x hx
    let F := fun t : ℝ =>
      (1 / (Complex.I * t - (p : ℂ))) * (K.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))
    have hiF : MeasureTheory.Integrable F := by
      simpa only [F, Complex.ofReal_zero, zero_add, mul_assoc] using
        integrable_pole_power_line K hc hc' hn (Ne.symm hp) hx
    have hb (t : ℝ) : ‖F t‖ ≤ (1 / |p|) * ‖K.function (Complex.I * t)‖ := by
      have hden := Complex.abs_re_le_norm (Complex.I * t - (p : ℂ))
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_sub, abs_neg] at hden
      have hi := one_div_le_one_div_of_le (abs_pos.mpr hp) hden
      dsimp only [F]
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]
      rw [one_div, norm_inv, ← one_div]
      exact mul_le_mul_of_nonneg_right hi (norm_nonneg _)
    have hiH :
      MeasureTheory.Integrable (fun t : ℝ => (1 / |p|) * ‖K.function (Complex.I * t)‖) := by
      simpa only [Complex.ofReal_zero, zero_add] using hiK.norm.const_mul (1 / |p|)
    have hi :=
      (MeasureTheory.norm_integral_le_integral_norm F).trans
        (MeasureTheory.integral_mono hiF.norm hiH hb)
    rw [MeasureTheory.integral_const_mul] at hi
    change ‖∫ t : ℝ, F t‖ ≤ D at hi
    change ‖d * ∫ t : ℝ, F t‖ ≤ _
    rw [norm_mul]
    exact
      (mul_le_mul_of_nonneg_left (hi.trans (le_max_left D 0)) (norm_nonneg d)).trans
        (le_add_of_nonneg_left zero_le_one)

/-- For a negative real pole, the right vertical pole integral at `x ≥ 1` equals
its central-line integral. The pole and kernel pole lie outside the intervening
nonnegative strip, so Cauchy's theorem gives zero finite boundaries. The horizontal
limits and proved vertical integrability give line independence.
This reduces the pole at `-1/2` in the xi completion to a bounded central error. -/
theorem poleIntegral_eq_central_of_neg (K : MellinKernel) {p b x : ℝ} (hp : p < 0) (hb : 0 ≤ b)
    (hbK : b ≤ 1 / 2 + K.delta) (hx : 1 ≤ x) :
    (∫ t : ℝ,
        (1 / ((((b : ℂ) + Complex.I * t)) - (p : ℂ))) *
          (K.function ((b : ℂ) + Complex.I * t) * (x : ℂ) ^ ((b : ℂ) + Complex.I * t))) =
      (∫ t : ℝ,
        (1 / (Complex.I * t - (p : ℂ))) *
          (K.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))) := by
  let F := fun s : ℂ => (1 / (s - (p : ℂ))) * K.function s * (x : ℂ) ^ s
  let T := fun n : ℕ => (n : ℝ) + 1
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hb' : b ≠ -1 / 2 := by linarith only [hb]
  have hl0 : -1 / 2 - K.delta < (0 : ℝ) := by linarith only [K.delta_pos]
  have hlb : -1 / 2 - K.delta < b := hl0.trans_le hb
  have h0 : (0 : ℝ) ≤ 1 / 2 + K.delta := hb.trans hbK
  have hi0 :=
    integrable_pole_power_line K hl0 h0 (by norm_num only : (0 : ℝ) ≠ -1 / 2) (ne_of_gt hp) hxpos
  have hib := integrable_pole_power_line K hlb hbK hb' (ne_of_gt (hp.trans_le hb)) hxpos
  have htop := tendsto_pole_horizontalIntegral K hb hl0 hbK hx p 1 (Or.inl rfl)
  have hbot := tendsto_pole_horizontalIntegral K hb hl0 hbK hx p (-1) (Or.inr rfl)
  have ht :=
    AnalyticNumberTheory.RectangleGeometry.tendsto_rectangleBoundaryIntegral_of_horizontal_limits
      (K := F) (a := 0) (b := b) T
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      (by
        simpa only [F, T, neg_one_mul, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, one_mul] using
          hbot)
      (by simpa only [F, T, one_mul] using htop) (by simpa only [F, mul_comm, mul_assoc] using hi0)
      (by simpa only [F, mul_comm, mul_assoc] using hib)
  have hz (n : ℕ) :
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral F ((0 : ℂ) - T n * Complex.I)
        ((b : ℂ) + T n * Complex.I) =
      0 := by
    apply
      AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    intro s hs
    have hsr : 0 ≤ s.re ∧ s.re ≤ b := by
      have hs' := hs.1
      change s.re ∈ Set.uIcc _ _ at hs'
      simpa only [Complex.sub_re, Complex.add_re, Complex.zero_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
        add_zero, Set.uIcc_of_le hb, Set.mem_Icc] using hs'
    have hreg : s ∈ K.region :=
      K.strip_subset ⟨by linarith only [hsr.1, K.delta_pos], hsr.2.trans hbK⟩
    have hsp : s ≠ -1 / 2 := by
      intro he
      have hre := congrArg Complex.re he
      norm_num only [Complex.neg_re, Complex.div_ofNat_re, Complex.one_re] at hre
      linarith only [hsr.1, hre]
    have hk :=
      K.holomorphic.differentiableAt ((K.region_open.sdiff isClosed_singleton).mem_nhds ⟨hreg, hsp⟩)
    have hden : s - (p : ℂ) ≠ 0 := by
      intro he
      have hre := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
      linarith only [hre, hsr.1, hp]
    have hf :=
      ((differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const (p : ℂ)) hden).mul
          hk |>.mul
        ((differentiable_id.const_cpow
            (Or.inl (Complex.ofReal_ne_zero.mpr hxpos.ne'))).differentiableAt)
    exact hf.differentiableWithinAt
  have he := tendsto_nhds_unique ht (tendsto_const_nhds.congr (fun n => (hz n).symm))
  have hi := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left Complex.I_ne_zero)
  simpa only [F, Complex.ofReal_zero, zero_add, mul_comm, mul_assoc, mul_left_comm] using hi

open AnalyticNumberTheory in
/-- A rectangle from real part zero to `b`, with positive height, contains exactly
one real pole at `0 < p < b`. Its weighted negative pole boundary integral is
minus `2πi K(p)x^p`. Apply the finite logarithmic residue theorem to `F(s)=s-p`;
the kernel pole lies outside the rectangle and the linear zero has multiplicity one. -/
theorem neg_pole_rectangleBoundaryIntegral_eq (K : MellinKernel) {p b T x : ℝ} (hp : 0 < p)
    (hpb : p < b) (hbK : b ≤ 1 / 2 + K.delta) (hT : 0 < T) (hx : 0 < x) :
    RectangleGeometry.rectangleBoundaryIntegral
        (fun s : ℂ => -(1 / (s - (p : ℂ))) * (K.function s * (x : ℂ) ^ s)) (-(T : ℂ) * Complex.I)
        ((b : ℂ) + T * Complex.I) =
      -(2 * Real.pi * Complex.I * (K.function (p : ℂ) * (x : ℂ) ^ (p : ℂ))) := by
  have hb : 0 < b := hp.trans hpb
  let z : ℂ := -(T : ℂ) * Complex.I
  let w : ℂ := (b : ℂ) + T * Complex.I
  have hzre : z.re = 0 := by
    simp only [z, neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, neg_zero]
  have hwre : w.re = b := by
    simp only [w, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hzim : z.im = -T := by
    simp only [z, neg_mul, Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  have hwim : w.im = T := by
    simp only [w, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  have hc : (p : ℂ) ∈ Rectangle.rectangleClosedBox z w := by
    change (p : ℂ).re ∈ Set.uIcc z.re w.re ∧ (p : ℂ).im ∈ Set.uIcc z.im w.im
    rw [hzre, hwre, hzim, hwim, Complex.ofReal_re, Complex.ofReal_im, Set.uIcc_of_le hb.le,
      Set.uIcc_of_le (neg_le_self hT.le)]
    exact ⟨⟨hp.le, hpb.le⟩, ⟨by linarith only [hT], hT.le⟩⟩
  have ho : (p : ℂ) ∈ RectangleGeometry.rectangleOpenBox z w := by
    apply
      RectangleGeometry.mem_rectangleOpenBox_of_mem_closedBox_of_ne
        (by
          rw [hzre, hwre]; exact hb)
        (by
          rw [hzim, hwim]; exact neg_lt_self hT)
        hc
    · rw [Complex.ofReal_re, hzre]
      exact hp.ne'
    · rw [Complex.ofReal_re, hwre]
      exact hpb.ne
    · rw [Complex.ofReal_im, hzim]
      linarith only [hT]
    · rw [Complex.ofReal_im, hwim]
      exact hT.ne
  have hreg : Rectangle.rectangleClosedBox z w ⊆ K.region := by
    simpa only [z, w, Complex.ofReal_zero, zero_sub, neg_mul] using
      closed_goodHeight_box_subset_region K hb.le (by linarith only [K.delta_pos]) hbK (T := T)
  have hF : AnalyticOnNhd ℂ (fun s : ℂ => s - (p : ℂ)) K.region := fun s _ =>
    analyticAt_id.sub analyticAt_const
  have hFp : (-1 / 2 : ℂ) - (p : ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num only [Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.ofReal_re, Complex.zero_re] at hr
    linarith only [hr, hp]
  have hcover :
    ∀ s ∈ Rectangle.rectangleClosedBox z w,
      s = -1 / 2 ∨ s - (p : ℂ) = 0 → s ∈ ({(p : ℂ)} : Finset ℂ) := by
    intro s hs hsing
    rcases hsing with he | he
    · have hr := hs.1
      change s.re ∈ Set.uIcc z.re w.re at hr
      rw [hzre, hwre, Set.uIcc_of_le hb.le] at hr
      rw [he] at hr
      norm_num only [Complex.neg_re, Complex.div_ofNat_re, Complex.one_re] at hr
      linarith only [hr.1]
    · exact Finset.mem_singleton.mpr (sub_eq_zero.mp he)
  have hfinite :
    ∀ s ∈ ({(p : ℂ)} : Finset ℂ), analyticOrderAt (fun s : ℂ => s - (p : ℂ)) s ≠ ⊤ := by
    intro s hs
    rw [Finset.mem_singleton] at hs
    rw [hs, analyticOrderAt_id_sub_const_self]
    exact ENat.one_ne_top
  have h :=
    weightedFiniteContourIdentity K hx
      (by
        rw [hzre, hwre]; exact hb)
      (by
        rw [hzim, hwim]; exact neg_lt_self hT)
      hreg hF hFp {(p : ℂ)} (fun s hs => (Finset.mem_singleton.mp hs) ▸ hc)
      (fun s hs => (Finset.mem_singleton.mp hs) ▸ ho) hcover hfinite
  have hpn : (p : ℂ) ≠ -1 / 2 := by
    intro he
    apply hFp
    rw [he, sub_self]
  simpa only [z, w, logDeriv_apply, deriv_sub_const, deriv_id'', Finset.sum_singleton,
    weightedResidue, ite_eq_right hpn, analyticOrderNatAt, analyticOrderAt_id_sub_const_self,
    ENat.toNat_one, Nat.cast_one, neg_one_mul, mul_neg] using h

/-- For a positive real pole below an admissible right line and `x ≥ 1`, the
right pole integral equals `2π K(p)x^p` plus its central-line integral.
Compare the finite rectangle residue identity with the infinite-height boundary
limit, then cancel `i`. This isolates the main term in the principal Mellin sum. -/
theorem poleIntegral_eq_central_add_residue (K : MellinKernel) {p b x : ℝ} (hp : 0 < p)
    (hpb : p < b) (hbK : b ≤ 1 / 2 + K.delta) (hx : 1 ≤ x) :
    (∫ t : ℝ,
        (1 / (((b : ℂ) + Complex.I * t) - (p : ℂ))) *
          (K.function ((b : ℂ) + Complex.I * t) * (x : ℂ) ^ ((b : ℂ) + Complex.I * t))) =
      2 * (Real.pi : ℂ) * (K.function (p : ℂ) * (x : ℂ) ^ (p : ℂ)) +
        (∫ t : ℝ,
          (1 / (Complex.I * t - (p : ℂ))) *
            (K.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))) := by
  let F := fun s : ℂ => -(1 / (s - (p : ℂ))) * (K.function s * (x : ℂ) ^ s)
  let T := fun n : ℕ => (n : ℝ) + 1
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hb : 0 ≤ b := (hp.trans hpb).le
  have hl0 : -1 / 2 - K.delta < (0 : ℝ) := by linarith only [K.delta_pos]
  have hlb : -1 / 2 - K.delta < b := hl0.trans_le hb
  have h0 : (0 : ℝ) ≤ 1 / 2 + K.delta := hb.trans hbK
  have hi0 :=
    (integrable_pole_power_line K hl0 h0 (by norm_num only : (0 : ℝ) ≠ -1 / 2) hp.ne hxpos).neg
  have hib :=
    (integrable_pole_power_line K hlb hbK (by linarith only [hb] : b ≠ -1 / 2) (ne_of_gt hpb)
        hxpos).neg
  have htop := (tendsto_pole_horizontalIntegral K hb hl0 hbK hx p 1 (Or.inl rfl)).neg
  have hbot := (tendsto_pole_horizontalIntegral K hb hl0 hbK hx p (-1) (Or.inr rfl)).neg
  have ht :=
    AnalyticNumberTheory.RectangleGeometry.tendsto_rectangleBoundaryIntegral_of_horizontal_limits
      (K := F) (a := 0) (b := b) T
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      (by
        simpa only [F, T, neg_one_mul, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, one_mul,
          mul_assoc, intervalIntegral.integral_neg, neg_zero] using hbot)
      (by
        simpa only [F, T, one_mul, neg_mul, mul_assoc, intervalIntegral.integral_neg,
          neg_zero] using htop)
      (by simpa only [F, Pi.neg_def, neg_mul, mul_assoc, mul_comm Complex.I] using hi0)
      (by simpa only [F, Pi.neg_def, neg_mul, mul_assoc, mul_comm Complex.I] using hib)
  have hz (n : ℕ) :
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral F ((0 : ℂ) - T n * Complex.I)
        ((b : ℂ) + T n * Complex.I) =
      -(2 * Real.pi * Complex.I * (K.function (p : ℂ) * (x : ℂ) ^ (p : ℂ))) := by
    simpa only [F, Complex.ofReal_zero, zero_sub, neg_mul] using
      neg_pole_rectangleBoundaryIntegral_eq K hp hpb hbK
        (by
          dsimp only [T]; linarith only [Nat.cast_nonneg (α := ℝ) n])
        hxpos
  have he := tendsto_nhds_unique ht (tendsto_const_nhds.congr (fun n => (hz n).symm))
  simp only [F, neg_mul, MeasureTheory.integral_neg, Complex.ofReal_zero, zero_add] at he
  have he' :
    Complex.I *
        ((∫ t : ℝ,
            (1 / (((b : ℂ) + t * Complex.I) - (p : ℂ))) *
              (K.function ((b : ℂ) + t * Complex.I) * (x : ℂ) ^ ((b : ℂ) + t * Complex.I))) -
          ∫ t : ℝ,
            (1 / (t * Complex.I - (p : ℂ))) *
              (K.function (t * Complex.I) * (x : ℂ) ^ (t * Complex.I))) =
      Complex.I * (2 * (Real.pi : ℂ) * (K.function (p : ℂ) * (x : ℂ) ^ (p : ℂ))) := by
    linear_combination -he
  have hd := mul_left_cancel₀ Complex.I_ne_zero he'
  have hfinal := eq_add_of_sub_eq hd
  simpa only [mul_comm Complex.I] using hfinal

/-- For a positive real pole below the right line, normalization by `1/(2π)`
and subtraction of `K(p)x^p` leave the normalized central pole integral.
Apply the residue shift identity and cancel the nonzero factor `2π`.
This expresses the principal main-term remainder as a central integral. -/
theorem normalized_poleIntegral_sub_residue_eq_central (K : MellinKernel) {p b x : ℝ} (hp : 0 < p)
    (hpb : p < b) (hbK : b ≤ 1 / 2 + K.delta) (hx : 1 ≤ x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            (1 / (((b : ℂ) + Complex.I * t) - (p : ℂ))) *
              (K.function ((b : ℂ) + Complex.I * t) * (x : ℂ) ^ ((b : ℂ) + Complex.I * t))) -
        K.function (p : ℂ) * (x : ℂ) ^ (p : ℂ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (1 / (Complex.I * t - (p : ℂ))) *
            (K.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))) := by
  have hd : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * (Real.pi : ℂ)) = 1 := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div,
      inv_mul_cancel₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  rw [poleIntegral_eq_central_add_residue K hp hpb hbK hx, mul_add, ← mul_assoc, hd, one_mul,
    add_sub_cancel_left]

/-- For a fixed positive real pole, the normalized right integral minus
`K(p)x^p` is uniformly bounded for every admissible line above the pole and
`x ≥ 1`. Move the line to the center and apply its uniform bound.
This supplies the main-pole error in the principal explicit formula. -/
theorem exists_norm_poleIntegral_sub_residue_le (K : MellinKernel) {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {b x : ℝ},
          p < b →
            b ≤ 1 / 2 + K.delta →
            1 ≤ x →
            ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
                    (∫ t : ℝ,
                      (1 / (((b : ℂ) + Complex.I * t) - (p : ℂ))) *
                        (K.function ((b : ℂ) + Complex.I * t) *
                          (x : ℂ) ^ ((b : ℂ) + Complex.I * t))) -
                  K.function (p : ℂ) * (x : ℂ) ^ (p : ℂ)‖ ≤
              C := by
  obtain ⟨C, hC, hb⟩ := exists_norm_central_poleIntegral_le K hp.ne'
  refine ⟨C, hC, ?_⟩
  intro b x hpb hbK hx
  rw [normalized_poleIntegral_sub_residue_eq_central K hp hpb hbK hx]
  exact hb (zero_lt_one.trans_le hx)

/-- For a fixed negative real pole, the normalized pole integral is uniformly
bounded for every admissible nonnegative line and `x ≥ 1`. No pole is crossed
when moving to the center; apply line independence and the central bound.
This supplies the elementary completion error without a main contribution. -/
theorem exists_norm_poleIntegral_le_of_neg (K : MellinKernel) {p : ℝ} (hp : p < 0) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {b x : ℝ},
          0 ≤ b →
            b ≤ 1 / 2 + K.delta →
            1 ≤ x →
            ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ,
                    (1 / (((b : ℂ) + Complex.I * t) - (p : ℂ))) *
                      (K.function ((b : ℂ) + Complex.I * t) *
                        (x : ℂ) ^ ((b : ℂ) + Complex.I * t)))‖ ≤
              C := by
  obtain ⟨C, hC, hb⟩ := exists_norm_central_poleIntegral_le K hp.ne
  refine ⟨C, hC, ?_⟩
  intro b x hb0 hbK hx
  rw [poleIntegral_eq_central_of_neg K hp hb0 hbK hx]
  exact hb (zero_lt_one.trans_le hx)

end PseudoPrime.LLS.PaperStatements.MellinKernel
