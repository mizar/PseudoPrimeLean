/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelZetaHorizontal
public import PseudoPrime.LLS.MellinKernelZetaVerticalIntegrability
public import PseudoPrime.LLS.MellinKernelZetaContour
public import PseudoPrime.LLS.MellinKernelContourGeometry
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.GoodHeight

/-! # Infinite-height limits for the principal xi Mellin contour

Good zeta heights remove the horizontal edges, while logarithmic xi growth
proves both vertical integrals absolutely integrable. Their difference is the
limit of weighted rectangle boundary integrals.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- On admissible lines with `-1 ≤ a < -1/2 < 1/2 < b ≤ 1` and `x ≥ 1`,
weighted ξ rectangle boundaries along zeta good heights converge to the difference
of vertical integrals multiplied by `i`. Both vertical integrands are proved
integrable, and both horizontal edges vanish. This gives the infinite-height
principal contour without extra analytic assumptions. -/
theorem tendsto_xi_boundaryIntegral (K : MellinKernel) {a b x : ℝ} (hab : a ≤ b)
    (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta) (ha' : -1 ≤ a) (hb' : b ≤ 1) (hx : 1 ≤ x)
    (haleft : a < -1 / 2) (hbright : 1 / 2 < b) :
    let T := AnalyticNumberTheory.RiemannZeta.goodHeightSeq
    let F := fun s : ℂ =>
      -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s + 1 / 2) * (K.function s * (x : ℂ) ^ s)
    Filter.Tendsto
      (fun n =>
        AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral F
          ((a : ℂ) - T n * Complex.I) ((b : ℂ) + T n * Complex.I))
      Filter.atTop
      (nhds
        (Complex.I *
          ((∫ t : ℝ, F ((b : ℂ) + t * Complex.I)) - (∫ t : ℝ, F ((a : ℂ) + t * Complex.I))))) := by
  apply
    AnalyticNumberTheory.RectangleGeometry.tendsto_rectangleBoundaryIntegral_of_horizontal_limits _
      AnalyticNumberTheory.RiemannZeta.tendsto_goodHeightSeq_atTop
  · have h := (tendsto_xi_horizontalIntegral K hab ha hb ha' hb' hx (-1) (Or.inr rfl)).neg
    simpa only [neg_one_mul, one_mul, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, mul_assoc,
      intervalIntegral.integral_neg, neg_zero] using h
  · have h := (tendsto_xi_horizontalIntegral K hab ha hb ha' hb' hx 1 (Or.inl rfl)).neg
    simpa only [one_mul, neg_mul, mul_assoc, intervalIntegral.integral_neg, neg_zero] using h
  · simpa only [mul_comm Complex.I] using
      integrable_xi_left_line K ha haleft ha' (zero_lt_one.trans_le hx)
  · simpa only [mul_comm Complex.I] using
      integrable_xi_right_line K hbright hb hb' (zero_lt_one.trans_le hx)

open AnalyticNumberTheory AnalyticNumberTheory.RiemannXi in
/-- Under RH, every shifted ξ zero and the kernel pole in a good-height rectangle
is strictly interior when the left edge is below `-1/2` and the right edge above `1/2`.
RH fixes real coordinates; zeta good heights exclude the signed zero ordinates.
This removes the finite ξ contour's geometric ledger assumption. -/
theorem xiKernelSingularities_interior_goodHeight (hRH : RiemannHypothesis) (n : ℕ) {a b : ℝ}
    (ha : a < -1 / 2) (hb : 1 / 2 < b) :
    let T := RiemannZeta.goodHeightSeq n
    ∀ s ∈ xiKernelSingularities ((a : ℂ) - T * Complex.I) ((b : ℂ) + T * Complex.I),
      s ∈
        RectangleGeometry.rectangleOpenBox ((a : ℂ) - T * Complex.I) ((b : ℂ) + T * Complex.I) := by
  let T := RiemannZeta.goodHeightSeq n
  have ht : 0 < T := by
    have hh := (RiemannZeta.goodHeightSeq_mem n).1
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    change 0 < RiemannZeta.goodHeightSeq n
    linarith only [hh, hn]
  dsimp only
  intro s hs
  have hmem := mem_xiKernelSingularities.mp hs
  have hlr : ((a : ℂ) - (T : ℂ) * Complex.I).re = a := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero]
  have hrr : ((b : ℂ) + (T : ℂ) * Complex.I).re = b := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hli : ((a : ℂ) - (T : ℂ) * Complex.I).im = -T := by
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, add_zero, zero_sub]
  have hri : ((b : ℂ) + (T : ℂ) * Complex.I).im = T := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  have hsr : s.re = -1 / 2 ∨ s.re = 0 := by
    rcases hmem.2 with he | hz
    · left
      rw [he]
      norm_num only [Complex.neg_re, Complex.div_ofNat_re, Complex.one_re]
    · right
      have hr := riemannXi_zero_re_eq_half_of_riemannHypothesis hRH hz
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hr
      linarith only [hr]
  have hsi : s.im ≠ -T ∧ s.im ≠ T := by
    rcases hmem.2 with he | hz
    · rw [he]
      have hi : (-1 / 2 : ℂ).im = 0 := by
        norm_num only [Complex.neg_im, Complex.div_ofNat_im, Complex.one_im]
      rw [hi]
      constructor <;> intro heq <;> linarith only [heq, ht]
    · have hh := zero_im_ne_goodHeight n hz
      simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div, add_zero] at hh
      exact ⟨hh.2, hh.1⟩
  apply
    RectangleGeometry.mem_rectangleOpenBox_of_mem_closedBox_of_ne
      (by
        rw [hlr, hrr]; linarith only [ha, hb])
      (by
        rw [hli, hri]; exact neg_lt_self ht)
      hmem.1
  · rw [hlr]
    rcases hsr with he | he <;> rw [he] <;> intro heq <;> linarith only [ha, heq]
  · rw [hrr]
    rcases hsr with he | he <;> rw [he] <;> intro heq <;> linarith only [hb, heq]
  · rw [hli]
    exact hsi.1
  · rw [hri]
    exact hsi.2

open AnalyticNumberTheory AnalyticNumberTheory.RiemannXi in
/-- Under RH, every good-height rectangle with admissible real endpoints has
weighted ξ boundary integral equal to its finite residue sum. The kernel strip
contains the rectangle, and the good-height ledger is strictly interior.
This gives the finite identity used in the infinite-height limit. -/
theorem xiGoodHeightContourIdentity (K : MellinKernel) (hRH : RiemannHypothesis) (n : ℕ) {a b x : ℝ}
    (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta) (haleft : a < -1 / 2)
    (hbright : 1 / 2 < b) (hx : 0 < x) :
    let T := RiemannZeta.goodHeightSeq n
    RectangleGeometry.rectangleBoundaryIntegral
        (fun s => -logDeriv riemannXi (s + 1 / 2) * (K.function s * (x : ℂ) ^ s))
        ((a : ℂ) - T * Complex.I) ((b : ℂ) + T * Complex.I) =
      ∑ s ∈ xiKernelSingularities ((a : ℂ) - T * Complex.I) ((b : ℂ) + T * Complex.I),
        2 * Real.pi * Complex.I * weightedResidue K (fun t : ℂ => riemannXi (t + 1 / 2)) x s := by
  let T := RiemannZeta.goodHeightSeq n
  have hab : a < b := by linarith only [haleft, hbright]
  have ht : 0 < T := by
    have hh := (RiemannZeta.goodHeightSeq_mem n).1
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    change 0 < RiemannZeta.goodHeightSeq n
    linarith only [hh, hn]
  apply xiKernelFiniteContourIdentity K hx
  · simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using
      hab
  · simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_sub,
      zero_add] using neg_lt_self ht
  · exact closed_goodHeight_box_subset_region K hab.le ha hb
  · exact xiKernelSingularities_interior_goodHeight hRH n haleft hbright

open AnalyticNumberTheory AnalyticNumberTheory.RiemannXi in
/-- Under RH and `x ≥ 1`, admissible lines on either side of the kernel pole and
critical line satisfy the ξ Mellin contour identity with the infinite zero sum.
The vertical-integral difference equals `2π` times the kernel-pole residue minus
the oscillatory ξ zero series, after multiplication by `i`. Identify the two
limits of good-height rectangle boundaries: vertical integration and finite
residue exhaustion. This is the analytic contour step for the principal estimate. -/
theorem xiContourIdentity (K : MellinKernel) (hRH : RiemannHypothesis) {a b x : ℝ}
    (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta) (ha' : -1 ≤ a) (hb' : b ≤ 1)
    (haleft : a < -1 / 2) (hbright : 1 / 2 < b) (hx : 1 ≤ x) :
    let F := fun s : ℂ => -logDeriv riemannXi (s + 1 / 2) * (K.function s * (x : ℂ) ^ s)
    Complex.I * ((∫ t : ℝ, F ((b : ℂ) + t * Complex.I)) - (∫ t : ℝ, F ((a : ℂ) + t * Complex.I))) =
      (2 * Real.pi * Complex.I) *
        (weightedResidue K (fun t : ℂ => riemannXi (t + 1 / 2)) x (-1 / 2) -
          ∑' ρ, K.zetaOscillatingZeroTerm x ρ) := by
  have hab : a ≤ b := by linarith only [haleft, hbright]
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hboundary := tendsto_xi_boundaryIntegral K hab ha hb ha' hb' hx haleft hbright
  have hres :=
    (tendsto_xiKernelResidueSum K hRH RiemannZeta.tendsto_goodHeightSeq_atTop haleft
          (by linarith only [hbright]) hxp).const_mul
      (2 * (Real.pi : ℂ) * Complex.I)
  have heq (n : ℕ) :
    RectangleGeometry.rectangleBoundaryIntegral
        (fun s => -logDeriv riemannXi (s + 1 / 2) * (K.function s * (x : ℂ) ^ s))
        ((a : ℂ) - RiemannZeta.goodHeightSeq n * Complex.I)
        ((b : ℂ) + RiemannZeta.goodHeightSeq n * Complex.I) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ∑
          s ∈
            xiKernelSingularities ((a : ℂ) - RiemannZeta.goodHeightSeq n * Complex.I)
              ((b : ℂ) + RiemannZeta.goodHeightSeq n * Complex.I),
          weightedResidue K (fun t : ℂ => riemannXi (t + 1 / 2)) x s := by
    rw [xiGoodHeightContourIdentity K hRH n ha hb haleft hbright hxp, Finset.mul_sum]
  have hr := hres.congr' (Filter.Eventually.of_forall (fun n => (heq n).symm))
  exact tendsto_nhds_unique hboundary hr

end PseudoPrime.LLS.PaperStatements.MellinKernel
