/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelFiniteContour
public import PseudoPrime.LLS.MellinKernelHorizontal

/-!
# Good-height rectangle geometry for completed Mellin contours

GRH puts shifted completed zeros on the imaginary axis.
Good heights avoid their ordinates, while the kernel pole stays strictly inside
the chosen left and right lines.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal GRH data, no completed zero has ordinate equal to either
signed good height. GRH gives real part one half, and horizontal nonvanishing excludes
both candidate points. This prevents zeros on the horizontal contour edges. -/
theorem completed_zero_im_ne_goodHeight {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (n : ℕ) {ρ : ℂ} (hz : χ.completedLFunction ρ = 0) :
    ρ.im ≠ primitiveHorizontalHeightSeq hq hGRH hp hne hinv n ∧
      ρ.im ≠ -primitiveHorizontalHeightSeq hq hGRH hp hne hinv n := by
  let T := primitiveHorizontalHeightSeq hq hGRH hp hne hinv n
  have hr := completedLFunction_zero_re_eq_half hGRH hp hne hinv hz
  have hb :=
    primitiveHorizontalHeightSeq_completedLFunction_ne_zero hq hGRH hp hne hinv n (σ := 1 / 2)
      (by norm_num only : |(1 : ℝ) / 2| ≤ 2)
  constructor
  · intro ht
    have he : ρ = ((1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I := by
      apply Complex.ext
      · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero] using hr
      · simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] using ht
    exact hb.1 (he ▸ hz)
  · intro ht
    have he : ρ = ((1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I := by
      apply Complex.ext
      · simpa only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero] using hr
      · simpa only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_sub] using ht
    exact hb.2 (he ▸ hz)

open AnalyticNumberTheory in
/-- An ordered real interval contained in the kernel strip gives a closed rectangle in
the kernel region at any symmetric height. Read the real-coordinate bounds from
closed-box membership and apply the strip containment. This verifies contour holomorphy. -/
theorem closed_goodHeight_box_subset_region (K : MellinKernel) {a b T : ℝ} (hab : a ≤ b)
    (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta) :
    Rectangle.rectangleClosedBox ((a : ℂ) - (T : ℂ) * Complex.I) ((b : ℂ) + (T : ℂ) * Complex.I) ⊆
      K.region := by
  intro s hs
  have hr := hs.1
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Set.uIcc_of_le hab] at hr
  exact K.strip_subset ⟨ha.trans_le hr.1, hr.2.trans hb⟩

open AnalyticNumberTheory in
/-- For primitive nonprincipal GRH data, left real part below minus one half and right
real part above one half, every ledger point is interior to each good-height rectangle.
The kernel pole has zero ordinate and the shifted zeros have zero real part;
the good heights avoid both signed zero ordinates. This discharges the finite
residue formula's geometric hypothesis. -/
theorem completedKernelSingularities_interior_goodHeight {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (n : ℕ) {a b : ℝ} (ha : a < -1 / 2) (hb : 1 / 2 < b) :
    let T := DirichletLFunction.primitiveHorizontalHeightSeq hq hGRH hp hne hinv n
    ∀
      s ∈
        DirichletLFunction.completedKernelSingularities hp hne ((a : ℂ) - (T : ℂ) * Complex.I)
          ((b : ℂ) + (T : ℂ) * Complex.I),
      s ∈
        RectangleGeometry.rectangleOpenBox ((a : ℂ) - (T : ℂ) * Complex.I)
          ((b : ℂ) + (T : ℂ) * Complex.I) := by
  let T := DirichletLFunction.primitiveHorizontalHeightSeq hq hGRH hp hne hinv n
  have ht : 0 < T :=
    zero_lt_one.trans_le
      ((le_add_of_nonneg_left (Nat.cast_nonneg n)).trans
        (DirichletLFunction.primitiveHorizontalHeightSeq_ge hq hGRH hp hne hinv n))
  dsimp only
  intro s hs
  have hmem := DirichletLFunction.mem_completedKernelSingularities.mp hs
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
      have hr := DirichletLFunction.completedLFunction_zero_re_eq_half hGRH hp hne hinv hz
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hr
      linarith only [hr]
  have hsi : s.im ≠ -T ∧ s.im ≠ T := by
    rcases hmem.2 with he | hz
    · rw [he]
      have hi : (-1 / 2 : ℂ).im = 0 := by
        norm_num only [Complex.neg_im, Complex.div_ofNat_im, Complex.one_im]
      rw [hi]
      constructor <;> intro heq <;> linarith only [heq, ht]
    · have hh := completed_zero_im_ne_goodHeight hq hGRH hp hne hinv n hz
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

end PseudoPrime.LLS.PaperStatements.MellinKernel
