/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogHorizontalEdges
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogContourRectangle

/-! # Unconditional good-height rectangles and finite logarithmic residue identities -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a natural left-edge parameter and real height, place the lower-left corner
at real part minus the parameter minus one half and imaginary part minus the height.
This fixes the unconditional contour rectangle independently of any chosen sequence. -/
noncomputable def unconditionalHeightLowerCorner (A : ℕ) (T : ℝ) : ℂ :=
  ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I

/-- For a real height, place the upper-right contour corner at real part two and
imaginary part equal to that height. This matches the Perron integral abscissa. -/
noncomputable def unconditionalHeightUpperCorner (T : ℝ) : ℂ :=
  ((2 : ℝ) : ℂ) + (T : ℂ) * Complex.I

/-- For left-edge parameter at least two and positive height, identify all corner
coordinates and prove both strict orientations. Expand the definitions and compare
real coordinates. These facts supply finite-contour geometry without GRH. -/
theorem unconditionalHeightRectangleFacts (A : ℕ) (hA : 2 ≤ A) (T : ℝ) (hT : 0 < T) :
    (unconditionalHeightLowerCorner A T).re = -(A : ℝ) - 1 / 2 ∧
      (unconditionalHeightLowerCorner A T).im = -T ∧
      (unconditionalHeightUpperCorner T).re = 2 ∧
      (unconditionalHeightUpperCorner T).im = T ∧
      (unconditionalHeightLowerCorner A T).re < (unconditionalHeightUpperCorner T).re ∧
      (unconditionalHeightLowerCorner A T).im < (unconditionalHeightUpperCorner T).im := by
  have hAreal : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hcoords :
    (unconditionalHeightLowerCorner A T).re = -(A : ℝ) - 1 / 2 ∧
      (unconditionalHeightLowerCorner A T).im = -T ∧
      (unconditionalHeightUpperCorner T).re = 2 ∧ (unconditionalHeightUpperCorner T).im = T := by
    simp only [unconditionalHeightLowerCorner, unconditionalHeightUpperCorner, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, sub_zero,
      Complex.add_re, add_zero, Complex.sub_im, Complex.mul_im, Complex.I_im, mul_one, zero_sub,
      Complex.add_im, zero_add, and_self]
  exact
    ⟨hcoords.1, hcoords.2.1, hcoords.2.2.1, hcoords.2.2.2, by
      rw [hcoords.1, hcoords.2.2.1]; linarith only [hAreal], by
      rw [hcoords.2.1, hcoords.2.2.2]; linarith only [hT]⟩

/-- A positive height whose completed function is nonzero on both central edges
avoids every ordinary L-zero at either signed height, for a primitive nonprincipal
character. An ordinary zero would give a completed zero in the open critical strip,
contradicting the central nonvanishing. This excludes singularities on full horizontal edges. -/
theorem ordinaryLFunction_ne_zero_on_signed_horizontal {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (T : ℝ)
    (hT : 0 < T)
    (hcentral :
      ∀ σ : ℝ,
        |σ| ≤ 2 →
          χ.completedLFunction ((σ : ℂ) + T * Complex.I) ≠ 0 ∧
            χ.completedLFunction ((σ : ℂ) - T * Complex.I) ≠ 0)
    {s : ℂ} (hs : s.im = T ∨ s.im = -T) : χ.LFunction s ≠ 0 := by
  intro hzero
  have hsim : s.im ≠ 0 := by
    rcases hs with h | h
    · rw [h]
      exact hT.ne'
    · rw [h]
      exact neg_ne_zero.mpr hT.ne'
  have hΓ : DirichletCharacter.gammaFactor χ s ≠ 0 := gammaFactor_ne_zero_of_im_ne_zero hsim
  have heq :=
    dirichletLFunction_eq_completed_div_gammaFactor χ s
      (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne))
  have hFzero : χ.completedLFunction s = 0 := (div_eq_zero_iff.mp (heq ▸ hzero)).resolve_right hΓ
  have hpos := completedLFunction_zero_re_pos hp hinv hFzero
  have hlt := completedLFunction_zero_re_lt_one hne hFzero
  have hsreal : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith only [hpos], by linarith only [hlt]⟩
  obtain ⟨hplus, hminus⟩ := hcentral s.re hsreal
  rcases hs with hs | hs
  · have hrepr : s = ((s.re : ℝ) : ℂ) + (T : ℂ) * Complex.I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      · simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using hs
    exact hplus (hrepr ▸ hFzero)
  · have hrepr : s = ((s.re : ℝ) : ℂ) - (T : ℂ) * Complex.I := by
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, zero_mul, sub_zero]
      · simpa only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_sub] using hs
    exact hminus (hrepr ▸ hFzero)

/-- For a primitive nonprincipal character, positive good height, and negative
half-integer left edge, every finite singularity lies strictly inside the contour.
Exclude Mellin points and ordinary zeros from all four boundary coordinates using
central nonvanishing, right-half-plane nonvanishing, and the left-vertical theorem.
This supplies the unconditional finite-contour interior condition. -/
theorem unconditionalHeight_singularities_mem_open {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A : ℕ) (hA : 2 ≤ A) (T : ℝ) (hTpos : 0 < T)
    (hcentral :
      ∀ σ : ℝ,
        |σ| ≤ 2 →
          χ.completedLFunction ((σ : ℂ) + T * Complex.I) ≠ 0 ∧
            χ.completedLFunction ((σ : ℂ) - T * Complex.I) ≠ 0) :
    ∀
      s ∈
        dirichletLFunctionSingularitiesInRectangle χ hne (unconditionalHeightLowerCorner A T)
          (unconditionalHeightUpperCorner T),
      s ∈
        RectangleGeometry.rectangleOpenBox (unconditionalHeightLowerCorner A T)
          (unconditionalHeightUpperCorner T) := by
  intro s hs
  obtain ⟨hrect, hcase⟩ := mem_dirichletLFunctionSingularitiesInRectangle_iff.mp hs
  obtain ⟨hzre, hzim, hwre, hwim, hre, him⟩ := unconditionalHeightRectangleFacts A hA T hTpos
  have hA' : (2 : ℝ) ≤ A := by exact_mod_cast hA
  apply RectangleGeometry.mem_rectangleOpenBox_of_mem_closedBox_of_ne hre him hrect
  · rcases hcase with hs0 | hs1 | hLzero
    · rw [hs0, hzre]
      simp only [Complex.zero_re, one_div, ne_eq]
      linarith only [hA']
    · rw [hs1, hzre]
      simp only [Complex.one_re, one_div, ne_eq]
      linarith only [hA']
    · rw [hzre]
      intro heq
      have hseq : s = ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (s.im : ℂ) * Complex.I := by
        rw [← heq, Complex.re_add_im]
      rw [hseq] at hLzero
      exact dirichletLFunction_ne_zero_leftVertical hp hne hinv A hA s.im hLzero
  · rcases hcase with hs0 | hs1 | hLzero
    · rw [hs0, hwre]
      change (0 : ℝ) ≠ 2
      norm_num only
    · rw [hs1, hwre]
      change (1 : ℝ) ≠ 2
      norm_num only
    · rw [hwre]
      intro heq
      exact
        DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne)
          (by
            rw [heq]
            norm_num only)
          hLzero
  · rcases hcase with hs0 | hs1 | hLzero
    · rw [hs0, hzim]
      simp only [Complex.zero_im, ne_eq, zero_eq_neg]
      linarith only [hTpos]
    · rw [hs1, hzim]
      simp only [Complex.one_im, ne_eq, zero_eq_neg]
      linarith only [hTpos]
    · rw [hzim]
      intro heq
      exact
        ordinaryLFunction_ne_zero_on_signed_horizontal hp hne hinv T hTpos hcentral (Or.inr heq)
          hLzero
  · rcases hcase with hs0 | hs1 | hLzero
    · rw [hs0, hwim]
      simpa only [Complex.zero_im, ne_eq] using hTpos.ne
    · rw [hs1, hwim]
      simpa only [Complex.one_im, ne_eq] using hTpos.ne
    · rw [hwim]
      intro heq
      exact
        ordinaryLFunction_ne_zero_on_signed_horizontal hp hne hinv T hTpos hcentral (Or.inl heq)
          hLzero

/-- The Mellin points zero and one belong to every positively oriented unconditional
height rectangle with left-edge parameter at least two. Check their real and
imaginary coordinates explicitly. This permits splitting the finite residue sum. -/
theorem unconditionalHeight_mellinPoints_mem {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) (A : ℕ) (hA : 2 ≤ A) (T : ℝ) (hT : 0 < T) :
    (0 : ℂ) ∈
        dirichletLFunctionSingularitiesInRectangle χ hne (unconditionalHeightLowerCorner A T)
          (unconditionalHeightUpperCorner T) ∧
      (1 : ℂ) ∈
        dirichletLFunctionSingularitiesInRectangle χ hne (unconditionalHeightLowerCorner A T)
          (unconditionalHeightUpperCorner T) := by
  obtain ⟨hzre, hzim, hwre, hwim, _, _⟩ := unconditionalHeightRectangleFacts A hA T hT
  have hAreal : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hbox (u : ℝ) (hu : 0 ≤ u ∧ u ≤ 1) :
    (u : ℂ) ∈
      dirichletCompletedLFunctionRectangleBox (unconditionalHeightLowerCorner A T)
        (unconditionalHeightUpperCorner T) := by
    rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox, Complex.mem_reProdIm,
      hzre, hzim, hwre, hwim, Complex.ofReal_re, Complex.ofReal_im]
    exact
      ⟨Set.Icc_subset_uIcc ⟨by linarith only [hAreal, hu.1], by linarith only [hu.2]⟩,
        Set.Icc_subset_uIcc ⟨by linarith only [hT], hT.le⟩⟩
  exact
    ⟨mem_dirichletLFunctionSingularitiesInRectangle_iff.mpr
        ⟨hbox 0 ⟨le_refl 0, zero_le_one⟩, Or.inl rfl⟩,
      mem_dirichletLFunctionSingularitiesInRectangle_iff.mpr
        ⟨hbox 1 ⟨zero_le_one, le_refl 1⟩, Or.inr (Or.inl rfl)⟩⟩

/-- For a primitive nonprincipal character and an unconditional good-height rectangle,
the normalized logarithmic boundary integral equals its finite residue sum.
Apply the generic finite-contour identity with the proved interior condition.
This removes GRH from the fixed-height logarithmic residue identity. -/
theorem unconditionalHeight_logFiniteContourIdentity_normalized {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A : ℕ)
    (hA : 2 ≤ A) (T : ℝ) (hT : 0 < T)
    (hcentral :
      ∀ σ : ℝ,
        |σ| ≤ 2 →
          χ.completedLFunction ((σ : ℂ) + T * Complex.I) ≠ 0 ∧
            χ.completedLFunction ((σ : ℂ) - T * Complex.I) ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    (-Complex.I / (2 * Real.pi)) *
        RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
          (unconditionalHeightLowerCorner A T) (unconditionalHeightUpperCorner T) =
      ∑
        ρ ∈
          dirichletLFunctionSingularitiesInRectangle χ hne (unconditionalHeightLowerCorner A T)
            (unconditionalHeightUpperCorner T),
        dirichletLogResidueAt hne x ρ := by
  obtain ⟨_, _, _, _, hre, him⟩ := unconditionalHeightRectangleFacts A hA T hT
  exact
    dirichletLogFiniteContourIdentity_normalized hx hp hne hre him
      (unconditionalHeight_singularities_mem_open hp hne hinv A hA T hT hcentral)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
