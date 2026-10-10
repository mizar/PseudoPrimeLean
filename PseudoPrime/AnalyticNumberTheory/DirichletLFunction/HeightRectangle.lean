/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveHorizontalLogDerivBound
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ContourRegularity
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LeftVerticalNonvanishing
public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.Boundary

/-! # Kernel-independent height and rectangle constructions -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The fixed left real part `λ_A := -A - 1/2` of the left-vertical edge. -/
noncomputable def primitiveReciprocalLeftRe (A : ℕ) : ℝ :=
  -(A : ℝ) - 1 / 2

/-- For a primitive nontrivial character with nontrivial inverse under GRH and level
`N ≥ 2`, define the lower-left corner `-A-1/2 - i*T_k` using the general good-height
sequence. This fixes the rectangle used by both Mellin kernels for indices `A` and `k`. -/
noncomputable def primitiveHeightSeqLowerCorner {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A k : ℕ) : ℂ :=
  ((primitiveReciprocalLeftRe A : ℝ) : ℂ) -
    (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k : ℂ) * Complex.I

/-- For the same primitive-character GRH hypotheses, define the upper-right corner
`2 + i*T_k` using the general good-height sequence. The right edge lies in the
absolutely convergent Dirichlet-series half-plane for the contour identities. -/
noncomputable def primitiveHeightSeqUpperCorner {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) : ℂ :=
  ((2 : ℝ) : ℂ) + (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k : ℂ) * Complex.I

/-! The following coordinate proof intentionally uses simplification to expose
the complex components. -/

/-- Real and imaginary coordinates, together with strict rectangle orientation
for generic corners. -/
theorem primitiveHeightSeqRectangleFacts {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A k : ℕ) (hA : 2 ≤ A) :
    (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k).re =
        primitiveReciprocalLeftRe A ∧
      (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k).im =
        -(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k) ∧
      (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k).re = 2 ∧
      (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k).im =
        primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k ∧
      (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k).re <
        (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k).re ∧
      (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k).im <
        (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k).im := by
  have hTge := primitiveHorizontalHeightSeq_ge hN2 hGRH hprimitive hne hinv k
  have hTpos : (0 : ℝ) < primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith only [hTge, hknn]
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num only [primitiveHeightSeqLowerCorner, primitiveReciprocalLeftRe, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      mul_one, sub_self, add_zero]
    ring
  · norm_num only [primitiveHeightSeqLowerCorner, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
      sub_zero, zero_sub]
  · norm_num only [primitiveHeightSeqUpperCorner, RCLike.ofNat_re, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      mul_one, add_zero]
  · norm_num only [primitiveHeightSeqUpperCorner, RCLike.ofNat_im, Complex.add_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
      mul_zero, add_zero, zero_add, sub_zero, zero_sub]
  · rw [primitiveHeightSeqLowerCorner, primitiveHeightSeqUpperCorner, primitiveReciprocalLeftRe]
    norm_num only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    linarith only [hA']
  · rw [primitiveHeightSeqLowerCorner, primitiveHeightSeqUpperCorner]
    norm_num only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    linarith only [hTpos]

/-- For a primitive nontrivial character with nontrivial inverse under GRH and
`N ≥ 2`, the ordinary L-function is nonzero at any real part on either selected
horizontal line. Reflect the left half-plane, use Euler nonvanishing on the right,
and use GRH and good-height nonvanishing in the critical strip. This protects both edges. -/
theorem dirichletLFunction_ne_zero_of_im_eq_primitiveHeightSeq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) {s : ℂ}
    (him :
      s.im = primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k ∨
        s.im = -(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  intro hL
  have hTge := primitiveHorizontalHeightSeq_ge hN2 hGRH hprimitive hne hinv k
  have hTpos : (0 : ℝ) < primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith only [hTge, hknn]
  have himne : s.im ≠ 0 := by
    rcases him with h | h
    · rw [h]
      exact hTpos.ne'
    · rw [h]
      exact (neg_lt_zero.mpr hTpos).ne
  have hΓne : DirichletCharacter.gammaFactor χ s ≠ 0 := gammaFactor_ne_zero_of_im_ne_zero himne
  have hFeq :=
    dirichletLFunction_eq_completed_div_gammaFactor χ s
      (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne))
  have hFzero : DirichletCharacter.completedLFunction χ s = 0 := by
    apply (div_eq_zero_iff.mp (hFeq ▸ hL)).resolve_right hΓne
  by_cases hre0 : s.re ≤ 0
  · have hs1re : (1 : ℝ) ≤ (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re, le_sub_self_iff]
      exact hre0
    exact completedLFunction_ne_zero_farLeft hprimitive hne hinv hs1re hFzero
  · rw [not_le] at hre0
    by_cases hre1 : (1 : ℝ) ≤ s.re
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) hre1 hL
    · rw [not_le] at hre1
      have hhalf := hGRH.zero_re_eq_half N χ hprimitive s hL hre0
      obtain ⟨hpos_ne, hneg_ne⟩ :=
        primitiveHorizontalHeightSeq_completedLFunction_ne_zero hN2 hGRH hprimitive hne hinv k
          (by norm_num only : |(1 / 2 : ℝ)| ≤ 2)
      rcases him with h | h
      · apply hpos_ne
        have hseq :
          s =
            ((1 / 2 : ℝ) : ℂ) +
              (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k : ℂ) * Complex.I := by
          apply Complex.ext
          · simp only [hhalf, one_div, Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.add_re,
              Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self',
              Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
              Complex.I_im, mul_one, sub_self, add_zero]
          · simp only [h, one_div, Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.add_im,
              Complex.inv_im, Complex.im_ofNat, neg_zero, Complex.normSq_ofNat, zero_div,
              Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
              Complex.I_re, mul_zero, add_zero, zero_add]
        rwa [← hseq]
      · apply hneg_ne
        have hseq :
          s =
            ((1 / 2 : ℝ) : ℂ) -
              (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k : ℂ) * Complex.I := by
          apply Complex.ext
          · simp only [hhalf, one_div, Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.sub_re,
              Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self',
              Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
              Complex.I_im, mul_one, sub_self, sub_zero]
          · simp only [h, one_div, Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.sub_im,
              Complex.inv_im, Complex.im_ofNat, neg_zero, Complex.normSq_ofNat, zero_div,
              Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
              Complex.I_re, mul_zero, add_zero, zero_sub]
        rwa [← hseq]

/-- Under the primitive-character GRH hypotheses and `A ≥ 2`, every listed Mellin
point or ordinary L-function zero in the closed good-height rectangle is interior.
The coordinate bounds put `0` and `1` inside; nonvanishing excludes zeros on all four
edges. This supplies the interior-singularity premise of the finite contour identities. -/
theorem primitiveHeightSeq_singularities_mem_open {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A k : ℕ) (hA : 2 ≤ A) :
    ∀
      s ∈
        dirichletLFunctionSingularitiesInRectangle χ hne
          (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
          (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k),
      s ∈
        RectangleGeometry.rectangleOpenBox
          (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
          (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k) := by
  intro s hs
  obtain ⟨hrect, hcase⟩ := mem_dirichletLFunctionSingularitiesInRectangle_iff.mp hs
  obtain ⟨hzre, hzim, hwre, hwim, hre, him⟩ :=
    primitiveHeightSeqRectangleFacts hN2 hGRH hprimitive hne hinv A k hA
  have hTge := primitiveHorizontalHeightSeq_ge hN2 hGRH hprimitive hne hinv k
  have hTpos : (0 : ℝ) < primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith only [hTge, hknn]
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  apply RectangleGeometry.mem_rectangleOpenBox_of_mem_closedBox_of_ne hre him hrect
  · rcases hcase with hs0 | hs1 | hLzero
    · rw [hs0, hzre, primitiveReciprocalLeftRe]
      simp only [Complex.zero_re, one_div, ne_eq]
      linarith only [hA']
    · rw [hs1, hzre, primitiveReciprocalLeftRe]
      simp only [Complex.one_re, one_div, ne_eq]
      linarith only [hA']
    · rw [hzre]
      intro heq
      have hseq : s = ((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (s.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp only [← heq, Complex.re_add_im]
      rw [primitiveReciprocalLeftRe] at hseq
      rw [hseq] at hLzero
      exact dirichletLFunction_ne_zero_leftVertical hprimitive hne hinv A hA s.im hLzero
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
        dirichletLFunction_ne_zero_of_im_eq_primitiveHeightSeq hN2 hGRH hprimitive hne hinv k
          (Or.inr heq) hLzero
  · rcases hcase with hs0 | hs1 | hLzero
    · rw [hs0, hwim]
      simpa only [Complex.zero_im, ne_eq] using hTpos.ne
    · rw [hs1, hwim]
      simpa only [Complex.one_im, ne_eq] using hTpos.ne
    · rw [hwim]
      intro heq
      exact
        dirichletLFunction_ne_zero_of_im_eq_primitiveHeightSeq hN2 hGRH hprimitive hne hinv k
          (Or.inl heq) hLzero

/-- The Mellin points `0` and `1` belong to the generic GRH height-sequence rectangle. -/
theorem primitiveReciprocalMellinPoints_mem_singularities_heightSeq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A k : ℕ) (hA : 2 ≤ A) :
    (0 : ℂ) ∈
        dirichletLFunctionSingularitiesInRectangle χ hne
          (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
          (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k) ∧
      (1 : ℂ) ∈
        dirichletLFunctionSingularitiesInRectangle χ hne
          (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
          (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k) := by
  obtain ⟨hzre, hzim, hwre, hwim, _, _⟩ :=
    primitiveHeightSeqRectangleFacts hN2 hGRH hprimitive hne hinv A k hA
  set z := primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k
  set w := primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hTge := primitiveHorizontalHeightSeq_ge hN2 hGRH hprimitive hne hinv k
  have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h0mem : (0 : ℂ) ∈ dirichletCompletedLFunctionRectangleBox z w := by
    rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox, Complex.mem_reProdIm]
    refine ⟨Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩), Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩)⟩
    · rw [hzre, primitiveReciprocalLeftRe]
      simp only [one_div, Complex.zero_re, tsub_le_iff_right, zero_add]
      linarith only [hA']
    · rw [hwre]
      change (0 : ℝ) ≤ 2
      norm_num only
    · rw [hzim]
      simp only [Complex.zero_im, Left.neg_nonpos_iff]
      linarith only [hTge, hknn]
    · rw [hwim]
      simp only [Complex.zero_im]
      linarith only [hTge, hknn]
  have h1mem : (1 : ℂ) ∈ dirichletCompletedLFunctionRectangleBox z w := by
    rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox, Complex.mem_reProdIm]
    refine ⟨Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩), Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩)⟩
    · rw [hzre, primitiveReciprocalLeftRe]
      simp only [one_div, Complex.one_re, tsub_le_iff_right]
      linarith only [hA']
    · rw [hwre]
      change (1 : ℝ) ≤ 2
      norm_num only
    · rw [hzim]
      simp only [Complex.one_im, Left.neg_nonpos_iff]
      linarith only [hTge, hknn]
    · rw [hwim]
      simp only [Complex.one_im]
      linarith only [hTge, hknn]
  exact
    ⟨mem_dirichletLFunctionSingularitiesInRectangle_iff.mpr ⟨h0mem, Or.inl rfl⟩,
      mem_dirichletLFunctionSingularitiesInRectangle_iff.mpr ⟨h1mem, Or.inr (Or.inl rfl)⟩⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
