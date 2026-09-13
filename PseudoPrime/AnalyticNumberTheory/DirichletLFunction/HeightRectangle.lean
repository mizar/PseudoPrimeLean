/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveHorizontalLogDerivBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ContourRegularity
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LeftVerticalNonvanishing
import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.Boundary

/-! # Kernel-independent height and rectangle constructions -/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The fixed left real part `λ_A := -A - 1/2` of the left-vertical edge. -/
noncomputable def primitiveReciprocalLeftRe (A : ℕ) : ℝ :=
  -(A : ℝ) - 1 / 2

/-- The lower-left corner of the shared-height rectangle. -/
noncomputable def primitiveReciprocalLowerCorner {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) (A k : ℕ) :
    ℂ :=
  ((primitiveReciprocalLeftRe A : ℝ) : ℂ) -
    (primitiveHorizontalHeightSeq hN2 hGRH
          hprimitive hne hinv hquad k :
        ℂ) *
      Complex.I

/-- The upper-right corner of the shared-height rectangle. -/
noncomputable def primitiveReciprocalUpperCorner {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) (k : ℕ) :
    ℂ :=
  ((2 : ℝ) : ℂ) +
    (primitiveHorizontalHeightSeq hN2 hGRH
          hprimitive hne hinv hquad k :
        ℂ) *
      Complex.I

/-! Generic (`hquad`-free) rectangle corners for the GRH height sequence. -/

noncomputable def primitiveHeightSeqLowerCorner_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A k : ℕ) : ℂ :=
  ((primitiveReciprocalLeftRe A : ℝ) : ℂ) -
    (primitiveHorizontalHeightSeq_of_grh hN2
          hGRH hprimitive hne hinv k :
        ℂ) *
      Complex.I

noncomputable def primitiveHeightSeqUpperCorner_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) : ℂ :=
  ((2 : ℝ) : ℂ) +
    (primitiveHorizontalHeightSeq_of_grh hN2
          hGRH hprimitive hne hinv k :
        ℂ) *
      Complex.I

/-! The following coordinate proof intentionally uses simplification to expose
the complex components. -/

/-- Real and imaginary coordinates, together with strict rectangle orientation
for generic corners. -/
theorem primitiveHeightSeqRectangleFacts_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A k : ℕ) (hA : 2 ≤ A) :
    (primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k).re =
        primitiveReciprocalLeftRe A ∧
      (primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k).im =
        -(primitiveHorizontalHeightSeq_of_grh
            hN2 hGRH hprimitive hne hinv k) ∧
      (primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k).re = 2 ∧
      (primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k).im =
        primitiveHorizontalHeightSeq_of_grh hN2
          hGRH hprimitive hne hinv k ∧
      (primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k).re <
        (primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k).re ∧
      (primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k).im <
        (primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k).im := by
  have hTge :=
    primitiveHorizontalHeightSeq_ge_of_grh hN2
      hGRH hprimitive hne hinv k
  have hTpos :
    (0 : ℝ) <
      primitiveHorizontalHeightSeq_of_grh hN2
        hGRH hprimitive hne hinv k := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num only [primitiveHeightSeqLowerCorner_of_grh, primitiveReciprocalLeftRe, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      mul_one, sub_self, add_zero]
    ring
  · norm_num only [primitiveHeightSeqLowerCorner_of_grh, Complex.sub_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
      zero_add, sub_zero, zero_sub]
  · norm_num only [primitiveHeightSeqUpperCorner_of_grh, RCLike.ofNat_re, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      mul_one, add_zero]
  · norm_num only [primitiveHeightSeqUpperCorner_of_grh, RCLike.ofNat_im, Complex.add_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
      mul_zero, add_zero, zero_add, sub_zero, zero_sub]
  · rw [primitiveHeightSeqLowerCorner_of_grh, primitiveHeightSeqUpperCorner_of_grh,
      primitiveReciprocalLeftRe]
    norm_num only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    linarith
  · rw [primitiveHeightSeqLowerCorner_of_grh, primitiveHeightSeqUpperCorner_of_grh]
    norm_num only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    linarith [hTpos]

/-- Generic GRH height-sequence horizontal edges contain no ordinary `L`-zeros. -/
theorem dirichletLFunction_ne_zero_of_im_eq_primitiveHeightSeq_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) {s : ℂ}
    (him :
      s.im =
          primitiveHorizontalHeightSeq_of_grh
            hN2 hGRH hprimitive hne hinv k ∨
        s.im =
          -(primitiveHorizontalHeightSeq_of_grh
              hN2 hGRH hprimitive hne hinv k)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  intro hL
  have hTge :=
    primitiveHorizontalHeightSeq_ge_of_grh hN2
      hGRH hprimitive hne hinv k
  have hTpos :
    (0 : ℝ) <
      primitiveHorizontalHeightSeq_of_grh hN2
        hGRH hprimitive hne hinv k := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have himne : s.im ≠ 0 := by
    rcases him with h | h
    · rw [h]; exact hTpos.ne'
    · rw [h]; exact (neg_lt_zero.mpr hTpos).ne
  have hΓne : DirichletCharacter.gammaFactor χ s ≠ 0 :=
    gammaFactor_ne_zero_of_im_ne_zero himne
  have hFeq :=
    dirichletLFunction_eq_completed_div_gammaFactor
      χ s
      (Or.inr
        (dirichletCharacter_level_ne_one_of_ne_one
          hne))
  have hFzero : DirichletCharacter.completedLFunction χ s = 0 := by
    apply (div_eq_zero_iff.mp (hFeq ▸ hL)).resolve_right hΓne
  by_cases hre0 : s.re ≤ 0
  · have hs1re : (1 : ℝ) ≤ (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re, le_sub_self_iff]
      linarith
    exact
      completedLFunction_ne_zero_farLeft
        hprimitive hne hinv hs1re hFzero
  · rw [not_le] at hre0
    by_cases hre1 : (1 : ℝ) ≤ s.re
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) hre1 hL
    · rw [not_le] at hre1
      have hhalf := hGRH.zero_re_eq_half N χ hprimitive s hL hre0
      obtain ⟨hpos_ne, hneg_ne⟩ :=
        primitiveHorizontalHeightSeq_completedLFunction_ne_zero_of_grh
          hN2 hGRH hprimitive hne hinv k (by norm_num only : |(1 / 2 : ℝ)| ≤ 2)
      rcases him with h | h
      · apply hpos_ne
        have hseq :
          s =
            ((1 / 2 : ℝ) : ℂ) +
              (primitiveHorizontalHeightSeq_of_grh
                    hN2 hGRH hprimitive hne hinv k :
                  ℂ) *
                Complex.I := by
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
              (primitiveHorizontalHeightSeq_of_grh
                    hN2 hGRH hprimitive hne hinv k :
                  ℂ) *
                Complex.I := by
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

/-- Every singularity of the generic GRH height-sequence rectangle is interior to that rectangle. -/
theorem primitiveHeightSeq_singularities_mem_open_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A k : ℕ) (hA : 2 ≤ A) :
    ∀
      s ∈
        dirichletLFunctionSingularitiesInRectangle
          χ hne (primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k)
          (primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k),
      s ∈
        RectangleGeometry.rectangleOpenBox
          (primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k)
          (primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k) := by
  intro s hs
  obtain ⟨hrect, hcase⟩ :=
    mem_dirichletLFunctionSingularitiesInRectangle_iff.mp
      hs
  obtain ⟨hzre, hzim, hwre, hwim, hre, him⟩ :=
    primitiveHeightSeqRectangleFacts_of_grh hN2 hGRH hprimitive hne hinv A k hA
  have hTge :=
    primitiveHorizontalHeightSeq_ge_of_grh hN2
      hGRH hprimitive hne hinv k
  have hTpos :
    (0 : ℝ) <
      primitiveHorizontalHeightSeq_of_grh hN2
        hGRH hprimitive hne hinv k := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  apply
    RectangleGeometry.mem_rectangleOpenBox_of_mem_closedBox_of_ne
      hre him hrect
  · rcases hcase with hs0 | hs1 | hLzero
    · rw [hs0, hzre, primitiveReciprocalLeftRe]
      simp only [Complex.zero_re, one_div, ne_eq]
      linarith
    · rw [hs1, hzre, primitiveReciprocalLeftRe]
      simp only [Complex.one_re, one_div, ne_eq]
      linarith
    · rw [hzre]
      intro heq
      have hseq : s = ((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (s.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp only [← heq, Complex.re_add_im]
      rw [primitiveReciprocalLeftRe] at hseq
      rw [hseq] at hLzero
      exact
        dirichletLFunction_ne_zero_leftVertical
          hprimitive hne hinv A hA s.im hLzero
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
            rw [heq]; norm_num only)
          hLzero
  · rcases hcase with hs0 | hs1 | hLzero
    · rw [hs0, hzim]
      simp only [Complex.zero_im, ne_eq, zero_eq_neg]
      linarith
    · rw [hs1, hzim]
      simp only [Complex.one_im, ne_eq, zero_eq_neg]
      linarith
    · rw [hzim]
      intro heq
      exact
        dirichletLFunction_ne_zero_of_im_eq_primitiveHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k
          (Or.inr heq) hLzero
  · rcases hcase with hs0 | hs1 | hLzero
    · rw [hs0, hwim]
      simpa only [Complex.zero_im, ne_eq] using hTpos.ne
    · rw [hs1, hwim]
      simpa only [Complex.one_im, ne_eq] using hTpos.ne
    · rw [hwim]
      intro heq
      exact
        dirichletLFunction_ne_zero_of_im_eq_primitiveHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k
          (Or.inl heq) hLzero

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`, `s : ℂ`
with `s.im = T_k` or `s.im = -T_k` (any real part).
Conclusion: `LFunction χ s ≠ 0`.
Content: three-way case split on `s.re`. If `s.re ≤ 0`: `s.im ≠ 0` (`T_k ≥ 1`) gives
`gammaFactor χ s ≠ 0` (`DirichletLFunction.gammaFactor_ne_zero_of_im_ne_zero`), so `L(s) = 0` would
force
`completedL(s) = L(s) · gammaFactor(s) = 0`
(`DirichletLFunction.dirichletLFunction_eq_completed_div_gammaFactor`), contradicting far-left
nonvanishing
(`completedLFunction_ne_zero_farLeft`, needs `1 ≤ (1-s).re`, i.e. `s.re ≤ 0`). If
`1 ≤ s.re`: direct contradiction with `DirichletCharacter.LFunction_ne_zero_of_one_le_re`. If
`0 < s.re < 1`: GRH forces `s.re = 1/2`, so `s = 1/2 ± T_k i` exactly, and the same
completedL-vanishing argument contradicts
`DirichletLFunction.primitiveHorizontalHeightSeq_completedLFunction_ne_zero`
at `σ = 1/2` (which covers `|σ| ≤ 2`, in particular `σ = 1/2`).
Role: an `A`-independent horizontal-edge regularity fact — since the two horizontal edges of the
shared-height rectangle are exactly `Im s = ± T_k`, this alone supplies the ordinary-`L`-zero half
of `hopen`
for every `A`.
-/
theorem dirichletLFunction_ne_zero_of_im_eq_primitiveHorizontalHeightSeq {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) (k : ℕ)
    {s : ℂ}
    (him :
      s.im =
          primitiveHorizontalHeightSeq hN2 hGRH
            hprimitive hne hinv hquad k ∨
        s.im =
          -(primitiveHorizontalHeightSeq hN2
              hGRH hprimitive hne hinv hquad k)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  intro hL
  have hTge :=
    primitiveHorizontalHeightSeq_ge hN2 hGRH
      hprimitive hne hinv hquad k
  have hTpos :
    (0 : ℝ) <
      primitiveHorizontalHeightSeq hN2 hGRH
        hprimitive hne hinv hquad k := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have himne : s.im ≠ 0 := by
    rcases him with h | h
    · rw [h]; exact hTpos.ne'
    · rw [h]; exact (neg_lt_zero.mpr hTpos).ne
  have hΓne : DirichletCharacter.gammaFactor χ s ≠ 0 :=
    gammaFactor_ne_zero_of_im_ne_zero himne
  have hFeq :=
    dirichletLFunction_eq_completed_div_gammaFactor
      χ s
      (Or.inr
        (dirichletCharacter_level_ne_one_of_ne_one
          hne))
  have hL' : DirichletCharacter.completedLFunction χ s / DirichletCharacter.gammaFactor χ s = 0 :=
    hFeq ▸ hL
  have hFzero : DirichletCharacter.completedLFunction χ s = 0 :=
    (div_eq_zero_iff.mp hL').resolve_right hΓne
  by_cases hre0 : s.re ≤ 0
  · have hs1re : (1 : ℝ) ≤ (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re, le_sub_self_iff]
      linarith
    exact
      completedLFunction_ne_zero_farLeft
        hprimitive hne hinv hs1re hFzero
  · rw [not_le] at hre0
    by_cases hre1 : (1 : ℝ) ≤ s.re
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) hre1 hL
    · rw [not_le] at hre1
      have hhalf := hGRH.zero_re_eq_half N χ hprimitive s hL hre0
      have hσ : |(1 / 2 : ℝ)| ≤ 2 := by norm_num only
      obtain ⟨hpos_ne, hneg_ne⟩ :=
        primitiveHorizontalHeightSeq_completedLFunction_ne_zero
          hN2 hGRH hprimitive hne hinv hquad k hσ
      rcases him with h | h
      · apply hpos_ne
        have hseq :
          s =
            ((1 / 2 : ℝ) : ℂ) +
              (primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k :
                  ℂ) *
                Complex.I := by
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
              (primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k :
                  ℂ) *
                Complex.I := by
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

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`, `A ≥ 2`,
`k : ℕ`.
Conclusion: every primitive singularity in the closed height-sequence rectangle
`[λ_A - i T_k, 2 + i T_k]` actually lies in its open interior.
Content: `RectangleGeometry.mem_rectangleOpenBox_of_mem_closedBox_of_ne` reduces this to four
coordinate-avoidance
facts, split via three cases on the singularity kind. `s = 0` and `s = 1`: direct numeric bounds
(`λ_A < 0, 1 < 2` and `-T_k < 0 < T_k`, using `A ≥ 2` and
`DirichletLFunction.primitiveHorizontalHeightSeq_ge`). Ordinary `L`-zero: closed-rectangle
membership gives the
non-strict bounds; strictness on the left edge follows from
`quadraticDirichletLFunction_ne_zero_leftVertical` (`L ≠ 0` at `Re s = λ_A`), on the right edge from
`DirichletCharacter.LFunction_ne_zero_of_one_le_re` (`Re s = 2 ≥ 1`), and on the top/bottom edges
from `dirichletLFunction_ne_zero_of_im_eq_primitiveHorizontalHeightSeq` (this file).
Role: **the shared-height argument `hopen` certificate**, feeding
`DirichletLFunction.dirichletReciprocalFiniteContourIdentity`
uniformly in `A` for the height-sequence rectangle.
-/
theorem primitiveHorizontalHeightSeq_singularities_mem_open {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) (A k : ℕ)
    (hA : 2 ≤ A) :
    ∀
      s ∈
        dirichletLFunctionSingularitiesInRectangle
          χ hne (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k)
          (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k),
      s ∈
        RectangleGeometry.rectangleOpenBox
          (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k)
          (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k) := by
  intro s hs
  set z := primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k with hz_def
  set w := primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k with hw_def
  obtain ⟨hrect, hcase⟩ :=
    mem_dirichletLFunctionSingularitiesInRectangle_iff.mp
      hs
  have hzre : z.re = primitiveReciprocalLeftRe A := by
    rw [hz_def, primitiveReciprocalLowerCorner]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero]
  have hzim :
    z.im =
      -(primitiveHorizontalHeightSeq hN2 hGRH
          hprimitive hne hinv hquad k) := by
    rw [hz_def, primitiveReciprocalLowerCorner]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.I_re, mul_zero, add_zero, zero_sub]
  have hwre : w.re = 2 := by
    rw [hw_def, primitiveReciprocalUpperCorner]
    simp only [Complex.ofReal_ofNat, Complex.add_re, Complex.re_ofNat, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
      add_zero]
  have hwim :
    w.im =
      primitiveHorizontalHeightSeq hN2 hGRH
        hprimitive hne hinv hquad k := by
    rw [hw_def, primitiveReciprocalUpperCorner]
    simp only [Complex.ofReal_ofNat, Complex.add_im, Complex.im_ofNat, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero,
      zero_add]
  have hTge :=
    primitiveHorizontalHeightSeq_ge hN2 hGRH
      hprimitive hne hinv hquad k
  have hTpos :
    (0 : ℝ) <
      primitiveHorizontalHeightSeq hN2 hGRH
        hprimitive hne hinv hquad k := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hre_lt : z.re < w.re := by
    rw [hzre, hwre, primitiveReciprocalLeftRe]; linarith
  have him_lt : z.im < w.im := by
    rw [hzim, hwim]; linarith
  apply
    RectangleGeometry.mem_rectangleOpenBox_of_mem_closedBox_of_ne
      hre_lt him_lt hrect
  · rcases hcase with hs0 | hs1 | hLzero
    · rw [hs0, hzre, primitiveReciprocalLeftRe]
      simp only [Complex.zero_re, one_div, ne_eq]
      linarith
    · rw [hs1, hzre, primitiveReciprocalLeftRe]
      simp only [Complex.one_re, one_div, ne_eq]
      linarith
    · rw [hzre]
      intro heq
      have hseq : s = ((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (s.im : ℂ) * Complex.I := by
        apply Complex.ext
        · simp only [← heq, Complex.re_add_im]
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
      rw [primitiveReciprocalLeftRe] at hseq
      rw [hseq] at hLzero
      exact
        quadraticDirichletLFunction_ne_zero_leftVertical
          hprimitive hne hquad A hA s.im hLzero
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
            rw [heq]; norm_num only)
          hLzero
  · rcases hcase with hs0 | hs1 | hLzero
    · rw [hs0, hzim]
      simp only [Complex.zero_im, ne_eq, zero_eq_neg]
      linarith
    · rw [hs1, hzim]
      simp only [Complex.one_im, ne_eq, zero_eq_neg]
      linarith
    · rw [hzim]
      intro heq
      exact
        dirichletLFunction_ne_zero_of_im_eq_primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne
          hinv hquad k (Or.inr heq) hLzero
  · rcases hcase with hs0 | hs1 | hLzero
    · rw [hs0, hwim]
      simpa only [Complex.zero_im, ne_eq] using hTpos.ne
    · rw [hs1, hwim]
      simpa only [Complex.one_im, ne_eq] using hTpos.ne
    · rw [hwim]
      intro heq
      exact
        dirichletLFunction_ne_zero_of_im_eq_primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne
          hinv hquad k (Or.inl heq) hLzero

/-- Common geometric facts about the height-sequence rectangle's corners, spelled out once so
downstream `hopen`/contour-identity proofs don't each redo the four `rw`+`simp?` unfoldings. -/
theorem primitiveReciprocalCorners_facts {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) (A k : ℕ)
    (hA : 2 ≤ A) :
    (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k).re =
        primitiveReciprocalLeftRe A ∧
      (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k).im =
        -(primitiveHorizontalHeightSeq hN2 hGRH
            hprimitive hne hinv hquad k) ∧
      (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k).re = 2 ∧
      (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k).im =
        primitiveHorizontalHeightSeq hN2 hGRH
          hprimitive hne hinv hquad k ∧
      (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k).re <
        (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k).re ∧
      (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k).im <
        (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k).im := by
  have hzre :
    (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k).re =
      primitiveReciprocalLeftRe A := by
    rw [primitiveReciprocalLowerCorner]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero]
  have hzim :
    (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k).im =
      -(primitiveHorizontalHeightSeq hN2 hGRH
          hprimitive hne hinv hquad k) := by
    rw [primitiveReciprocalLowerCorner]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.I_re, mul_zero, add_zero, zero_sub]
  have hwre : (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k).re = 2 := by
    rw [primitiveReciprocalUpperCorner]
    simp only [Complex.ofReal_ofNat, Complex.add_re, Complex.re_ofNat, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
      add_zero]
  have hwim :
    (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k).im =
      primitiveHorizontalHeightSeq hN2 hGRH
        hprimitive hne hinv hquad k := by
    rw [primitiveReciprocalUpperCorner]
    simp only [Complex.ofReal_ofNat, Complex.add_im, Complex.im_ofNat, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero,
      zero_add]
  have hTge :=
    primitiveHorizontalHeightSeq_ge hN2 hGRH
      hprimitive hne hinv hquad k
  have hTpos :
    (0 : ℝ) <
      primitiveHorizontalHeightSeq hN2 hGRH
        hprimitive hne hinv hquad k := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  refine ⟨hzre, hzim, hwre, hwim, ?_, ?_⟩
  · rw [hzre, hwre, primitiveReciprocalLeftRe]; linarith
  · rw [hzim, hwim]; linarith

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`, `A ≥ 2`.
Conclusion: both Mellin points `0` and `1` lie in the height-sequence rectangle's primitive
singularity ledger.
Content: `0` and `1` both lie in the open (hence closed) rectangle `(λ_A, -T_k), (2, T_k)`, since
`λ_A < 0 < 1 < 2` (`A ≥ 2`) and `-T_k < 0 < T_k`
(`DirichletLFunction.primitiveHorizontalHeightSeq_ge`).
Role: supplies the two membership hypotheses needed by
`DirichletLFunction.dirichletSplitReciprocalSingularitySum`
to split the residue sum into `r(1) + r(0) + (ordinary-zero sum)`.
-/
theorem primitiveReciprocalMellinPoints_mem_singularities_heightSeq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) (A k : ℕ)
    (hA : 2 ≤ A) :
    (0 : ℂ) ∈
        dirichletLFunctionSingularitiesInRectangle
          χ hne (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k)
          (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k) ∧
      (1 : ℂ) ∈
        dirichletLFunctionSingularitiesInRectangle
          χ hne (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k)
          (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k) := by
  obtain ⟨hzre, hzim, hwre, hwim, hre, him⟩ :=
    primitiveReciprocalCorners_facts hN2 hGRH hprimitive hne hinv hquad A k hA
  set z := primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k
  set w := primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have h0mem :
    (0 : ℂ) ∈
      dirichletCompletedLFunctionRectangleBox z
        w := by
    rw [dirichletCompletedLFunctionRectangleBox,
      Rectangle.rectangleClosedBox, Complex.mem_reProdIm]
    refine ⟨Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩), Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩)⟩
    · rw [hzre, primitiveReciprocalLeftRe]
      simp only [one_div, Complex.zero_re, tsub_le_iff_right, zero_add]
      linarith
    · rw [hwre]
      change (0 : ℝ) ≤ 2
      norm_num only
    · rw [hzim]
      change
        -primitiveHorizontalHeightSeq hN2 hGRH
              hprimitive hne hinv hquad k ≤
          0
      linarith
    · rw [hwim]
      change
        (0 : ℝ) ≤
          primitiveHorizontalHeightSeq hN2 hGRH
            hprimitive hne hinv hquad k
      linarith
  have h1mem :
    (1 : ℂ) ∈
      dirichletCompletedLFunctionRectangleBox z
        w := by
    rw [dirichletCompletedLFunctionRectangleBox,
      Rectangle.rectangleClosedBox, Complex.mem_reProdIm]
    refine ⟨Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩), Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩)⟩
    · rw [hzre, primitiveReciprocalLeftRe]
      simp only [one_div, Complex.one_re, tsub_le_iff_right]
      linarith
    · rw [hwre]
      change (1 : ℝ) ≤ 2
      norm_num only
    · rw [hzim]
      change
        -primitiveHorizontalHeightSeq hN2 hGRH
              hprimitive hne hinv hquad k ≤
          0
      linarith
    · rw [hwim]
      change
        (0 : ℝ) ≤
          primitiveHorizontalHeightSeq hN2 hGRH
            hprimitive hne hinv hquad k
      linarith
  exact
    ⟨mem_dirichletLFunctionSingularitiesInRectangle_iff.mpr
        ⟨h0mem, Or.inl rfl⟩,
      mem_dirichletLFunctionSingularitiesInRectangle_iff.mpr
        ⟨h1mem, Or.inr (Or.inl rfl)⟩⟩

/-- The Mellin points `0` and `1` belong to the generic GRH height-sequence rectangle. -/
theorem primitiveReciprocalMellinPoints_mem_singularities_heightSeq_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A k : ℕ) (hA : 2 ≤ A) :
    (0 : ℂ) ∈
        dirichletLFunctionSingularitiesInRectangle
          χ hne (primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k)
          (primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k) ∧
      (1 : ℂ) ∈
        dirichletLFunctionSingularitiesInRectangle
          χ hne (primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k)
          (primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k) := by
  obtain ⟨hzre, hzim, hwre, hwim, _, _⟩ :=
    primitiveHeightSeqRectangleFacts_of_grh hN2 hGRH hprimitive hne hinv A k hA
  set z := primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k
  set w := primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hTge :=
    primitiveHorizontalHeightSeq_ge_of_grh hN2
      hGRH hprimitive hne hinv k
  have h0mem :
    (0 : ℂ) ∈
      dirichletCompletedLFunctionRectangleBox z
        w := by
    rw [dirichletCompletedLFunctionRectangleBox,
      Rectangle.rectangleClosedBox, Complex.mem_reProdIm]
    refine ⟨Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩), Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩)⟩
    · rw [hzre, primitiveReciprocalLeftRe]
      simp only [one_div, Complex.zero_re, tsub_le_iff_right, zero_add]
      linarith
    · rw [hwre]
      change (0 : ℝ) ≤ 2
      norm_num only
    · rw [hzim]
      simp only [Complex.zero_im, Left.neg_nonpos_iff]
      linarith
    · rw [hwim]
      simp only [Complex.zero_im]
      linarith
  have h1mem :
    (1 : ℂ) ∈
      dirichletCompletedLFunctionRectangleBox z
        w := by
    rw [dirichletCompletedLFunctionRectangleBox,
      Rectangle.rectangleClosedBox, Complex.mem_reProdIm]
    refine ⟨Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩), Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩)⟩
    · rw [hzre, primitiveReciprocalLeftRe]
      simp only [one_div, Complex.one_re, tsub_le_iff_right]
      linarith
    · rw [hwre]
      change (1 : ℝ) ≤ 2
      norm_num only
    · rw [hzim]
      simp only [Complex.one_im, Left.neg_nonpos_iff]
      linarith
    · rw [hwim]
      simp only [Complex.one_im]
      linarith
  exact
    ⟨mem_dirichletLFunctionSingularitiesInRectangle_iff.mpr
        ⟨h0mem, Or.inl rfl⟩,
      mem_dirichletLFunctionSingularitiesInRectangle_iff.mpr
        ⟨h1mem, Or.inr (Or.inl rfl)⟩⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
