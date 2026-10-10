/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.GoodHeight
public import PseudoPrime.AnalyticNumberTheory.General.WeightedLogarithmicResidues
public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.LocalResidueAssembly
public import PseudoPrime.Analysis.FiniteSumExhaustion

/-!
# Finite rectangle residues and absolutely convergent zero sums

These results supply the analytic weights and finite zero ledgers used when
passing from weighted residue rectangles to an infinite zero sum.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The finite set of zeros of an entire function, nonzero at zero, in the closed
rectangle with corners z and w. Compactness and isolated zeros ensure finiteness.
The set records each zero once; analytic multiplicity is supplied separately
in residue sums. No corner ordering or critical-line hypothesis is required. -/
noncomputable def entireZerosInRectangle {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (z w : ℂ) : Finset ℂ :=
  (finite_entire_zerosOn_compact hF h0 (Rectangle.isCompact_rectangleClosedBox z w)).toFinset

/-- For an entire function nonzero at zero, membership in its finite rectangle
zero set means closed rectangle membership together with vanishing of the function.
The finite-set conversion preserves this defining condition. Use this equivalence
to cover all singularities of a logarithmic derivative. -/
theorem mem_entireZerosInRectangle {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (z w ρ : ℂ) :
    ρ ∈ entireZerosInRectangle hF h0 z w ↔ ρ ∈ Rectangle.rectangleClosedBox z w ∧ F ρ = 0 := by
  exact Set.Finite.mem_toFinset _

/-- If all zeros of an entire function lie in the closed critical strip and
the upper and lower heights tend respectively to positive and negative infinity,
each zero eventually enters the rectangles with real endpoints -1 and 2.
The proof uses the two height limits and the zero's real-part bounds.
This permits nonmonotone good-height exhaustions. -/
theorem eventually_zero_mem_rectangle {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (hs : ∀ ρ : ℂ, F ρ = 0 → ρ.re ∈ Set.Icc (0 : ℝ) 1) (U B : ℕ → ℝ)
    (hU : Filter.Tendsto U Filter.atTop Filter.atTop)
    (hB : Filter.Tendsto B Filter.atTop Filter.atBot) (ρ : ℂ) (hz : F ρ = 0) :
    ∀ᶠ n in Filter.atTop,
      ρ ∈
        entireZerosInRectangle hF h0 (((-1 : ℝ) : ℂ) + B n * Complex.I)
          (((2 : ℝ) : ℂ) + U n * Complex.I) := by
  have hu := hU.eventually (Filter.eventually_gt_atTop ρ.im)
  have hb := hB.eventually (Filter.eventually_lt_atBot ρ.im)
  filter_upwards [hu, hb] with n hun hbn
  apply (mem_entireZerosInRectangle hF h0 _ _ ρ).mpr
  refine ⟨?_, hz⟩
  rw [Rectangle.rectangleClosedBox, Complex.mem_reProdIm]
  have hr := hs ρ hz
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  exact
    ⟨Set.Icc_subset_uIcc ⟨by linarith only [hr.1], by linarith only [hr.2]⟩,
      Set.Icc_subset_uIcc ⟨hbn.le, hun.le⟩⟩

/-- For an entire function nonzero at zero with all zeros in the critical strip,
an absolutely summable multiplicity-weighted family is the limit of its finite
rectangle sums as the two heights tend to opposite infinities. Every nonzero term
comes from a zero and eventually enters the ledger. Dominated convergence for
finite exhaustions identifies the limit without assuming nested rectangles. -/
theorem tendsto_rectangle_zero_sum {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (hs : ∀ ρ : ℂ, F ρ = 0 → ρ.re ∈ Set.Icc (0 : ℝ) 1) (W : ℂ → ℂ)
    (hw : Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℂ) * W ρ)) (U B : ℕ → ℝ)
    (hU : Filter.Tendsto U Filter.atTop Filter.atTop)
    (hB : Filter.Tendsto B Filter.atTop Filter.atBot) :
    Filter.Tendsto
      (fun n ↦
        ∑
          ρ ∈
            entireZerosInRectangle hF h0 (((-1 : ℝ) : ℂ) + B n * Complex.I)
              (((2 : ℝ) : ℂ) + U n * Complex.I),
          (analyticOrderNatAt F ρ : ℂ) * W ρ)
      Filter.atTop (nhds (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * W ρ)) := by
  apply PseudoPrime.Analysis.tendsto_sum_of_eventually_mem_support _ hw.norm
  intro ρ hn
  have hm : analyticOrderNatAt F ρ ≠ 0 := by
    intro hm
    apply hn
    rw [hm, Nat.cast_zero, zero_mul]
  exact
    eventually_zero_mem_rectangle hF h0 hs U B hU hB ρ
      (apply_eq_zero_of_analyticOrderNatAt_ne_zero hm)

/-- For entire F nonzero at zero and an entire weight W, an ordered rectangle
whose zero ledger is interior has boundary integral of -logDeriv F times W
equal to 2*pi*i times the negative multiplicity-weighted zero sum.
Finite analytic orders give local square residue certificates, and rectangle
assembly sums them. This is the finite stage before taking contour limits. -/
theorem weighted_entire_finite_contour {F W : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (hW : Differentiable ℂ W) {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    (hopen : ∀ ρ ∈ entireZerosInRectangle hF h0 z w, ρ ∈ RectangleGeometry.rectangleOpenBox z w) :
    RectangleGeometry.rectangleBoundaryIntegral (fun s ↦ -logDeriv F s * W s) z w =
      ∑ ρ ∈ entireZerosInRectangle hF h0 z w,
        2 * Real.pi * Complex.I * (-(analyticOrderNatAt F ρ : ℂ) * W ρ) := by
  apply
    RectangleGeometry.rectangleBoundaryIntegral_eq_sum_of_local_residues _ _ _ hre him
      (fun ρ hρ ↦ (mem_entireZerosInRectangle hF h0 z w ρ).mp hρ |>.1) hopen
  · intro s hs hn
    have hf : F s ≠ 0 := fun hz ↦ hn ((mem_entireZerosInRectangle hF h0 z w s).mpr ⟨hs, hz⟩)
    exact
      (((hF.analyticAt s).deriv.div (hF.analyticAt s) hf).neg.mul
          (hW.analyticAt s)).differentiableAt
  · intro ρ _
    obtain ⟨g, hg, hg0, hlog⟩ :=
      exists_logDeriv_local_expansion (hF.analyticAt ρ) (entire_analyticOrderAt_ne_top hF h0 ρ)
    exact exists_radius_weighted_logDeriv_residue hg hg0 (hW.analyticAt ρ) hlog

/-- For an entire function nonzero at zero with zeros in the critical strip,
an entire weight with summable multiplicity-weighted values determines the limit
of its logarithmic-derivative rectangle integrals. Assume ordered heights and
interior zero ledgers along the exhaustion. Apply the finite residue identity
and the finite-sum limit, retaining the sign and factor -2*pi*i.
This connects local residues to the infinite zero side. -/
theorem tendsto_weighted_entire_boundary {F W : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (hW : Differentiable ℂ W) (hs : ∀ ρ : ℂ, F ρ = 0 → ρ.re ∈ Set.Icc (0 : ℝ) 1)
    (hw : Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℂ) * W ρ)) (U B : ℕ → ℝ)
    (hU : Filter.Tendsto U Filter.atTop Filter.atTop)
    (hB : Filter.Tendsto B Filter.atTop Filter.atBot) (horder : ∀ n, B n < U n)
    (hopen :
      ∀ n ρ,
        ρ ∈
            entireZerosInRectangle hF h0 (((-1 : ℝ) : ℂ) + B n * Complex.I)
              (((2 : ℝ) : ℂ) + U n * Complex.I) →
          ρ ∈
            RectangleGeometry.rectangleOpenBox (((-1 : ℝ) : ℂ) + B n * Complex.I)
              (((2 : ℝ) : ℂ) + U n * Complex.I)) :
    Filter.Tendsto
      (fun n ↦
        RectangleGeometry.rectangleBoundaryIntegral (fun s ↦ -logDeriv F s * W s)
          (((-1 : ℝ) : ℂ) + B n * Complex.I) (((2 : ℝ) : ℂ) + U n * Complex.I))
      Filter.atTop
      (nhds (-(2 * Real.pi * Complex.I) * ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * W ρ)) := by
  have ht :=
    (tendsto_rectangle_zero_sum hF h0 hs W hw U B hU hB).const_mul (-(2 * Real.pi * Complex.I))
  apply ht.congr
  intro n
  have hre : ((((-1 : ℝ) : ℂ) + B n * Complex.I)).re < ((((2 : ℝ) : ℂ) + U n * Complex.I)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    norm_num only
  have him : ((((-1 : ℝ) : ℂ) + B n * Complex.I)).im < ((((2 : ℝ) : ℂ) + U n * Complex.I)).im := by
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, zero_add, add_zero] using horder n
  rw [weighted_entire_finite_contour hF h0 hW hre him (hopen n), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

/-- For an entire function nonzero at zero whose zeros lie in the critical strip,
the zeros in a rectangle with real endpoints -1 and 2 are interior if its ordered
horizontal sides contain no zeros. Real-part bounds exclude the vertical sides,
and horizontal nonvanishing makes the closed height bounds strict.
This discharges the interior-ledger premise for good-height contours. -/
theorem entireZerosInRectangle_subset_open {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (hs : ∀ ρ : ℂ, F ρ = 0 → ρ.re ∈ Set.Icc (0 : ℝ) 1) (U B : ℝ) (horder : B < U)
    (hboundary : ∀ s : ℂ, (s.im = U ∨ s.im = B) → -1 ≤ s.re → s.re ≤ 2 → F s ≠ 0) :
    ∀
      ρ ∈
        entireZerosInRectangle hF h0 (((-1 : ℝ) : ℂ) + B * Complex.I)
          (((2 : ℝ) : ℂ) + U * Complex.I),
      ρ ∈
        RectangleGeometry.rectangleOpenBox (((-1 : ℝ) : ℂ) + B * Complex.I)
          (((2 : ℝ) : ℂ) + U * Complex.I) := by
  intro ρ hρ
  obtain ⟨hr, hz⟩ := (mem_entireZerosInRectangle hF h0 _ _ ρ).mp hρ
  have hr' := hs ρ hz
  have hlo : (-1 : ℝ) < ρ.re := by linarith only [hr'.1]
  have hhi : ρ.re < (2 : ℝ) := by linarith only [hr'.2]
  have hneqU : ρ.im ≠ U := fun heq ↦ hboundary ρ (Or.inl heq) hlo.le hhi.le hz
  have hneqB : ρ.im ≠ B := fun heq ↦ hboundary ρ (Or.inr heq) hlo.le hhi.le hz
  have him : ρ.im ∈ Set.Icc B U := by
    rw [Rectangle.rectangleClosedBox, Complex.mem_reProdIm] at hr
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, zero_add, add_zero, Set.uIcc_of_le horder.le] using hr.2
  rw [RectangleGeometry.rectangleOpenBox, Complex.mem_reProdIm]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  rw [min_eq_left (by norm_num only : (-1 : ℝ) ≤ 2), max_eq_right (by norm_num only : (-1 : ℝ) ≤ 2),
    min_eq_left horder.le, max_eq_right horder.le]
  exact ⟨⟨hlo, hhi⟩, ⟨lt_of_le_of_ne him.1 hneqB.symm, lt_of_le_of_ne him.2 hneqU⟩⟩

end PseudoPrime.AnalyticNumberTheory.General
