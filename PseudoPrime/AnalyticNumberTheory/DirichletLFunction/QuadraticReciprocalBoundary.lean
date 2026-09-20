/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveContourRectangle
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveMultiplicityBridge
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveResidueClosedForms
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveEvenResidueClosedForm
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveExplicitFormula
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericHorizontalEdge

/-! General smoothed-contour identities and bounds. -/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`, `x > 0`,
`k : ℕ`, a sign `ε ∈ {1, -1}`.
Conclusion: `σ ↦ K_x(σ + ε·T_k·i)` is continuous on all of `ℝ`.
Content: `T_k ≥ 1 > 0` gives `(σ + ε T_k i).im ≠ 0`, hence `≠ 0, 1`; combined with
`DirichletLFunction.dirichletLFunction_ne_zero_of_im_eq_primitiveHorizontalHeightSeq` (`L(s) ≠ 0`),
`DirichletLFunction.differentiableAt_dirichletReciprocalContourKernel` gives `DifferentiableAt` at
every point,
hence continuity.
Role: supplies `IntervalIntegrable` for the horizontal edges at height `±T_k`, needed to split
`[λ_A, 2]` into `[λ_A, -2] + [-2, 2]` and recombine the two already-established `Tendsto → 0`
facts.
-/
theorem continuous_dirichletReciprocalContourKernel_horizontalHeightSeq {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 0 < x) (k : ℕ) :
    Continuous
        (fun σ : ℝ =>
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) +
              primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k * Complex.I)) ∧
      Continuous
        (fun σ : ℝ =>
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) -
              primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k * Complex.I)) := by
  have hTge := primitiveHorizontalHeightSeq_ge hN2 hGRH hprimitive hne hinv hquad k
  have hTpos : (0 : ℝ) < primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hpt :
    ∀ s : ℂ,
      s.im = primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k ∨
          s.im = -(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k) →
        ContinuousAt (dirichletReciprocalContourKernel x χ) s := by
    intro s hsim
    have hsimne : s.im ≠ 0 := by
      rcases hsim with h | h <;> rw [h] <;> [exact hTpos.ne'; exact (neg_lt_zero.mpr hTpos).ne]
    have hs0 : s ≠ 0 := fun h =>
      hsimne
        (by
          rw [h]; simp only [Complex.zero_im])
    have hs1 : s ≠ 1 := fun h =>
      hsimne
        (by
          rw [h]; simp only [Complex.one_im])
    have hLne :=
      dirichletLFunction_ne_zero_of_im_eq_primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv
        hquad k hsim
    exact (differentiableAt_dirichletReciprocalContourKernel hx hne hs0 hs1 hLne).continuousAt
  constructor
  · have hg :
      Continuous
        (fun σ : ℝ =>
          (σ : ℂ) +
            (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k : ℂ) *
              Complex.I) := by
      fun_prop
    have hOn :
      ContinuousOn (dirichletReciprocalContourKernel x χ)
        (Set.range
          (fun σ : ℝ =>
            (σ : ℂ) +
              (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k : ℂ) *
                Complex.I)) := by
      rintro s ⟨σ, rfl⟩
      exact
        (hpt _
            (Or.inl
              (by
                simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
                  Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
                  zero_add]))).continuousWithinAt
    exact hOn.comp_continuous hg (fun σ => Set.mem_range_self σ)
  · have hg :
      Continuous
        (fun σ : ℝ =>
          (σ : ℂ) -
            (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k : ℂ) *
              Complex.I) := by
      fun_prop
    have hOn :
      ContinuousOn (dirichletReciprocalContourKernel x χ)
        (Set.range
          (fun σ : ℝ =>
            (σ : ℂ) -
              (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k : ℂ) *
                Complex.I)) := by
      rintro s ⟨σ, rfl⟩
      exact
        (hpt _
            (Or.inr
              (by
                simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
                  Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
                  zero_sub]))).continuousWithinAt
    exact hOn.comp_continuous hg (fun σ => Set.mem_range_self σ)

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`, `A ≥ 2`,
`x ≥ 1`.
Conclusion: the full-range top and bottom horizontal integrals `∫ σ in λ_A..2, K(σ ± T_k i)` both
tend to `0` along the height sequence.
Content: `intervalIntegral.integral_add_adjacent_intervals` splits `[λ_A, 2]` into `[λ_A, -2] +
[-2, 2]` (the two pieces `IntervalIntegrable` via `Continuous.intervalIntegrable`, fed by
`DirichletLFunction.continuous_dirichletReciprocalContourKernel_horizontalHeightSeq`); the two
summands tend to
`0` individually (the far-left and central bounds), so their sum does too.
Role: the merged horizontal-edge vanishing fact, ready to feed the boundary integral's `k → ∞`
limit.
-/
theorem tendsto_primitiveHorizontalHeightSeq_reciprocalKernel_horizontal_integral (A : ℕ)
    (hA : 2 ≤ A) {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 1 ≤ x) :
    Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k * Complex.I))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k * Complex.I))
        Filter.atTop (nhds 0) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hfarLeft :=
    tendsto_primitiveHorizontalHeightSeq_reciprocalKernel_farLeft_integral A hA hN2 hGRH hprimitive
      hne hinv hquad hx
  have hcentral :=
    tendsto_primitiveHorizontalHeightSeq_reciprocalKernel_central_integral hN2 hGRH hprimitive hne
      hinv hquad hx
  have hcont := fun k : ℕ =>
    continuous_dirichletReciprocalContourKernel_horizontalHeightSeq hN2 hGRH hprimitive hne hinv
      hquad hxpos k
  have hsplit :
    ∀ k : ℕ,
      (∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k * Complex.I)) +
          ∫ σ in (-2 : ℝ)..(2 : ℝ),
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k * Complex.I) =
        ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) +
              primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k * Complex.I) :=
    fun k =>
    intervalIntegral.integral_add_adjacent_intervals
      ((hcont k).1.intervalIntegrable (-(A : ℝ) - 1 / 2) (-2))
      ((hcont k).1.intervalIntegrable (-2) 2)
  have hsplit' :
    ∀ k : ℕ,
      (∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k * Complex.I)) +
          ∫ σ in (-2 : ℝ)..(2 : ℝ),
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k * Complex.I) =
        ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) -
              primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k * Complex.I) :=
    fun k =>
    intervalIntegral.integral_add_adjacent_intervals
      ((hcont k).2.intervalIntegrable (-(A : ℝ) - 1 / 2) (-2))
      ((hcont k).2.intervalIntegrable (-2) 2)
  constructor
  · have := (hfarLeft.1.add hcentral.1)
    simp only [add_zero] at this
    exact this.congr hsplit
  · have := (hfarLeft.2.add hcentral.2)
    simp only [add_zero] at this
    exact this.congr hsplit'

/--
For `N ≥ 2`, a primitive nontrivial quadratic character with nontrivial inverse,
GRH, `x ≥ 1`, and `A ≥ 2`, the normalized reciprocal boundary integral converges
to the weighted character sum minus `(2π)⁻¹` times the whole left-line integral.
The horizontal integrals vanish; the right real-parameter integral tends to `2π*R(x,χ)`,
and the left one tends to its whole-line integral. The vertical orientation factors
and `-i/(2π)` give the displayed normalization. This limit is combined with the
normalized finite contour identity and its residue bounds.
-/
theorem tendsto_normalized_dirichletReciprocalBoundary_heightSeq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 1 ≤ x) (A : ℕ) (hA : 2 ≤ A) :
    Filter.Tendsto
      (fun k : ℕ =>
        (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (dirichletReciprocalContourKernel x χ)
            (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k)
            (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k))
      Filter.atTop
      (nhds
        (Arithmetic.characterReciprocalWeightedSum x χ -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            ∫ t : ℝ,
              dirichletReciprocalContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hpi_ne : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have hpine : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero, hpine, or_self,
      not_false_eq_true]
  have hcoeffI : (-Complex.I / (2 * (Real.pi : ℂ))) * Complex.I = ((2 * Real.pi : ℝ)⁻¹ : ℂ) := by
    rw [div_mul_eq_mul_div,
      show (-Complex.I) * Complex.I = 1 from by
        rw [neg_mul, Complex.I_mul_I]; ring]
    push_cast; ring
  have heq :
    ∀ k : ℕ,
      (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (dirichletReciprocalContourKernel x χ)
            (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k)
            (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k) =
        (-Complex.I / (2 * (Real.pi : ℂ))) *
              ((∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletReciprocalContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)) -
                ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletReciprocalContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t in
                (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
                    k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
                dirichletReciprocalContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t in
              (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
                  k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
              dirichletReciprocalContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    intro k
    have hzre :
      (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k).re =
        primitiveReciprocalLeftRe A := by
      rw [primitiveReciprocalLowerCorner]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero]
    have hzim :
      (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k).im =
        -(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k) := by
      rw [primitiveReciprocalLowerCorner]
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.I_re, mul_zero, add_zero, zero_sub]
    have hwre : (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k).re = 2 := by
      rw [primitiveReciprocalUpperCorner]
      simp only [Complex.ofReal_ofNat, Complex.add_re, Complex.re_ofNat, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
        sub_self, add_zero]
    have hwim :
      (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k).im =
        primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k := by
      rw [primitiveReciprocalUpperCorner]
      simp only [Complex.ofReal_ofNat, Complex.add_im, Complex.im_ofNat, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
        add_zero, zero_add]
    unfold RectangleGeometry.rectangleBoundaryIntegral
    rw [hzre, hzim, hwre, hwim, primitiveReciprocalLeftRe]
    simp only [smul_eq_mul, Complex.ofReal_neg, neg_mul]
    linear_combination
      (∫ t in
            (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
                k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
            dirichletReciprocalContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) *
          hcoeffI -
        (∫ t in
            (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
                k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
            dirichletReciprocalContourKernel x χ
              (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
          hcoeffI
  apply Filter.Tendsto.congr (fun k => (heq k).symm)
  have hhoriz :=
    tendsto_primitiveHorizontalHeightSeq_reciprocalKernel_horizontal_integral A hA hN2 hGRH
      hprimitive hne hinv hquad hx
  have hright :
    Filter.Tendsto
      (fun k : ℕ =>
        ∫ t in
          (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
              k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
          dirichletReciprocalContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (nhds (∫ t : ℝ, dirichletReciprocalContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I))) :=
    (tendsto_intervalIntegral_dirichletReciprocalContourKernel hxpos χ hne
          (show (1 : ℝ) < 2 from by norm_num only)).comp
      (tendsto_primitiveHorizontalHeightSeq_atTop hN2 hGRH hprimitive hne hinv hquad)
  have hleft :=
    quadraticTendsto_primitiveHorizontalHeightSeq_leftVertical_intervalIntegral hN2 hGRH hprimitive
      hne hinv hquad hxpos hA
  have hweighted :=
    characterReciprocalWeightedSum_eq_integral χ hxpos (show (1 : ℝ) < 2 from by norm_num only)
  have htarget :
    Filter.Tendsto
      (fun k : ℕ =>
        (-Complex.I / (2 * (Real.pi : ℂ))) *
              ((∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletReciprocalContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)) -
                ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletReciprocalContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t in
                (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
                    k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
                dirichletReciprocalContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t in
              (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
                  k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
              dirichletReciprocalContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
      Filter.atTop
      (nhds
        ((-Complex.I / (2 * (Real.pi : ℂ))) * ((0 : ℂ) - (0 : ℂ)) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t : ℝ, dirichletReciprocalContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t : ℝ,
              dirichletReciprocalContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)))) := by
    apply Filter.Tendsto.sub
    · apply Filter.Tendsto.add
      · exact (Filter.Tendsto.const_mul _ (hhoriz.2.sub hhoriz.1))
      · exact Filter.Tendsto.const_mul _ hright
    · exact Filter.Tendsto.const_mul _ hleft
  simp only [sub_zero, mul_zero, zero_add] at htarget
  rw [hweighted, Complex.real_smul]
  convert htarget using 2
  push_cast; ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
