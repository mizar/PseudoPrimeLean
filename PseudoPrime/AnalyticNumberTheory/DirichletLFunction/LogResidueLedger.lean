/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLogResidueClosedForms
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroContribution
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveMultiplicityBridge
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ContourRegularity

/-! General smoothed-contour identities and bounds. -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Designated logarithmic residue contribution for a nontrivial character and real weight `x`.
At zero use half the second derivative of the canonical even regularization with multiplicity
one, or the derivative of the odd Mellin regularization; at one return zero; elsewhere use the
ordinary zero contribution. The definition is total and imposes neither primitivity nor `x > 0`.
The local boundary certificates identify these values with actual residues for primitive
characters and positive `x`, and the finite contour identities sum them over the ledger. -/
noncomputable def dirichletLogResidueAt {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (_hne : χ ≠ 1) (x : ℝ) (s : ℂ) : ℂ := by
  classical
    exact
    if s = 0 then
      if χ.Even then
        iteratedDeriv 2 (dirichletLogEvenZeroRegularization x 1 (dirichletEvenZeroLocalFactor χ))
            0 /
          2
      else deriv (dirichletLogMellinZeroRegularization x χ) 0
    else if s = 1 then 0 else LFunctionLogZeroContribution x χ s

/-- At `s = 0` for an even character, the residue unfolds to half the second derivative
of the canonical even-zero regularization. -/
theorem dirichletLogResidueAt_zero_of_even {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (x : ℝ) (heven : χ.Even) :
    dirichletLogResidueAt hne x 0 =
      iteratedDeriv 2 (dirichletLogEvenZeroRegularization x 1 (dirichletEvenZeroLocalFactor χ)) 0 /
        2 := by
  classical
  unfold dirichletLogResidueAt
  rw [ite_eq_left rfl, ite_eq_left heven]

/-- At `s = 0` for an odd character, the residue unfolds to the odd Mellin regularization's
derivative. -/
theorem dirichletLogResidueAt_zero_of_odd {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (x : ℝ) (hodd : χ.Odd) :
    dirichletLogResidueAt hne x 0 = deriv (dirichletLogMellinZeroRegularization x χ) 0 := by
  classical
  unfold dirichletLogResidueAt
  rw [ite_eq_left rfl, ite_eq_right hodd.not_even]

/-- At `s = 1`, the residue is `0` (the log kernel has no pole there). -/
theorem dirichletLogResidueAt_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1)
    (x : ℝ) : dirichletLogResidueAt hne x 1 = 0 := by
  classical
  unfold dirichletLogResidueAt
  rw [ite_eq_right (by norm_num only), ite_eq_left rfl]

/-- Away from `0` and `1`, the residue unfolds to the ordinary zero contribution. -/
theorem dirichletLogResidueAt_zero_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (x : ℝ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    dirichletLogResidueAt hne x s = LFunctionLogZeroContribution x χ s := by
  classical
  unfold dirichletLogResidueAt
  rw [ite_eq_right hs0, ite_eq_right hs1]

/--
Input/assumptions: `N ≥ 1`, `χ` primitive nontrivial even mod `N`, `x > 0`.
Conclusion: some centered square at zero evaluates the logarithmic boundary integral by `2πi`
times the residue function's value at `0`.
Content: feed the canonical even-zero local regularization identity directly into the generic cubic
Laurent square adapter
(`RectangleGeometry.exists_radius_integral_cubic`),
then convert the nested-`dslope` value to `iteratedDeriv 2 · 0 / 2`
(`PseudoPrime.AnalyticNumberTheory.General.dslope_dslope_same_eq_iteratedDeriv_two_div_two`).
Role: the even half of the `s = 0` local certificate, with no `Classical.choose` witness anywhere.
-/
theorem exists_even_origin_log_residue {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (heven : χ.Even) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
                (RectangleGeometry.centeredSquareLower 0 r)
                (RectangleGeometry.centeredSquareUpper 0 r) =
              2 * Real.pi * Complex.I * dirichletLogResidueAt hne x 0 := by
  rw [dirichletLogResidueAt_zero_of_even hne x heven]
  obtain ⟨hGanalytic, hG0⟩ := evenZeroFactor_analytic_ne_zero hprimitive hne
  have heq := logEven_regularization_canonical (x := x) hprimitive hne heven
  obtain ⟨R, hR, hcert⟩ :=
    RectangleGeometry.exists_radius_integral_cubic
      (analyticAt_logEvenZeroRegularization hx 1 hGanalytic hG0) heq
  refine ⟨R, hR, fun r hr hrR => ?_⟩
  rw [hcert r hr hrR,
    General.dslope_dslope_same_eq_iteratedDeriv_two_div_two
      (analyticAt_logEvenZeroRegularization hx 1 hGanalytic hG0)]

/--
Input/assumptions: `N ≥ 1`, `χ` primitive nontrivial mod `N`, `x > 0`.
Conclusion: some centered square at zero evaluates the logarithmic boundary integral by `2πi`
times the residue function's value at `0`, for either parity.
Role: supplies the local certificate at zero by combining the even and odd boundary identities.
-/
theorem exists_origin_log_residue {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
                (RectangleGeometry.centeredSquareLower 0 r)
                (RectangleGeometry.centeredSquareUpper 0 r) =
              2 * Real.pi * Complex.I * dirichletLogResidueAt hne x 0 := by
  rcases χ.even_or_odd with heven | hodd
  · exact exists_even_origin_log_residue hx hprimitive hne heven
  · rw [dirichletLogResidueAt_zero_of_odd hne x hodd]
    exact exists_log_origin_odd hx hprimitive hne hodd

/--
Input/assumptions: `N ≥ 1`, `χ ≠ 1`, `x > 0`.
Conclusion: some centered square at one has vanishing logarithmic boundary integral.
Content: `L(1,χ) ≠ 0`
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LFunction_one_ne_zero_of_ne_one`),
so continuity gives a whole
neighborhood of `1` (avoiding both `L`'s zero set and `0`) on which the log kernel is
differentiable
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.differentiableAt_logKernel`,
which needs no `s ≠ 1` exclusion,
unlike the reciprocal kernel); Cauchy-Goursat then gives a vanishing boundary integral on every
sufficiently small centered square, matching
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt hne x 1 = 0`.
Role: the `s = 1` local certificate — the log kernel's regularity there makes this simpler than the
reciprocal kernel's Mellin-pole residue at the same point.
-/
theorem exists_one_log_residue {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x) {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
                (RectangleGeometry.centeredSquareLower 1 r)
                (RectangleGeometry.centeredSquareUpper 1 r) =
              2 * Real.pi * Complex.I * dirichletLogResidueAt hne x 1 := by
  rw [dirichletLogResidueAt_one hne x, mul_zero]
  have hL1ne : DirichletCharacter.LFunction χ 1 ≠ 0 := LFunction_one_ne_zero_of_ne_one hne
  have hcont : ContinuousAt (DirichletCharacter.LFunction χ) 1 :=
    (DirichletCharacter.differentiable_LFunction hne).continuous.continuousAt
  have hLnear : ∀ᶠ s in nhds (1 : ℂ), DirichletCharacter.LFunction χ s ≠ 0 :=
    hcont.eventually_ne hL1ne
  have h0near : ∀ᶠ s : ℂ in nhds (1 : ℂ), s ≠ 0 := compl_singleton_mem_nhds (by norm_num only)
  obtain ⟨R0, hR0, hball⟩ := Metric.eventually_nhds_iff.mp (hLnear.and h0near)
  set R := R0 / 2 with hR_def
  have hR : 0 < R := by
    rw [hR_def]; exact div_pos hR0 (by norm_num only)
  refine ⟨R, hR, fun r hr hrR => ?_⟩
  have hsqrt2lt2 : Real.sqrt 2 < 2 := by
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num only)
    nlinarith only [hsq, Real.sqrt_nonneg (2 : ℝ)]
  have hsub :
    Rectangle.rectangleClosedBox (RectangleGeometry.centeredSquareLower 1 r)
        (RectangleGeometry.centeredSquareUpper 1 r) ⊆
      Metric.ball (1 : ℂ) R0 := by
    apply (RectangleGeometry.square_closedBox_subset_closedBall 1 hr.le).trans
    apply Metric.closedBall_subset_ball
    calc
      Real.sqrt 2 * r ≤ Real.sqrt 2 * R := mul_le_mul_of_nonneg_left hrR (Real.sqrt_nonneg 2)
      _ < 2 * R := by exact mul_lt_mul_of_pos_right hsqrt2lt2 hR
      _ = R0 := by
        rw [hR_def]
        ring
  unfold RectangleGeometry.rectangleBoundaryIntegral
  apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn
  intro s hs
  have hsball := hsub hs
  have hh := hball (Metric.mem_ball.mp hsball)
  exact (differentiableAt_logKernel hx hne hh.2 hh.1).differentiableWithinAt

/--
Input/assumptions: `N ≥ 1`, `χ` primitive nontrivial mod `N`, `x > 0`, and `s` a point of the
primitive singularity ledger (`s = 0`, `s = 1`, or an ordinary `L`-zero).
Conclusion: some centered square at `s` evaluates the logarithmic boundary integral by `2πi`
times the residue function's value at `s`.
Content: dispatches on `s = 0`, `s = 1`, or the ordinary-zero case, reusing the log-kernel component
of the existing generic ordinary-zero certificate
(`exists_kernel_zeroContributions`).
Role: the general local certificate (the local boundary step), the direct log-kernel analogue of
`DirichletLFunction.exists_reciprocal_local_residue`.
-/
theorem exists_local_log_residue {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {s : ℂ}
    (hs : s = 0 ∨ s = 1 ∨ DirichletCharacter.LFunction χ s = 0) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
                (RectangleGeometry.centeredSquareLower s r)
                (RectangleGeometry.centeredSquareUpper s r) =
              2 * Real.pi * Complex.I * dirichletLogResidueAt hne x s := by
  rcases hs with rfl | rfl | hzero
  · exact exists_origin_log_residue hx hprimitive hne
  · exact exists_one_log_residue hx hne
  · by_cases hs0 : s = 0
    · subst hs0
      exact exists_origin_log_residue hx hprimitive hne
    · by_cases hs1 : s = 1
      · subst hs1
        exact exists_one_log_residue hx hne
      · rw [dirichletLogResidueAt_zero_ne_one hne x hs0 hs1]
        exact
          (exists_kernel_zeroContributions hx hne hs0 hs1 hzero).imp fun R hR =>
            ⟨hR.1, fun r hr hrR => (hR.2 r hr hrR).2⟩

/--
Once both Mellin points lie in the outer rectangle, the log-kernel residue sum over the whole
primitive singularity ledger splits off the `s = 1` and `s = 0` contributions, leaving only the
ordinary `L`-zero residues. Mirrors
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.splitReciprocalSingularitySum`
exactly.
-/
theorem dirichletSplitLogSingularitySum {N : ℕ} [NeZero N] (x : ℝ) {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {z w : ℂ} (h1 : (1 : ℂ) ∈ LFunctionSingularitiesInRectangle χ hne z w)
    (h0 : (0 : ℂ) ∈ LFunctionSingularitiesInRectangle χ hne z w) :
    ∑ s ∈ LFunctionSingularitiesInRectangle χ hne z w, dirichletLogResidueAt hne x s =
      dirichletLogResidueAt hne x 1 + dirichletLogResidueAt hne x 0 +
        ∑ ρ ∈ ((LFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0,
          dirichletLogResidueAt hne x ρ := by
  classical
  have h0' : (0 : ℂ) ∈ (LFunctionSingularitiesInRectangle χ hne z w).erase 1 :=
    Finset.mem_erase.mpr ⟨by norm_num only, h0⟩
  rw [← Finset.add_sum_erase _ _ h1, ← Finset.add_sum_erase _ _ h0']
  ring

/--
Every point of the twice-erased singularity ledger is an ordinary `L`-zero away from both Mellin
points, so its residue is the plain log zero contribution. Mirrors
`DirichletLFunction.reciprocalResidue_eq_erased_zeroTerm`.
-/
theorem logResidue_eq_zeroTerm_of_erased {N : ℕ} [NeZero N] (x : ℝ) {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {z w : ℂ} {ρ : ℂ}
    (hρ : ρ ∈ ((LFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0) :
    dirichletLogResidueAt hne x ρ = LFunctionLogZeroContribution x χ ρ := by
  have hρ0 : ρ ≠ 0 := (Finset.mem_erase.mp hρ).1
  have hρ1 : ρ ≠ 1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hρ)).1
  exact dirichletLogResidueAt_zero_ne_one hne x hρ0 hρ1

/-- Generic erased-ledger estimate using the pair-system finite zero-mass bound. -/
theorem logResidue_erased_re_sum_le_GRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) {z w : ℂ} :
    (∑ ρ ∈ ((LFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0,
          dirichletLogResidueAt hne x ρ).re ≤
      2 * Real.sqrt x * |primitiveBRe χ| := by
  set S := ((LFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0 with hS_def
  rw [Complex.re_sum]
  have hstep :
    ∀ ρ ∈ S,
      (dirichletLogResidueAt hne x ρ).re ≤
        ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ ρ /
            ρ ^ 2‖ := by
    intro ρ hρ
    rw [logResidue_eq_zeroTerm_of_erased x hne (hS_def ▸ hρ)]
    have hρ0 : ρ ≠ 0 := (Finset.mem_erase.mp hρ).1
    exact logZeroTerm_re_le_completedNorm hne hx hρ0
  calc
    ∑ ρ ∈ S, (dirichletLogResidueAt hne x ρ).re ≤
        ∑ ρ ∈ S,
          ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
                (x : ℂ) ^ ρ /
              ρ ^ 2‖ :=
      Finset.sum_le_sum hstep
    _ ≤ 2 * Real.sqrt x * |primitiveBRe χ| :=
      sum_norm_logZeroTerm_le_abs_BRe hN2 hGRH hprimitive hne hinv hx S

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
