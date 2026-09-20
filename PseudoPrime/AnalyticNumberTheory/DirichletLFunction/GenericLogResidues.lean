/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogHorizontalEdge
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogLeftVertical
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ContourRegularity
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLogExplicitFormula
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogResidueLedger
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogContourRectangle

/-! Generic GRH boundary limits and exact logarithmic residue identities. -/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-!
Input/assumptions: generic GRH height data, a primitive nontrivial character, `x ≥ 1`, and `A ≥ 2`.
Conclusion: the normalized generic logarithmic rectangle boundary converges along the height
sequence to the character log-weighted sum minus the left-vertical whole-line integral.
Content: expand the four rectangle edges, then combine generic horizontal decay, right-edge
interval exhaustion, and the generic left-vertical height-sequence limit.
Role: fixed-`A` normalized boundary interface for the generic logarithmic raw bound.
-/

theorem tendsto_normalized_dirichletLogBoundary_heightSeq_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (A : ℕ)
    (hA : 2 ≤ A) :
    Filter.Tendsto
      (fun k : ℕ =>
        (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
            (primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k))
      Filter.atTop
      (nhds
        (Arithmetic.characterLogWeightedSum x χ -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            ∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hcoeffI : (-Complex.I / (2 * (Real.pi : ℂ))) * Complex.I = ((2 * Real.pi : ℝ)⁻¹ : ℂ) := by
    rw [div_mul_eq_mul_div,
      show (-Complex.I) * Complex.I = 1 from by
        rw [neg_mul, Complex.I_mul_I]; ring]
    push_cast
    ring
  have heq :
    ∀ k : ℕ,
      (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
            (primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k) =
        (-Complex.I / (2 * (Real.pi : ℂ))) *
              ((∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k *
                        Complex.I)) -
                ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k *
                        Complex.I)) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t in
                (-(primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv
                    k))..(primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k),
                dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t in
              (-(primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv
                  k))..(primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k),
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    intro k
    obtain ⟨hzre, hzim, hwre, hwim, _, _⟩ :=
      primitiveHeightSeqRectangleFacts_of_grh hN2 hGRH hprimitive hne hinv A k hA
    unfold RectangleGeometry.rectangleBoundaryIntegral
    rw [hzre, hzim, hwre, hwim, primitiveReciprocalLeftRe]
    simp only [smul_eq_mul, Complex.ofReal_neg, neg_mul]
    linear_combination
      (∫ t in
            (-(primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv
                k))..(primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k),
            dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) *
          hcoeffI -
        (∫ t in
            (-(primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv
                k))..(primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k),
            dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
          hcoeffI
  apply Filter.Tendsto.congr (fun k => (heq k).symm)
  have hhoriz :=
    tendsto_primitiveHorizontalHeightSeq_logKernel_horizontal_integral_of_grh A hA hN2 hGRH
      hprimitive hne hinv hx
  have hright :=
    (tendsto_intervalIntegral_dirichletLogContourKernel hxpos χ hne
          (show (1 : ℝ) < 2 by norm_num only)).comp
      (tendsto_primitiveHorizontalHeightSeq_atTop_of_grh hN2 hGRH hprimitive hne hinv)
  have hleft :=
    tendsto_primitiveHorizontalHeightSeq_log_leftVertical_intervalIntegral hN2 hGRH hprimitive hne
      hinv hxpos hA
  have hweighted := characterLogWeightedSum_eq_integral χ hxpos (show (1 : ℝ) < 2 by norm_num only)
  have htarget :
    Filter.Tendsto
      (fun k : ℕ =>
        (-Complex.I / (2 * (Real.pi : ℂ))) *
              ((∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k *
                        Complex.I)) -
                ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k *
                        Complex.I)) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t in
                (-(primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv
                    k))..(primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k),
                dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t in
              (-(primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv
                  k))..(primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k),
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
      Filter.atTop
      (nhds
        ((-Complex.I / (2 * (Real.pi : ℂ))) * ((0 : ℂ) - 0) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t : ℝ, dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)))) := by
    apply Filter.Tendsto.sub
    · apply Filter.Tendsto.add
      · exact Filter.Tendsto.const_mul _ (hhoriz.2.sub hhoriz.1)
      · exact Filter.Tendsto.const_mul _ hright
    · exact Filter.Tendsto.const_mul _ hleft
  simp only [sub_zero, mul_zero, zero_add] at htarget
  rw [hweighted, Complex.real_smul]
  convert htarget using 2
  push_cast
  ring

/-!
Generic replacement for the even zero-contribution closed form.  The regularization
calculation is character-generic; only the completed-L value at zero is supplied by
the pair-system functional equation API.
-/

theorem re_iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_div_two_of_grh {N : ℕ}
    [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    (iteratedDeriv 2 (dirichletLogEvenZeroRegularization x 1 (dirichletEvenZeroLocalFactor χ)) 0 /
          2).re =
      -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
          |primitiveBRe χ| * Real.log x +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
          (Real.pi : ℝ) ^ 2 / 24 -
        (Real.eulerMascheroniConstant / 2) * Real.log x -
        (1 / 2) * Real.log x ^ 2 := by
  rw [iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_eq hprimitive hne hx,
    deriv_logDeriv_dirichletEvenZeroLocalFactor_zero hprimitive hne,
    logDeriv_dirichletEvenZeroLocalFactor_zero hprimitive hne]
  have hF0re :=
    completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log_of_grh hN2 hGRH hprimitive hne
      hinv
  have hlogxC : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := (Complex.ofReal_log hx.le).symm
  have hcomplex :
    (-(2 * (deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0 - (Real.pi : ℂ) ^ 2 / 24) +
            2 *
              (logDeriv (DirichletCharacter.completedLFunction χ) 0 +
                (Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2) *
              Complex.log (x : ℂ) +
            Complex.log (x : ℂ) ^ 2)) /
        2 =
      -deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0 + (Real.pi : ℂ) ^ 2 / 24 -
        logDeriv (DirichletCharacter.completedLFunction χ) 0 * Complex.log (x : ℂ) -
        (Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2 * Complex.log (x : ℂ) -
        Complex.log (x : ℂ) ^ 2 / 2 := by
    ring
  rw [hcomplex, hlogxC]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re]
  have hpi24re : ((Real.pi : ℂ) ^ 2 / 24).re = (Real.pi : ℝ) ^ 2 / 24 := by
    rw [show ((Real.pi : ℂ) ^ 2 / 24) = (((Real.pi : ℝ) ^ 2 / 24 : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.ofReal_re]
  have hAre :
    (logDeriv (DirichletCharacter.completedLFunction χ) 0 * ((Real.log x : ℝ) : ℂ)).re =
      (logDeriv (DirichletCharacter.completedLFunction χ) 0).re * Real.log x := by
    rw [mul_comm, Complex.re_ofReal_mul]
    ring
  have hBre :
    ((Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2 *
          ((Real.log x : ℝ) : ℂ)).re =
      (Real.log Real.pi + Real.eulerMascheroniConstant) / 2 * Real.log x := by
    have heq :
      (Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2 =
        (((Real.log Real.pi + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_log Real.pi_nonneg]
      push_cast
      ring
    rw [heq, mul_comm, Complex.re_ofReal_mul, Complex.ofReal_re]
    ring
  have hSqre : (((Real.log x : ℝ) : ℂ) ^ 2 / 2).re = Real.log x ^ 2 / 2 := by
    rw [show (((Real.log x : ℝ) : ℂ) ^ 2 / 2) = (((Real.log x ^ 2 / 2 : ℝ)) : ℂ) from by
        push_cast; ring,
      Complex.ofReal_re]
  rw [hpi24re, hAre, hBre, hSqre, hF0re]
  ring

/-! For an odd primitive nontrivial character under GRH and `x > 0`, the exact real part
of the logarithmic Mellin regularization's derivative at zero. -/

theorem re_deriv_dirichletLogMellinZeroRegularization_zero_of_odd_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hodd : χ.Odd) {x : ℝ}
    (hx : 0 < x) :
    (deriv (dirichletLogMellinZeroRegularization x χ) 0).re =
      -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
          |primitiveBRe χ| * Real.log x +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
          (Real.pi : ℝ) ^ 2 / 8 -
        (Real.log 2 + Real.eulerMascheroniConstant / 2) * Real.log x := by
  rw [deriv_dirichletLogMellinZeroRegularization_zero_of_odd_eq hprimitive hne hodd hx,
    deriv_logDeriv_LFunction_zero_of_odd hprimitive hne hodd]
  have hΓ0ne : DirichletCharacter.gammaFactor χ 0 ≠ 0 :=
    gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat hodd
      (by
        intro m hm
        have him := congrArg Complex.re hm
        simp only [zero_add] at him
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        norm_num only [Complex.div_re, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat,
          div_self_mul_self', mul_zero, zero_mul, add_zero, zero_add, sub_zero, neg_zero] at him
        have hmneg : -(m : ℝ) ≤ 0 := neg_nonpos.mpr hmnn
        have hhalf : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num only
        have him' : (1 / 2 : ℝ) = -(m : ℝ) := by
          convert him using 1
          norm_num only [Complex.one_re, one_mul]
        exact (not_lt_of_ge hmneg) (him' ▸ hhalf))
  have hdΓ0 : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) 0 :=
    differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat hodd
      (by
        intro m hm
        have him := congrArg Complex.re hm
        simp only [zero_add] at him
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        norm_num only [Complex.div_re, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat,
          div_self_mul_self', mul_zero, zero_mul, add_zero, zero_add, sub_zero, neg_zero] at him
        have hmneg : -(m : ℝ) ≤ 0 := neg_nonpos.mpr hmnn
        have hhalf : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num only
        have him' : (1 / 2 : ℝ) = -(m : ℝ) := by
          convert him using 1
          norm_num only [Complex.one_re, one_mul]
        exact (not_lt_of_ge hmneg) (him' ▸ hhalf))
  have hF0ne := dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  have hbridge0 :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne hF0ne hΓ0ne hdΓ0
  rw [hbridge0]
  have hF0re :=
    completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log_of_grh hN2 hGRH hprimitive hne
      hinv
  have hG0re := logDeriv_gammaFactor_zero_re_of_odd hodd
  have hlogxC : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := (Complex.ofReal_log hx.le).symm
  have hAre :
    ((logDeriv (DirichletCharacter.completedLFunction χ) 0 -
            logDeriv (DirichletCharacter.gammaFactor χ) 0) *
          Complex.log (x : ℂ)).re =
      ((logDeriv (DirichletCharacter.completedLFunction χ) 0).re -
          (logDeriv (DirichletCharacter.gammaFactor χ) 0).re) *
        Real.log x := by
    rw [hlogxC, mul_comm, Complex.re_ofReal_mul, Complex.sub_re, mul_comm]
  have hpi8re : ((Real.pi : ℂ) ^ 2 / 8).re = (Real.pi : ℝ) ^ 2 / 8 := by
    rw [show ((Real.pi : ℂ) ^ 2 / 8) = (((Real.pi : ℝ) ^ 2 / 8 : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.ofReal_re]
  simp only [Complex.sub_re, Complex.neg_re]
  rw [hpi8re, hAre, hF0re, hG0re]
  ring

/-! Generic erased-ledger estimate using the pair-system finite zero-mass bound. -/

theorem re_sum_erased_primitiveLogResidues_le_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) {z w : ℂ} :
    (∑ ρ ∈ ((dirichletLFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0,
          dirichletLogResidueAt hne x ρ).re ≤
      2 * Real.sqrt x * |primitiveBRe χ| := by
  set S := ((dirichletLFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0 with hS_def
  rw [Complex.re_sum]
  have hstep :
    ∀ ρ ∈ S,
      (dirichletLogResidueAt hne x ρ).re ≤
        ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ ρ /
            ρ ^ 2‖ := by
    intro ρ hρ
    rw [dirichletLogResidueAt_eq_zeroContribution_of_mem_erase x hne (hS_def ▸ hρ)]
    have hρ0 : ρ ≠ 0 := (Finset.mem_erase.mp hρ).1
    exact dirichletLFunctionLogZeroContribution_re_le_completedTerm_norm hne hx hρ0
  calc
    ∑ ρ ∈ S, (dirichletLogResidueAt hne x ρ).re ≤
        ∑ ρ ∈ S,
          ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
                (x : ℂ) ^ ρ /
              ρ ^ 2‖ :=
      Finset.sum_le_sum hstep
    _ ≤ 2 * Real.sqrt x * |primitiveBRe χ| :=
      sum_norm_completedLogZeroTerm_le_abs_BRe_of_grh hN2 hGRH hprimitive hne hinv hx S

/-!
Input/assumptions: `N ≥ 2`, a primitive nontrivial quadratic character with `χ⁻¹ ≠ 1`,
GRH, and `y > 0`.
Conclusion: the exact second-derivative formula for the canonical even-zero regularization
at `x = y²`, retaining the negative square-log term.
Proof: specialize the local regularization identity and use `log (y²) = 2 log y`.
No evenness is needed for this algebraic identity; interpreting it as the actual residue of
`L` at zero in the even branch additionally uses evenness.
-/

theorem re_evenLogResidueAt_square_raw {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {y : ℝ} (hy : 0 < y) :
    (iteratedDeriv 2 (dirichletLogEvenZeroRegularization (y ^ 2) 1 (dirichletEvenZeroLocalFactor χ))
            0 /
          2).re =
      -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
          |primitiveBRe χ| * (2 * Real.log y) +
          (1 / 2) * (Real.log N - Real.log Real.pi) * (2 * Real.log y) +
          (Real.pi : ℝ) ^ 2 / 24 -
        (Real.eulerMascheroniConstant / 2) * (2 * Real.log y) -
        (1 / 2) * (2 * Real.log y) ^ 2 := by
  have hraw :=
    re_iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_div_two_raw hN2 hGRH hprimitive hne
      hinv hquad (sq_pos_of_pos hy)
  simpa only [Complex.div_ofNat_re, one_div, Real.log_pow, Nat.cast_ofNat] using hraw

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
