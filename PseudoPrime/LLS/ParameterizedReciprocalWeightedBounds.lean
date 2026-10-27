/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrimitiveReciprocalWeightedBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveMultiplicityBridge
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveResidueClosedForms
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveEvenResidueClosedForm
public import PseudoPrime.Analysis.PrimitiveReciprocalMainErrorBounds

/-! # Reciprocal weighted bounds with a parameterized main error

Both parity main errors remain explicit inputs. The contour limits require
only x greater than one, and impose no fixed numerical cutoff.
-/

@[expose] public section

namespace PseudoPrime.LLS

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For x greater than one and the applicable parity main error bounded by e,
the zero and one residues obey the displayed conductor and zero-mass bound.
Apply the exact odd or even closed form. This isolates the numerical error
from the contour argument. -/
theorem primitiveReciprocalOrigin_le_of_parity_mainErrors {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} {e : ℝ} (hx : 1 < x)
    (ho : χ.Odd → Analysis.primitiveReciprocalOddMainError x ≤ e)
    (he : χ.Even → Analysis.primitiveReciprocalEvenMainError x ≤ e) :
    (dirichletReciprocalResidueAt hne x 0 + dirichletReciprocalResidueAt hne x 1).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - (1 + 1 / x) * |primitiveBRe χ| +
        e := by
  have hxpos : (0 : ℝ) < x := by linarith only [hx]
  rcases χ.even_or_odd with heven | hodd
  · have hraw :=
      re_add_dirichletReciprocalResidues_zero_one_of_even_raw hN2 hGRH hprimitive hne hinv heven
        hxpos
    have herr := he heven
    unfold Analysis.primitiveReciprocalEvenMainError at herr
    rw [hraw]
    nlinarith only [herr]
  · have hraw :=
      re_add_dirichletReciprocalResidues_zero_one_of_odd_raw hN2 hGRH hprimitive hne hinv hodd hxpos
    have herr := ho hodd
    unfold Analysis.primitiveReciprocalOddMainError at herr
    rw [hraw]
    nlinarith only [herr]

/-- For a primitive nonprincipal character under GRH and x greater than one,
parity-conditional main-error bounds by e control the finite reciprocal residue ledger.
Combine the zero and one residues with the erased-ledger zero contribution.
This supplies the finite-contour estimate at arbitrary numerical cutoffs. -/
theorem primitiveReciprocalLedger_le_of_parity_mainErrors {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {e : ℝ} (hx : 1 < x)
    (ho : χ.Odd → Analysis.primitiveReciprocalOddMainError x ≤ e)
    (he : χ.Even → Analysis.primitiveReciprocalEvenMainError x ≤ e) {z w : ℂ}
    (h0 :
      (0 : ℂ) ∈
        AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle χ hne z
          w)
    (h1 :
      (1 : ℂ) ∈
        AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle χ hne z
          w) :
    (∑
          s ∈
            AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle χ hne
              z w,
          AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x s).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) + e -
        (1 - 1 / Real.sqrt x) ^ 2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| := by
  have hxpos : (0 : ℝ) < x := by linarith only [hx]
  rw [AnalyticNumberTheory.DirichletLFunction.dirichletSplitReciprocalSingularitySum x hne h1 h0]
  have h01 :=
    primitiveReciprocalOrigin_le_of_parity_mainErrors hN2 hGRH hprimitive hne hinv hx ho he
  have hzeros :=
    AnalyticNumberTheory.DirichletLFunction.re_sum_erased_primitiveReciprocalResidues_le hN2 hGRH
      hprimitive hne hinv hxpos (z := z) (w := w)
  have hsqrtx_pos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hsqrt_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hxpos.le
  have hinv_sqrt_sq : (1 / Real.sqrt x) ^ 2 = 1 / x := by rw [div_pow, one_pow, hsqrt_sq]
  have hbcoeff :
    -(1 + 1 / x) * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
        2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| / Real.sqrt x =
      -(1 - 1 / Real.sqrt x) ^ 2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| := by
    have hsqrtx_ne : Real.sqrt x ≠ 0 := hsqrtx_pos.ne'
    have hexpand : (1 - 1 / Real.sqrt x) ^ 2 = 1 - 2 / Real.sqrt x + 1 / x := by
      rw [sub_sq, one_pow, hinv_sqrt_sq]
      ring
    rw [hexpand]
    have h2sqrt : 2 / Real.sqrt x = 2 * (1 / Real.sqrt x) := by ring
    ring
  have herased_re :
    (∑
          ρ ∈
            ((AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle χ
                      hne z w).erase
                  1).erase
              0,
          AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x ρ).re ≤
      2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| / Real.sqrt x :=
    hzeros
  rw [Complex.add_re, Complex.add_re]
  calc
    (AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x 1).re +
          (AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x 0).re +
          (∑
              ρ ∈
                ((AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle
                          χ hne z w).erase
                      1).erase
                  0,
              AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x ρ).re ≤
        ((1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) -
              (1 + 1 / x) * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
            e) +
          2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| / Real.sqrt x :=
      by
      have h01' :
        (AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x 1).re +
            (AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x 0).re ≤
          (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) -
              (1 + 1 / x) * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
            e := by
        rw [add_comm]
        rw [← Complex.add_re]
        exact h01
      exact add_le_add h01' herased_re
    _ =
        (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) + e -
          (1 - 1 / Real.sqrt x) ^ 2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| :=
      by linear_combination hbcoeff

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For x greater than one, A at least two and the applicable parity error at most e,
the reciprocal weighted sum minus its left edge has the displayed upper bound.
Pass the finite-ledger inequality through the common-height contour limit.
The error e is retained unchanged. -/
theorem characterReciprocalWeightedSum_sub_leftVertical_le_of_parity_mainErrors {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} {e : ℝ} (hx : 1 < x)
    (ho : χ.Odd → Analysis.primitiveReciprocalOddMainError x ≤ e)
    (he : χ.Even → Analysis.primitiveReciprocalEvenMainError x ≤ e) (A : ℕ) (hA : 2 ≤ A) :
    (characterReciprocalWeightedSum x χ).re -
        (2 * Real.pi)⁻¹ *
          (∫ t : ℝ,
              dirichletReciprocalContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) + e -
        (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
  have hx1 : (1 : ℝ) ≤ x := by linarith only [hx]
  have htend :=
    tendsto_normalized_dirichletReciprocalBoundary_heightSeq hN2 hGRH hprimitive hne hinv hx1 A hA
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  have hev :
    ∀ᶠ k : ℕ in Filter.atTop,
      ((-Complex.I / (2 * (Real.pi : ℂ))) *
            AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
              (dirichletReciprocalContourKernel x χ)
              (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
              (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k)).re ≤
        (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) + e -
          (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
    filter_upwards with k
    have hid :=
      dirichletReciprocalFiniteContourIdentity_heightSeq_normalized hN2 hGRH hprimitive hne hinv
        (zero_lt_one.trans hx) A k hA
        (primitiveHeightSeq_singularities_mem_open hN2 hGRH hprimitive hne hinv A k hA)
    obtain ⟨h0, h1⟩ :=
      primitiveReciprocalMellinPoints_mem_singularities_heightSeq hN2 hGRH hprimitive hne hinv A k
        hA
    have hbound :=
      primitiveReciprocalLedger_le_of_parity_mainErrors hN2 hGRH hprimitive hne hinv hx ho he (z :=
        primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k) (w :=
        primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k) h0 h1
    rw [hid]
    exact hbound
  have hlimit := le_of_tendsto htendRe hev
  rw [Complex.sub_re] at hlimit
  have hmulre :
    ((↑(2 * Real.pi))⁻¹ *
            ∫ t : ℝ,
              dirichletReciprocalContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I) :
          ℂ).re =
      (2 * Real.pi)⁻¹ *
        (∫ t : ℝ,
            dirichletReciprocalContourKernel x χ
              (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
    rw [show ((↑(2 * Real.pi))⁻¹ : ℂ) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) from
        (Complex.ofReal_inv (2 * Real.pi)).symm,
      Complex.re_ofReal_mul]
  rw [hmulre] at hlimit
  exact hlimit

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For x greater than one and the applicable parity main error at most e,
a primitive nonprincipal character under GRH satisfies the raw reciprocal bound.
Remove the left edge by its limit as A tends to infinity. This is the
cutoff-independent reciprocal input to witness comparisons. -/
theorem primitiveReciprocalRaw_of_parity_mainErrors {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} {e : ℝ} (hx : 1 < x)
    (ho : χ.Odd → Analysis.primitiveReciprocalOddMainError x ≤ e)
    (he : χ.Even → Analysis.primitiveReciprocalEvenMainError x ≤ e) :
    (characterReciprocalWeightedSum x χ).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) + e -
        (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
  have hx1 : (1 : ℝ) < x := by linarith only [hx]
  have htend :=
    tendsto_dirichletReciprocalContourKernel_leftVertical_integral_atTop hprimitive hne hinv hx1
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  simp only [Complex.zero_re] at htendRe
  have htendScaled :
    Filter.Tendsto
      (fun A : ℕ =>
        (characterReciprocalWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletReciprocalContourKernel x χ
                  (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re)
      Filter.atTop (nhds ((characterReciprocalWeightedSum x χ).re - (2 * Real.pi)⁻¹ * 0)) :=
    Filter.Tendsto.const_sub _ (Filter.Tendsto.const_mul _ htendRe)
  simp only [mul_zero, sub_zero] at htendScaled
  have hev :
    ∀ᶠ A : ℕ in Filter.atTop,
      (characterReciprocalWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletReciprocalContourKernel x χ
                  (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
        (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) + e -
          (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
    filter_upwards [Filter.eventually_ge_atTop 2] with A hA
    exact
      characterReciprocalWeightedSum_sub_leftVertical_le_of_parity_mainErrors hN2 hGRH hprimitive
        hne hinv hx ho he A hA
  exact le_of_tendsto htendScaled hev

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For x greater than one and both parity main errors bounded by e,
the zero and one residues obey the displayed conductor and zero-mass bound.
Apply the exact odd or even closed form. This isolates the numerical error
from the contour argument. -/
theorem primitiveReciprocalOrigin_le_of_mainErrors {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} {e : ℝ} (hx : 1 < x)
    (ho : Analysis.primitiveReciprocalOddMainError x ≤ e)
    (he : Analysis.primitiveReciprocalEvenMainError x ≤ e) :
    (dirichletReciprocalResidueAt hne x 0 + dirichletReciprocalResidueAt hne x 1).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - (1 + 1 / x) * |primitiveBRe χ| +
        e := by
  exact
    primitiveReciprocalOrigin_le_of_parity_mainErrors hN2 hGRH hprimitive hne hinv hx (fun _ ↦ ho)
      (fun _ ↦ he)

/-- For a primitive nonprincipal character under GRH and x greater than one,
parity main-error bounds by e control the finite reciprocal residue ledger.
Combine the zero and one residues with the erased-ledger zero contribution.
This supplies the finite-contour estimate at arbitrary numerical cutoffs. -/
theorem primitiveReciprocalLedger_le_of_mainErrors {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {e : ℝ} (hx : 1 < x)
    (ho : Analysis.primitiveReciprocalOddMainError x ≤ e)
    (he : Analysis.primitiveReciprocalEvenMainError x ≤ e) {z w : ℂ}
    (h0 :
      (0 : ℂ) ∈
        AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle χ hne z
          w)
    (h1 :
      (1 : ℂ) ∈
        AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle χ hne z
          w) :
    (∑
          s ∈
            AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle χ hne
              z w,
          AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x s).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) + e -
        (1 - 1 / Real.sqrt x) ^ 2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| := by
  exact
    primitiveReciprocalLedger_le_of_parity_mainErrors hN2 hGRH hprimitive hne hinv hx (fun _ ↦ ho)
      (fun _ ↦ he) h0 h1

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For x greater than one, A at least two and both parity errors at most e,
the reciprocal weighted sum minus its left edge has the displayed upper bound.
Pass the finite-ledger inequality through the common-height contour limit.
The error e is retained unchanged. -/
theorem characterReciprocalWeightedSum_sub_leftVertical_le_of_mainErrors {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} {e : ℝ} (hx : 1 < x)
    (ho : Analysis.primitiveReciprocalOddMainError x ≤ e)
    (he : Analysis.primitiveReciprocalEvenMainError x ≤ e) (A : ℕ) (hA : 2 ≤ A) :
    (characterReciprocalWeightedSum x χ).re -
        (2 * Real.pi)⁻¹ *
          (∫ t : ℝ,
              dirichletReciprocalContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) + e -
        (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
  exact
    characterReciprocalWeightedSum_sub_leftVertical_le_of_parity_mainErrors hN2 hGRH hprimitive hne
      hinv hx (fun _ ↦ ho) (fun _ ↦ he) A hA

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For x greater than one and both parity main errors at most e,
a primitive nonprincipal character under GRH satisfies the raw reciprocal bound.
Remove the left edge by its limit as A tends to infinity. This is the
cutoff-independent reciprocal input to witness comparisons. -/
theorem primitiveReciprocalRaw_of_mainErrors {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} {e : ℝ} (hx : 1 < x)
    (ho : Analysis.primitiveReciprocalOddMainError x ≤ e)
    (he : Analysis.primitiveReciprocalEvenMainError x ≤ e) :
    (characterReciprocalWeightedSum x χ).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) + e -
        (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
  exact
    primitiveReciprocalRaw_of_parity_mainErrors hN2 hGRH hprimitive hne hinv hx (fun _ ↦ ho)
      (fun _ ↦ he)

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For an even primitive nonprincipal character under GRH and x greater
than one, any upper bound e for the even reciprocal main error gives the
raw weighted-sum bound. Select the even branch; the odd guard is vacuous.
This permits stronger even errors without controlling the odd main term. -/
theorem primitiveReciprocalRaw_even_le_of_mainError {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {x e : ℝ}
    (hx : 1 < x) (he : Analysis.primitiveReciprocalEvenMainError x ≤ e) :
    (characterReciprocalWeightedSum x χ).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) + e -
        (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
  have h :=
    primitiveReciprocalRaw_of_parity_mainErrors hN2 hGRH hprimitive hne hinv hx
      (fun hodd ↦ (χ.not_even_and_odd ⟨heven, hodd⟩).elim) (fun _ ↦ he)
  linarith only [h]

end PseudoPrime.LLS
