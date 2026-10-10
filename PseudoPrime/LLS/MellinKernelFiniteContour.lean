/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelContour
public import PseudoPrime.AnalyticNumberTheory.General.WeightedLogarithmicResidues
public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.LocalResidueAssembly
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedShiftedZeros

/-!
# Finite weighted Mellin contour identities

Local regularization treats the kernel pole and finite-order zeros separately.
The rectangle residue theorem then sums both contributions for an analytic function
with a certified finite interior singularity ledger.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- At a finite-order zero away from the kernel pole, with positive scale and a point
in the kernel region, the weighted logarithmic derivative has residue minus the
vanishing order times `K(c) x^c`. The analytic local expansion and square Cauchy formula
supply a common radius for finite contour assembly. -/
theorem exists_radius_weighted_zero (K : MellinKernel) {F : ℂ → ℂ} {x : ℝ} {c : ℂ} (hx : 0 < x)
    (hc : c ∈ K.region) (hc' : c ≠ -1 / 2) (hF : AnalyticAt ℂ F c)
    (hfinite : analyticOrderAt F c ≠ ⊤) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
                (fun s => -logDeriv F s * (K.function s * (x : ℂ) ^ s))
                (AnalyticNumberTheory.RectangleGeometry.centeredSquareLower c r)
                (AnalyticNumberTheory.RectangleGeometry.centeredSquareUpper c r) =
              2 * Real.pi * Complex.I *
                (-(analyticOrderNatAt F c : ℂ) * (K.function c * (x : ℂ) ^ c)) := by
  have hK : AnalyticAt ℂ K.function c :=
    K.holomorphic.analyticAt
      ((K.region_open.sdiff isClosed_singleton).mem_nhds
        ⟨hc, fun hs => hc' (Set.mem_singleton_iff.mp hs)⟩)
  have hW := hK.mul (analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.mpr hx))
  obtain ⟨g, hg, hg0, hlog⟩ :=
    AnalyticNumberTheory.General.exists_logDeriv_local_expansion hF hfinite
  exact AnalyticNumberTheory.General.exists_radius_weighted_logDeriv_residue hg hg0 hW hlog

open AnalyticNumberTheory in
/-- At the kernel pole, assume the analytic function is nonzero and the scale is positive.
The residue is its negative logarithmic derivative times the regularized kernel and power.
Multiplication by `s+1/2` removes the possible pole and gives a local square certificate. -/
theorem exists_radius_weighted_pole (K : MellinKernel) {F : ℂ → ℂ} {x : ℝ} (hx : 0 < x)
    (hp : (-1 / 2 : ℂ) ∈ K.region) (hF : AnalyticAt ℂ F (-1 / 2)) (hF0 : F (-1 / 2) ≠ 0) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral
                (fun s => -logDeriv F s * (K.function s * (x : ℂ) ^ s))
                (RectangleGeometry.centeredSquareLower (-1 / 2) r)
                (RectangleGeometry.centeredSquareUpper (-1 / 2) r) =
              2 * Real.pi * Complex.I *
                (-logDeriv F (-1 / 2) * (K.regularized (-1 / 2) * (x : ℂ) ^ (-1 / 2 : ℂ))) := by
  let H : ℂ → ℂ := fun s => -logDeriv F s * (K.regularized s * (x : ℂ) ^ s)
  have hK := K.regularized_holomorphic.analyticAt (K.region_open.mem_nhds hp)
  have hH : AnalyticAt ℂ H (-1 / 2) :=
    (hF.deriv.div hF hF0).neg.mul
      (hK.mul (analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.mpr hx)))
  have hr : ∀ᶠ s in nhdsWithin (-1 / 2 : ℂ) ({(-1 / 2 : ℂ)}ᶜ : Set ℂ), s ∈ K.region :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (K.region_open.mem_nhds hp)
  have heq :
    Filter.EventuallyEq (nhdsWithin (-1 / 2 : ℂ) ({(-1 / 2 : ℂ)}ᶜ : Set ℂ))
      (fun s => (s - (-1 / 2)) * (-logDeriv F s * (K.function s * (x : ℂ) ^ s))) H := by
    filter_upwards [hr, eventually_mem_nhdsWithin] with s hs hsp
    dsimp only [H]
    rw [K.regularized_eq s hs (Set.mem_compl_singleton_iff.mp hsp)]
    ring
  exact RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul hH heq

/-- The residue coefficient of `-logDeriv F(s) K(s) x^s`: use kernel regularization at
`-1/2`, and minus the finite analytic order times the weight elsewhere. Analyticity,
finite order and nonvanishing at the kernel pole justify this totalized definition
in the finite contour theorem. -/
noncomputable def weightedResidue (K : MellinKernel) (F : ℂ → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  if s = -1 / 2 then -logDeriv F s * (K.regularized s * (x : ℂ) ^ s)
  else -(analyticOrderNatAt F s : ℂ) * (K.function s * (x : ℂ) ^ s)

/-- For a positive scale and ordered rectangle in the kernel region, assume `F` is analytic,
nonzero at the kernel pole, and has a finite interior ledger covering all possible poles
and zeros. Its weighted logarithmic contour integral is `2πi` times the residue sum.
The proof assembles the local square certificates; it requires no GRH or contour limit.
This is the finite identity used before passing to good-height limits. -/
theorem weightedFiniteContourIdentity (K : MellinKernel) {F : ℂ → ℂ} {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hregion : AnalyticNumberTheory.Rectangle.rectangleClosedBox z w ⊆ K.region)
    (hF : AnalyticOnNhd ℂ F K.region) (hp : F (-1 / 2) ≠ 0) (S : Finset ℂ)
    (hclosed : ∀ s ∈ S, s ∈ AnalyticNumberTheory.Rectangle.rectangleClosedBox z w)
    (hopen : ∀ s ∈ S, s ∈ AnalyticNumberTheory.RectangleGeometry.rectangleOpenBox z w)
    (hcover :
      ∀ s ∈ AnalyticNumberTheory.Rectangle.rectangleClosedBox z w, s = -1 / 2 ∨ F s = 0 → s ∈ S)
    (hfinite : ∀ s ∈ S, analyticOrderAt F s ≠ ⊤) :
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
        (fun s => -logDeriv F s * (K.function s * (x : ℂ) ^ s)) z w =
      ∑ s ∈ S, 2 * Real.pi * Complex.I * weightedResidue K F x s := by
  apply
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral_eq_sum_of_local_residues _ _ S
      hre him hclosed hopen
  · intro s hs hn
    have hr := hregion hs
    have hsp : s ≠ -1 / 2 := fun he => hn (hcover s hs (Or.inl he))
    have hFs : F s ≠ 0 := fun he => hn (hcover s hs (Or.inr he))
    have hK :=
      K.holomorphic.analyticAt
        ((K.region_open.sdiff isClosed_singleton).mem_nhds
          ⟨hr, fun he => hsp (Set.mem_singleton_iff.mp he)⟩)
    have hFa := hF s hr
    exact
      ((hFa.deriv.div hFa hFs).neg.mul
          (hK.mul
            (analyticAt_const.cpow analyticAt_id
              (Complex.ofReal_mem_slitPlane.mpr hx)))).differentiableAt
  · intro s hs
    by_cases hsp : s = -1 / 2
    · subst s
      simpa only [weightedResidue, ↓reduceIte] using
        exists_radius_weighted_pole K hx (hregion (hclosed _ hs)) (hF _ (hregion (hclosed _ hs))) hp
    · simpa only [weightedResidue, ite_eq_right hsp] using
        exists_radius_weighted_zero K hx (hregion (hclosed _ hs)) hsp
          (hF _ (hregion (hclosed _ hs))) (hfinite _ hs)

open AnalyticNumberTheory in
/-- For a primitive nonprincipal character and positive scale, an ordered rectangle
in the kernel region has weighted completed-logarithmic boundary integral equal to
`2πi` times its finite shifted-zero and kernel-pole residues, provided its ledger
is interior. Compact zero finiteness and the generic local certificates discharge
all multiplicity and residue hypotheses. This is the finite stage of Lemma 6.1. -/
theorem completedFiniteContourIdentity (K : MellinKernel) {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x)
    {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    (hregion : Rectangle.rectangleClosedBox z w ⊆ K.region)
    (hopen :
      ∀ s ∈ DirichletLFunction.completedKernelSingularities hprimitive hne z w,
        s ∈ RectangleGeometry.rectangleOpenBox z w) :
    RectangleGeometry.rectangleBoundaryIntegral
        (fun s => -logDeriv χ.completedLFunction (s + 1 / 2) * (K.function s * (x : ℂ) ^ s)) z w =
      ∑ s ∈ DirichletLFunction.completedKernelSingularities hprimitive hne z w,
        2 * Real.pi * Complex.I *
          weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x s := by
  have hlog :
    (fun s =>
        -logDeriv (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) s *
          (K.function s * (x : ℂ) ^ s)) =
      (fun s => -logDeriv χ.completedLFunction (s + 1 / 2) * (K.function s * (x : ℂ) ^ s)) := by
    funext s
    rw [DirichletLFunction.logDeriv_shifted_completed hne]
  rw [← hlog]
  apply weightedFiniteContourIdentity K hx hre him hregion
  · intro s _
    exact
      ((χ.differentiable_completedLFunction hne).analyticAt _).comp
        (analyticAt_id.add analyticAt_const)
  · simpa only [neg_div, neg_add_cancel] using
      DirichletLFunction.dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  · exact fun s hs => (DirichletLFunction.mem_completedKernelSingularities.mp hs).1
  · exact hopen
  · exact fun s hs hz => DirichletLFunction.mem_completedKernelSingularities.mpr ⟨hs, hz⟩
  · exact fun s _ => DirichletLFunction.shifted_completed_order_ne_top hprimitive hne s

end PseudoPrime.LLS.PaperStatements.MellinKernel
