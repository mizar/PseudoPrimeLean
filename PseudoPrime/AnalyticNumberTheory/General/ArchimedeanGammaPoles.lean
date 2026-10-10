/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.InverseZeros
public import PseudoPrime.AnalyticNumberTheory.General.ArchimedeanGammaFactor
public import PseudoPrime.AnalyticNumberTheory.General.WeightedLogarithmicResidues
public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.LocalResidueAssembly

/-!
# Finite contours for archimedean gamma poles

Reciprocal gamma factors are entire. Their zero locations and analytic
multiplicities supply the gamma residues in a positive-real rectangle.
For nonnegative shifts the same finite contour formula has an empty ledger.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The entire reciprocal of Gamma((s+kappa)/2), defined with the total Gamma
function. Its simple zeros record the poles of the shifted gamma factor.
No restriction on the complex shift is imposed by this definition. -/
noncomputable def inverseShiftedGamma (κ s : ℂ) : ℂ :=
  (Complex.Gamma ((s + κ) / 2))⁻¹

/-- For any complex shift, the shifted reciprocal Gamma function is entire.
Compose the entire reciprocal Gamma with its affine argument. This supplies
analyticity at gamma poles for their logarithmic residue certificates. -/
theorem differentiable_inverseShiftedGamma (κ : ℂ) : Differentiable ℂ (inverseShiftedGamma κ) := by
  exact Complex.differentiable_one_div_Gamma.comp ((differentiable_id.add_const κ).div_const 2)

/-- For arbitrary complex shift and argument, the shifted reciprocal Gamma
vanishes exactly at -kappa-2*n for natural n. Use Gamma's zero characterization
and solve the affine equation. This locates all shifted gamma poles. -/
theorem inverseShiftedGamma_eq_zero_iff (κ s : ℂ) :
    inverseShiftedGamma κ s = 0 ↔ ∃ n : ℕ, s = -κ - 2 * (n : ℂ) := by
  rw [inverseShiftedGamma, inv_eq_zero, Complex.Gamma_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : s + κ = -(n : ℂ) * 2 := (div_eq_iff (two_ne_zero : (2 : ℂ) ≠ 0)).mp hn
    linear_combination h
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    ring

/-- At every shifted gamma pole -kappa-2*n, the reciprocal has analytic order one.
Its affine argument has nonzero derivative, so composition preserves the simple
inverse-Gamma order. This determines each individual gamma residue. -/
theorem analyticOrderAt_inverseShiftedGamma_pole (κ : ℂ) (n : ℕ) :
    analyticOrderAt (inverseShiftedGamma κ) (-κ - 2 * (n : ℂ)) = 1 := by
  have ha : AnalyticAt ℂ (fun s : ℂ ↦ (s + κ) / 2) (-κ - 2 * (n : ℂ)) :=
    (analyticAt_id.add analyticAt_const).div_const
  have hd : deriv (fun s : ℂ ↦ (s + κ) / 2) (-κ - 2 * (n : ℂ)) ≠ 0 := by
    rw [((hasDerivAt_id' (-κ - 2 * (n : ℂ))).add_const κ).div_const 2 |>.deriv]
    exact div_ne_zero one_ne_zero two_ne_zero
  change
    analyticOrderAt ((fun s : ℂ ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ (s + κ) / 2))
        (-κ - 2 * (n : ℂ)) =
      1
  rw [analyticOrderAt_comp_of_deriv_ne_zero ha hd]
  have he : (-κ - 2 * (n : ℂ) + κ) / 2 = -(n : ℂ) := by ring
  rw [he]
  exact Gamma.analyticOrderAt_inverseGamma_neg_nat n

/-- If Re kappa>-1 and Re s>0, a reciprocal Gamma zero occurs exactly at s=-kappa.
All positive natural indices put the pole strictly in the left half-plane.
This reduces the pole ledger for positive rectangles to the first shifted pole. -/
theorem inverseShiftedGamma_eq_zero_iff_of_re_pos {κ s : ℂ} (hk : -1 < κ.re) (hs : 0 < s.re) :
    inverseShiftedGamma κ s = 0 ↔ s = -κ := by
  rw [inverseShiftedGamma_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hz : n = 0 := by
      by_contra hn0
      have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn0)
      have he : s.re = -κ.re - 2 * (n : ℝ) := by
        rw [hn]
        simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.re_ofNat,
          Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
      linarith only [hk, hs, hn1, he]
    simpa only [hz, Nat.cast_zero, mul_zero, sub_zero] using hn
  · intro h
    exact ⟨0, by simpa only [Nat.cast_zero, mul_zero, sub_zero] using h⟩

/-- For any shift and natural pole index, the natural multiplicity of the shifted
reciprocal Gamma zero is one. Convert the proved finite analytic order to its
natural value. This permits counting coincident gamma poles by multiplicity. -/
theorem analyticOrderNatAt_inverseShiftedGamma_pole (κ : ℂ) (n : ℕ) :
    analyticOrderNatAt (inverseShiftedGamma κ) (-κ - 2 * (n : ℂ)) = 1 := by
  rw [analyticOrderNatAt, analyticOrderAt_inverseShiftedGamma_pole]
  rfl

/-- For ordered real corners with positive left real coordinate, each point of
the closed rectangle has positive real part. Read its unordered real interval
membership. This applies the first-pole characterization throughout the rectangle. -/
private theorem re_pos_of_mem_positive_rectangle {z w s : ℂ} (hz : 0 < z.re) (hre : z.re < w.re)
    (hs : s ∈ Rectangle.rectangleClosedBox z w) : 0 < s.re := by
  have hsr : s.re ∈ Set.uIcc z.re w.re := hs.1
  rw [Set.uIcc_of_le hre.le] at hsr
  exact lt_of_lt_of_le hz hsr.1

/-- At a differentiable nonzero value, taking the reciprocal negates the logarithmic
derivative. Apply the composition rule for inverse and simplify. This transfers
entire reciprocal-Gamma residues to the actual gamma logarithmic derivative. -/
private theorem logDeriv_inverse_of_differentiable {f : ℂ → ℂ} {s : ℂ} (hf : DifferentiableAt ℂ f s)
    (hn : f s ≠ 0) : logDeriv (fun z ↦ (f z)⁻¹) s = -logDeriv f s := by
  change logDeriv ((fun z : ℂ ↦ z⁻¹) ∘ f) s = _
  rw [logDeriv_comp (differentiableAt_inv hn) hf, logDeriv_inv, logDeriv_apply]
  ring

/-- The reciprocal of the degree-d archimedean gamma factor. It is entire, and its
zero multiplicities record the gamma poles, including coincident parameter shifts.
It provides an analytic function for finite weighted residue assembly. -/
noncomputable def inverseArchimedeanGammaFactor {d : ℕ} (κ : Fin d → ℂ) (s : ℂ) : ℂ :=
  (archimedeanGammaFactor κ s)⁻¹

/-- For any parameter family and argument, the reciprocal archimedean factor is
the reciprocal pi power times the product of shifted reciprocal Gamma functions.
Distribute the inverse over the finite product. This exposes its entire factors. -/
theorem inverseArchimedeanGammaFactor_eq_product {d : ℕ} (κ : Fin d → ℂ) (s : ℂ) :
    inverseArchimedeanGammaFactor κ s =
      ((Real.pi : ℂ) ^ ((-(d : ℂ) / 2) * s))⁻¹ * ∏ j : Fin d, inverseShiftedGamma (κ j) s := by
  simp only [inverseArchimedeanGammaFactor, archimedeanGammaFactor, archimedeanGammaProduct,
    mul_inv, inverseShiftedGamma, Finset.prod_inv_distrib]

/-- For any finite family of complex shifts, the reciprocal archimedean factor is
entire. Differentiate the nonzero reciprocal pi power and each shifted reciprocal
Gamma, then multiply. This includes its zeros without pole exclusions. -/
theorem differentiable_inverseArchimedeanGammaFactor {d : ℕ} (κ : Fin d → ℂ) :
    Differentiable ℂ (inverseArchimedeanGammaFactor κ) := by
  have hp : Differentiable ℂ (fun s : ℂ ↦ ((Real.pi : ℂ) ^ ((-(d : ℂ) / 2) * s))⁻¹) := by
    intro s
    exact
      ((differentiableAt_id.const_mul (-(d : ℂ) / 2)).const_cpow
            (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).inv
        (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have hg :=
    Differentiable.fun_finsetProd (u := Finset.univ)
      (fun j _ ↦ differentiable_inverseShiftedGamma (κ j))
  have heq :
    inverseArchimedeanGammaFactor κ =
      (fun s ↦
        ((Real.pi : ℂ) ^ ((-(d : ℂ) / 2) * s))⁻¹ * ∏ j : Fin d, inverseShiftedGamma (κ j) s) :=
    funext (inverseArchimedeanGammaFactor_eq_product κ)
  rw [heq]
  exact hp.mul hg

/-- For shifts with real part greater than minus one, the reciprocal archimedean
factor is nonzero at two. Its gamma arguments have positive real part.
This rules out the identically zero function when constructing local residues. -/
theorem inverseArchimedeanGammaFactor_ne_zero_at_two {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, -1 < (κ j).re) : inverseArchimedeanGammaFactor κ 2 ≠ 0 := by
  exact
    inv_ne_zero
      (archimedeanGammaFactor_ne_zero
        (by
          rw [Complex.re_ofNat]; exact one_lt_two)
        hk)

/-- For shifts with Re kappa_j>-1 and Re s>0, the reciprocal archimedean factor
vanishes exactly when s=-kappa_j for some j. Its pi power is nonzero and each
shifted reciprocal has only its first pole in this half-plane.
This describes the complete positive-rectangle pole ledger. -/
theorem inverseArchimedeanGammaFactor_eq_zero_iff_of_re_pos {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, -1 < (κ j).re) {s : ℂ} (hs : 0 < s.re) :
    inverseArchimedeanGammaFactor κ s = 0 ↔ ∃ j : Fin d, s = -κ j := by
  rw [inverseArchimedeanGammaFactor_eq_product]
  have hp : ((Real.pi : ℂ) ^ ((-(d : ℂ) / 2) * s))⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  rw [mul_eq_zero, or_iff_right hp, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, inverseShiftedGamma_eq_zero_iff_of_re_pos (hk _) hs]

/-- The distinct first shifted gamma poles -kappa_j lying in a closed rectangle.
The filtered finite image records locations once; reciprocal-factor analytic
orders supply multiplicities. With Re kappa_j>-1 and a positive-real rectangle,
this contains all gamma poles relevant to moving the Mellin line. -/
noncomputable def archimedeanGammaPolesInPositiveRectangle {d : ℕ} (κ : Fin d → ℂ) (z w : ℂ) :
    Finset ℂ := by
  classical
    exact
    ((Finset.univ : Finset (Fin d)).image (fun j ↦ -κ j)).filter
      (fun s ↦ s ∈ Rectangle.rectangleClosedBox z w)

/-- Membership in the positive-rectangle gamma ledger means that the point is
-kappa_j for some index and belongs to the closed rectangle. Unfold the finite
image and filter. This verifies singularity coverage and boundary exclusions. -/
theorem mem_archimedeanGammaPolesInPositiveRectangle {d : ℕ} (κ : Fin d → ℂ) (z w s : ℂ) :
    s ∈ archimedeanGammaPolesInPositiveRectangle κ z w ↔
      (∃ j : Fin d, s = -κ j) ∧ s ∈ Rectangle.rectangleClosedBox z w := by
  classical
    simp only [archimedeanGammaPolesInPositiveRectangle, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and, eq_comm]

/-- An entire function nonzero at a specified point has finite analytic order at
every point. The plane identity theorem excludes local vanishing. This applies
to reciprocal gamma factors even when they vanish at the origin. -/
private theorem entire_finite_order_of_ne_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F) {p : ℂ}
    (hp : F p ≠ 0) (s : ℂ) : analyticOrderAt F s ≠ ⊤ := by
  intro ht
  have ha : AnalyticOnNhd ℂ F Set.univ := fun z _ ↦ hF.analyticAt z
  have he :=
    ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ s)
      (analyticOrderAt_eq_top.mp ht)
  exact hp (he (Set.mem_univ p))

/-- For shifts with real part greater than minus one and a weight analytic at c,
sufficiently small square integrals of the negative reciprocal-factor logarithmic
derivative times the weight equal -2*pi*i times its multiplicity times W(c).
Finite analytic order follows from the nonzero value at two. This supplies the
local certificates for gamma-factor contour assembly. -/
theorem exists_radius_weighted_inverseArchimedeanGamma_residue {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, -1 < (κ j).re) (c : ℂ) {W : ℂ → ℂ} (hW : AnalyticAt ℂ W c) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral
                (fun s ↦ -logDeriv (inverseArchimedeanGammaFactor κ) s * W s)
                (RectangleGeometry.centeredSquareLower c r)
                (RectangleGeometry.centeredSquareUpper c r) =
              2 * Real.pi * Complex.I *
                (-(analyticOrderNatAt (inverseArchimedeanGammaFactor κ) c : ℂ) * W c) := by
  obtain ⟨g, hg, hg0, hlog⟩ :=
    exists_logDeriv_local_expansion ((differentiable_inverseArchimedeanGammaFactor κ).analyticAt c)
      (entire_finite_order_of_ne_zero (differentiable_inverseArchimedeanGammaFactor κ)
        (inverseArchimedeanGammaFactor_ne_zero_at_two κ hk) c)
  exact exists_radius_weighted_logDeriv_residue hg hg0 hW hlog

/-- At any point where the reciprocal archimedean factor is nonzero, its negative
logarithmic derivative equals the actual factor's logarithmic derivative.
Use the entire reciprocal and the inverse identity. This connects analytic
zero certificates to the gamma term of the completed explicit formula. -/
theorem neg_logDeriv_inverseArchimedeanGammaFactor {d : ℕ} (κ : Fin d → ℂ) {s : ℂ}
    (hn : inverseArchimedeanGammaFactor κ s ≠ 0) :
    -logDeriv (inverseArchimedeanGammaFactor κ) s = logDeriv (archimedeanGammaFactor κ) s := by
  have heq : archimedeanGammaFactor κ = (fun z ↦ (inverseArchimedeanGammaFactor κ z)⁻¹) := by
    funext z
    exact (inv_inv (archimedeanGammaFactor κ z)).symm
  rw [heq, logDeriv_inverse_of_differentiable (differentiable_inverseArchimedeanGammaFactor κ s) hn]

/-- For shifts with real part greater than minus one in a positive ordered rectangle,
a point outside the gamma ledger has nonzero reciprocal factor. Apply the exact
positive-half-plane zero characterization. This proves regularity off the ledger. -/
theorem inverseArchimedeanGammaFactor_ne_zero_off_pole_ledger {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, -1 < (κ j).re) {z w s : ℂ} (hz : 0 < z.re) (hre : z.re < w.re)
    (hs : s ∈ Rectangle.rectangleClosedBox z w)
    (hn : s ∉ archimedeanGammaPolesInPositiveRectangle κ z w) :
    inverseArchimedeanGammaFactor κ s ≠ 0 := by
  intro h
  have hp :=
    (inverseArchimedeanGammaFactor_eq_zero_iff_of_re_pos κ hk
          (re_pos_of_mem_positive_rectangle hz hre hs)).mp
      h
  exact hn ((mem_archimedeanGammaPolesInPositiveRectangle κ z w s).mpr ⟨hp, hs⟩)

/-- For shifts with Re kappa_j>-1, an ordered positive-real rectangle, an entire
weight, and no gamma pole on the boundary, the negative reciprocal-factor
logarithmic integral equals its negative multiplicity-weighted finite zero sum
with factor 2*pi*i. Assemble the local square certificates and use regularity
off the finite pole ledger. This prepares the actual gamma contour identity. -/
theorem inverseArchimedeanGamma_weighted_finite_contour {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, -1 < (κ j).re) {z w : ℂ} (hz : 0 < z.re) (hre : z.re < w.re) (him : z.im < w.im)
    {W : ℂ → ℂ} (hW : Differentiable ℂ W)
    (hopen :
      ∀ s ∈ archimedeanGammaPolesInPositiveRectangle κ z w,
        s ∈ RectangleGeometry.rectangleOpenBox z w) :
    RectangleGeometry.rectangleBoundaryIntegral
        (fun s ↦ -logDeriv (inverseArchimedeanGammaFactor κ) s * W s) z w =
      ∑ s ∈ archimedeanGammaPolesInPositiveRectangle κ z w,
        2 * Real.pi * Complex.I *
          (-(analyticOrderNatAt (inverseArchimedeanGammaFactor κ) s : ℂ) * W s) := by
  apply
    RectangleGeometry.rectangleBoundaryIntegral_eq_sum_of_local_residues _ _ _ hre him
      (fun s hs ↦ ((mem_archimedeanGammaPolesInPositiveRectangle κ z w s).mp hs).2) hopen
  · intro s hs hn
    have hf := inverseArchimedeanGammaFactor_ne_zero_off_pole_ledger κ hk hz hre hs hn
    exact
      ((((differentiable_inverseArchimedeanGammaFactor κ).analyticAt s).deriv.div
              ((differentiable_inverseArchimedeanGammaFactor κ).analyticAt s) hf).neg.mul
          (hW.analyticAt s)).differentiableAt
  · intro s _
    exact exists_radius_weighted_inverseArchimedeanGamma_residue κ hk s (hW.analyticAt s)

/-- For shifts with Re kappa_j>-1, an ordered positive-real rectangle, an entire
weight, and an interior pole ledger, the weighted actual gamma logarithmic
boundary integral equals -2*pi*i times the weighted reciprocal-factor zero
multiplicities. Transfer the reciprocal identity on the boundary.
This retains the gamma residues when moving a Mellin integration line. -/
theorem archimedeanGamma_weighted_finite_contour {d : ℕ} (κ : Fin d → ℂ) (hk : ∀ j, -1 < (κ j).re)
    {z w : ℂ} (hz : 0 < z.re) (hre : z.re < w.re) (him : z.im < w.im) {W : ℂ → ℂ}
    (hW : Differentiable ℂ W)
    (hopen :
      ∀ s ∈ archimedeanGammaPolesInPositiveRectangle κ z w,
        s ∈ RectangleGeometry.rectangleOpenBox z w) :
    RectangleGeometry.rectangleBoundaryIntegral
        (fun s ↦ logDeriv (archimedeanGammaFactor κ) s * W s) z w =
      ∑ s ∈ archimedeanGammaPolesInPositiveRectangle κ z w,
        2 * Real.pi * Complex.I *
          (-(analyticOrderNatAt (inverseArchimedeanGammaFactor κ) s : ℂ) * W s) := by
  rw [← inverseArchimedeanGamma_weighted_finite_contour κ hk hz hre him hW hopen]
  apply RectangleGeometry.rectangleBoundaryIntegral_congr_boundary
  intro s hs
  have hn : s ∉ archimedeanGammaPolesInPositiveRectangle κ z w := fun h ↦ hs.2 (hopen s h)
  dsimp only
  rw [neg_logDeriv_inverseArchimedeanGammaFactor κ
      (inverseArchimedeanGammaFactor_ne_zero_off_pole_ledger κ hk hz hre hs.1 hn)]

/-- For shifts with nonnegative real part, an ordered positive-real rectangle has
an empty gamma pole ledger. Every first pole has nonpositive real part.
This isolates the residue-free case used by the LLS gamma parameters. -/
theorem archimedeanGammaPolesInPositiveRectangle_eq_empty_of_nonneg {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, 0 ≤ (κ j).re) {z w : ℂ} (hz : 0 < z.re) (hre : z.re < w.re) :
    archimedeanGammaPolesInPositiveRectangle κ z w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨⟨j, hj⟩, hbox⟩ := (mem_archimedeanGammaPolesInPositiveRectangle κ z w s).mp hs
  have hp := re_pos_of_mem_positive_rectangle hz hre hbox
  rw [hj, Complex.neg_re] at hp
  exact (not_lt_of_ge (neg_nonpos.mpr (hk j))) hp

/-- For nonnegative-real-part shifts, an entire weight and an ordered positive-real
rectangle, the actual gamma logarithmic boundary integral vanishes. Apply the
finite gamma residue identity with its empty ledger. This supplies the finite
contour stage of residue-free Mellin line shifting in LLS. -/
theorem archimedeanGamma_weighted_finite_contour_eq_zero_of_nonneg {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, 0 ≤ (κ j).re) {z w : ℂ} (hz : 0 < z.re) (hre : z.re < w.re) (him : z.im < w.im)
    {W : ℂ → ℂ} (hW : Differentiable ℂ W) :
    RectangleGeometry.rectangleBoundaryIntegral
        (fun s ↦ logDeriv (archimedeanGammaFactor κ) s * W s) z w =
      0 := by
  have he := archimedeanGammaPolesInPositiveRectangle_eq_empty_of_nonneg κ hk hz hre
  have hop :
    ∀ s ∈ archimedeanGammaPolesInPositiveRectangle κ z w,
      s ∈ RectangleGeometry.rectangleOpenBox z w := by
    intro s hs
    rw [he] at hs
    exact False.elim (Finset.notMem_empty s hs)
  rw [archimedeanGamma_weighted_finite_contour κ (fun j ↦ lt_of_lt_of_le neg_one_lt_zero (hk j)) hz
      hre him hW hop,
    he, Finset.sum_empty]

/-- For nonnegative-real shifts, the reciprocal gamma factor is nonzero at every
positive-real argument. Its possible zeros are the negated shifts, whose real
parts are nonpositive. This supplies zero-free lines for Mellin-gamma integrals. -/
theorem inverseArchimedeanGammaFactor_ne_zero_of_nonneg {d : ℕ} (κ : Fin d → ℂ)
    (hk : ∀ j, 0 ≤ (κ j).re) {s : ℂ} (hs : 0 < s.re) : inverseArchimedeanGammaFactor κ s ≠ 0 := by
  intro he
  obtain ⟨j, hj⟩ :=
    (inverseArchimedeanGammaFactor_eq_zero_iff_of_re_pos κ
          (fun j ↦ lt_of_lt_of_le neg_one_lt_zero (hk j)) hs).mp
      he
  rw [hj, Complex.neg_re] at hs
  exact (not_lt_of_ge (neg_nonpos.mpr (hk j))) hs

end PseudoPrime.AnalyticNumberTheory.General
