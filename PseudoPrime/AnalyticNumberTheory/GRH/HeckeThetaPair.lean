/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.WeakFEPairProduct
public import PseudoPrime.Analysis.WeakFEPairRescale

/-! # Theta pairs for the Hecke lattice -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.GRH

/-- The even Hurwitz functional-equation pair rescaled by a positive real
number. It is a factor in the rectangular theta pair for the Hecke lattice. -/
noncomputable def heckeScaledEvenPair (a : UnitAddCircle) (u : ℝ) (hu : 0 < u) : WeakFEPair ℂ :=
  Analysis.rescaleWeakFEPair (HurwitzZeta.hurwitzEvenFEPair a)
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_evenKernel a))
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_cosKernel a)) u hu

/-- The first coordinate shift in the parity decomposition of the
Eisenstein lattice, for real coordinates `a`, `b` and period `L`. -/
noncomputable def heckeXShift (a b L : ℝ) (e : Fin 2) : ℝ :=
  (2 * a - b - L * e) / (2 * L)

/-- The second coordinate shift in the parity decomposition of the
Eisenstein lattice, for real coordinate `b` and period `L`. -/
noncomputable def heckeYShift (b L : ℝ) (e : Fin 2) : ℝ :=
  (b + L * e) / (2 * L)

/-- The first kernel of a scaled even Hurwitz pair is continuous for positive
arguments, so it may be multiplied by another such kernel. -/
theorem heckeScaledEvenPair_f_continuous (a : UnitAddCircle) (u : ℝ) (hu : 0 < u) :
    ContinuousOn (heckeScaledEvenPair a u hu).f (Set.Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_evenKernel a)).comp
    (continuous_const.mul continuous_id).continuousOn (fun _ hx ↦ mul_pos hu hx)

/-- The second kernel of a scaled even Hurwitz pair is continuous for positive
arguments, so it may be multiplied by another such kernel. -/
theorem heckeScaledEvenPair_g_continuous (a : UnitAddCircle) (u : ℝ) (hu : 0 < u) :
    ContinuousOn (heckeScaledEvenPair a u hu).g (Set.Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_cosKernel a)).comp
    (continuous_const.mul continuous_id).continuousOn (fun _ hx ↦ mul_pos (inv_pos.mpr hu) hx)

/-- The product of two positively scaled even Hurwitz pairs. Its kernels are
the rectangular theta kernels used in the Eisenstein lattice decomposition. -/
noncomputable def heckeRectangularPair (a b : UnitAddCircle) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    WeakFEPair ℂ :=
  Analysis.mulWeakFEPair (heckeScaledEvenPair a u hu) (heckeScaledEvenPair b v hv)
    (heckeScaledEvenPair_f_continuous a u hu) (heckeScaledEvenPair_g_continuous a u hu)
    (heckeScaledEvenPair_f_continuous b v hv) (heckeScaledEvenPair_g_continuous b v hv)

/-- The theta pair associated to one parity class of the Eisenstein lattice
with real coordinates `a`, `b` and positive period `L`. -/
noncomputable def heckeParityPair (a b L : ℝ) (hL : 0 < L) (e : Fin 2) : WeakFEPair ℂ :=
  heckeRectangularPair (heckeXShift a b L e) (heckeYShift b L e) (L ^ 2) (3 * L ^ 2)
    (sq_pos_of_pos hL) (mul_pos (show (0 : ℝ) < 3 from zero_lt_three) (sq_pos_of_pos hL))

/-- Each parity pair has weight one, so its weighted finite sums again
admit the functional-equation construction. -/
theorem heckeParityPair_k (a b L : ℝ) (hL : 0 < L) (e : Fin 2) :
    (heckeParityPair a b L hL e).k = 1 := by
  change (1 / 2 : ℝ) + 1 / 2 = 1
  norm_num only

end PseudoPrime.AnalyticNumberTheory.GRH
