/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven

/-! # Rescaling rapidly decreasing kernels -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- If `f - a` decays faster than every real power at infinity, the same is
true of `x ↦ f (u * x) - a` for every positive `u`. This is the asymptotic
input needed to rescale the kernels of a weak functional-equation pair. -/
theorem rapid_rescale (f : ℝ → ℂ) (a : ℂ)
    (hf : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop (fun x ↦ f x - a) (fun x : ℝ ↦ x ^ r)) {u : ℝ}
    (hu : 0 < u) (r : ℝ) :
    Asymptotics.IsBigO Filter.atTop (fun x ↦ f (u * x) - a) (fun x : ℝ ↦ x ^ r) := by
  have ht : Filter.Tendsto (fun x : ℝ ↦ u * x) Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos hu).2 Filter.tendsto_id
  have h := (hf r).comp_tendsto ht
  have heq :
    Filter.EventuallyEq Filter.atTop (fun x : ℝ ↦ (u * x) ^ r) (fun x : ℝ ↦ u ^ r * x ^ r) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
    exact Real.mul_rpow hu.le hx
  exact
    h.trans
      (heq.isBigO.trans
        ((Asymptotics.isBigO_refl (fun x : ℝ ↦ x ^ r) Filter.atTop).const_mul_left _))

/-- Rescale the kernels of a weak functional-equation pair by reciprocal
positive factors. Continuity of both kernels supplies local integrability;
their rapid decay is preserved by `rapid_rescale`. -/
noncomputable def rescaleWeakFEPair (P : WeakFEPair ℂ) (hPf : ContinuousOn P.f (Set.Ioi 0))
    (hPg : ContinuousOn P.g (Set.Ioi 0)) (u : ℝ) (hu : 0 < u) : WeakFEPair ℂ
    where
  f := fun x ↦ P.f (u * x)
  g := fun x ↦ P.g (u⁻¹ * x)
  k := P.k
  ε := P.ε * (u ^ (-P.k) : ℝ)
  f₀ := P.f₀
  g₀ := P.g₀
  hf_int :=
    (hPf.comp (continuous_const.mul continuous_id).continuousOn
          (fun x hx ↦ mul_pos hu hx)).locallyIntegrableOn
      measurableSet_Ioi
  hg_int :=
    (hPg.comp (continuous_const.mul continuous_id).continuousOn
          (fun x hx ↦ mul_pos (inv_pos.mpr hu) hx)).locallyIntegrableOn
      measurableSet_Ioi
  hk := P.hk
  hε := mul_ne_zero P.hε (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hu _).ne')
  h_feq x hx := by
    have heq : u * (1 / x) = 1 / (u⁻¹ * x) := by simp only [one_div, mul_inv_rev, inv_inv, mul_comm]
    rw [heq, P.h_feq _ (mul_pos (inv_pos.mpr hu) hx), Real.mul_rpow (inv_pos.mpr hu).le hx.le,
      Real.inv_rpow hu.le, ← Real.rpow_neg hu.le]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  hf_top := rapid_rescale P.f P.f₀ P.hf_top hu
  hg_top := rapid_rescale P.g P.g₀ P.hg_top (inv_pos.mpr hu)

end PseudoPrime.Analysis
