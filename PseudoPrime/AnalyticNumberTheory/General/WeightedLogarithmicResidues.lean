/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.Boundary
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Analytic.Order

/-!
# Weighted logarithmic-derivative residues

Finite analytic order gives a logarithmic derivative with a simple principal part.
An arbitrary analytic weight multiplies the residue by its value at the zero.
These local square certificates feed finite rectangle residue assembly.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For an analytic function of finite order at `c`, factor off its vanishing power.
The remaining analytic unit has nonzero value at `c`; differentiating the factorization
gives multiplicity divided by `s-c` plus the unit's logarithmic derivative.
This expansion supplies local residue certificates without any special L-function assumptions. -/
theorem exists_logDeriv_local_expansion {F : ℂ → ℂ} {c : ℂ} (hF : AnalyticAt ℂ F c)
    (hfinite : analyticOrderAt F c ≠ ⊤) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g c ∧
        g c ≠ 0 ∧
        Filter.EventuallyEq (nhdsWithin c ({c}ᶜ : Set ℂ)) (logDeriv F)
          (fun s => (analyticOrderNatAt F c : ℂ) / (s - c) + logDeriv g s) := by
  obtain ⟨g, hg, hg0, hfactor⟩ := hF.analyticOrderAt_ne_top.mp hfinite
  refine ⟨g, hg, hg0, ?_⟩
  have hlog := (logDeriv_congr_nhds hfactor).filter_mono (nhdsWithin_le_nhds (s := ({c}ᶜ : Set ℂ)))
  have hga := hg.eventually_analyticAt.filter_mono (nhdsWithin_le_nhds (s := ({c}ᶜ : Set ℂ)))
  have hgn :=
    ((hg.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hg0).filter_mono
      (nhdsWithin_le_nhds (s := ({c}ᶜ : Set ℂ)))
  filter_upwards [hlog, hga, hgn, eventually_mem_nhdsWithin] with s hs hgs hgns hsc
  simp only [smul_eq_mul] at hs
  rw [hs]
  change logDeriv ((fun s => (s - c) ^ analyticOrderNatAt F c) * g) s = _
  have hd : DifferentiableAt ℂ (fun s : ℂ => s - c) s := differentiableAt_id.sub_const c
  rw [logDeriv_mul s]
  · rw [logDeriv_fun_pow hd]
    simp only [logDeriv_apply]
    rw [deriv_sub_const]
    simp only [deriv_id'', one_div, add_left_inj]
    ring
  · exact pow_ne_zero _ (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsc))
  · exact hgns
  · exact hd.pow _
  · exact hgs.differentiableAt

/-- For a local logarithmic-derivative expansion of multiplicity `m` and analytic weight
`W`, every sufficiently small square has residue `-m * W c` for `-logDeriv F * W`.
Multiply by `s-c` to remove the pole and apply the analytic square Cauchy formula.
This certificate is used when assembling weighted finite contour identities. -/
theorem exists_radius_weighted_logDeriv_residue {F g W : ℂ → ℂ} {c : ℂ} {m : ℕ}
    (hg : AnalyticAt ℂ g c) (hg0 : g c ≠ 0) (hW : AnalyticAt ℂ W c)
    (hlog :
      Filter.EventuallyEq (nhdsWithin c ({c}ᶜ : Set ℂ)) (logDeriv F)
        (fun s => (m : ℂ) / (s - c) + logDeriv g s)) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral (fun s => -logDeriv F s * W s)
                (RectangleGeometry.centeredSquareLower c r)
                (RectangleGeometry.centeredSquareUpper c r) =
              2 * Real.pi * Complex.I * (-(m : ℂ) * W c) := by
  let H : ℂ → ℂ := fun s => -((m : ℂ) + (s - c) * logDeriv g s) * W s
  have hH : AnalyticAt ℂ H c :=
    (analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul (hg.deriv.div hg hg0))).neg.mul
      hW
  have heq :
    Filter.EventuallyEq (nhdsWithin c ({c}ᶜ : Set ℂ)) (fun s => (s - c) * (-logDeriv F s * W s))
      H := by
    filter_upwards [hlog, eventually_mem_nhdsWithin] with s hs hsc
    rw [hs]
    dsimp only [H]
    field_simp [sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsc)]
  obtain ⟨R, hR, hr⟩ :=
    RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul hH heq
  refine ⟨R, hR, fun r hpos hle => ?_⟩
  rw [hr r hpos hle]
  simp only [H, sub_self, zero_mul, add_zero]

end PseudoPrime.AnalyticNumberTheory.General
