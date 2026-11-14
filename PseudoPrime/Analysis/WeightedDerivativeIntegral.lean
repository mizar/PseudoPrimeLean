/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # Integral bounds from a weighted derivative bound -/

public section

namespace PseudoPrime.Analysis

/-- On a nonnegative ordered interval, a nonnegative continuous derivative
with `x * f' x ≤ b * f' b` gives a lower bound for the integral of f.
Integrate by parts against `x - a` and bound the remaining integrand. -/
theorem integral_lower_of_weighted_deriv {f f' : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x) (hc : ContinuousOn f' (Set.Icc a b))
    (hn : ∀ x ∈ Set.Icc a b, 0 ≤ f' x) (hm : ∀ x ∈ Set.Icc a b, x * f' x ≤ b * f' b) :
    (b - a) * f b - b * (b - a) * f' b ≤ ∫ x in a..b, f x := by
  have hfcont : ContinuousOn f (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have hdint : IntervalIntegrable f' MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hc
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (u := fun x : ℝ ↦ x - a) (v := f)
      (u' := fun _ : ℝ ↦ 1) (v' := f') ((continuous_id.sub continuous_const).continuousOn) hfcont
      (fun x hx ↦ by simpa only [id_eq] using (hasDerivAt_id x).sub_const a)
      (fun x hx ↦ by
        rw [min_eq_left hab, max_eq_right hab] at hx
        exact hf x ⟨hx.1.le, hx.2.le⟩)
      intervalIntegrable_const hdint
  simp only [sub_self, zero_mul, one_mul] at hparts
  have hprod : IntervalIntegrable (fun x ↦ (x - a) * f' x) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact (continuous_id.sub continuous_const).continuousOn.mul hc
  have hbound :=
    intervalIntegral.integral_mono_on (g := fun _ : ℝ ↦ b * f' b) hab hprod intervalIntegrable_const
      (fun x hx ↦ by
        have h := mul_nonneg ha (hn x hx)
        have h' := hm x hx
        nlinarith only [h, h'])
  rw [intervalIntegral.integral_const, smul_eq_mul] at hbound
  nlinarith only [hparts, hbound]

/-- An integrable function inherits the limiting lower bound on `[0,b]`
from bounds on all positive left endpoints. Continuity of the interval
integral in its endpoint permits an integrable singularity at zero. -/
theorem integral_lower_of_positive_endpoints {f : ℝ → ℝ} {b F D : ℝ} (hb : 0 < b)
    (hf : IntervalIntegrable f MeasureTheory.volume 0 b)
    (hbound : ∀ a : ℝ, 0 < a → a ≤ b → (b - a) * F - b * (b - a) * D ≤ ∫ x in a..b, f x) :
    b * F - b ^ 2 * D ≤ ∫ x in (0 : ℝ)..b, f x := by
  have hm : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), a ∈ Set.uIcc 0 b := by
    have hpos : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < a := self_mem_nhdsWithin
    have hlt : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), a < b :=
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos, hlt] with a ha hab
    rw [Set.uIcc_of_le hb.le]
    exact ⟨ha.le, hab.le⟩
  have ht :
    Filter.Tendsto (fun a : ℝ ↦ a) (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.uIcc 0 b)) :=
    tendsto_nhdsWithin_iff.mpr ⟨Filter.tendsto_id.mono_left nhdsWithin_le_nhds, hm⟩
  have hc := intervalIntegral.continuousOn_primitive_interval' hf (Set.right_mem_uIcc)
  have hzero : (0 : ℝ) ∈ Set.uIcc 0 b := Set.left_mem_uIcc
  have htint := ((hc 0 hzero).tendsto.comp ht).neg
  have hInt :
    Filter.Tendsto (fun a : ℝ ↦ ∫ x in a..b, f x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x in (0 : ℝ)..b, f x)) := by
    have hfun : (fun a : ℝ ↦ ∫ x in a..b, f x) = (fun a : ℝ ↦ -(∫ x in b..a, f x)) := by
      funext a
      exact intervalIntegral.integral_symm b a
    rw [hfun]
    have he : -(∫ x in b..(0 : ℝ), f x) = ∫ x in (0 : ℝ)..b, f x := by
      rw [intervalIntegral.integral_symm 0 b, neg_neg]
    rw [← he]
    exact htint
  have hL :
    Filter.Tendsto (fun a : ℝ ↦ (b - a) * F - b * (b - a) * D) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (b * F - b ^ 2 * D)) := by
    have hc' : Continuous (fun a : ℝ ↦ (b - a) * F - b * (b - a) * D) :=
      ((continuous_const.sub continuous_id).mul continuous_const).sub
        ((continuous_const.mul (continuous_const.sub continuous_id)).mul continuous_const)
    have ht' :=
      (hc'.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa only [sub_zero, pow_two, mul_assoc] using ht'
  apply le_of_tendsto_of_tendsto hL hInt
  have hpos : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < a := self_mem_nhdsWithin
  have hlt : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), a < b :=
    (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, hlt] with a ha hab
  exact hbound a ha hab.le

end PseudoPrime.Analysis
