/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-! Conversion between the meromorphic divisor and analytic multiplicity of entire functions. -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For an entire complex function, its divisor on the plane is its natural analytic order.
The conventions agree at infinite order: both assign zero to a locally zero function.
Convert the analytic divisor formula by separating finite order from infinite order.
This links divisor-weighted explicit formulas to completed-zero subtype sums. -/
theorem divisor_eq_natCast_analyticOrderNatAt {F : ℂ → ℂ} (hF : Differentiable ℂ F) (s : ℂ) :
    MeromorphicOn.divisor F Set.univ s = (analyticOrderNatAt F s : ℤ) := by
  have ha : AnalyticOnNhd ℂ F Set.univ := fun z _ ↦ hF.analyticAt z
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha (Set.mem_univ s)]
  change
    ((analyticOrderAt F s).map (fun k : ℕ ↦ (k : ℤ))).untop₀ = ((analyticOrderAt F s).toNat : ℤ)
  induction analyticOrderAt F s using ENat.recTopCoe
  · rfl
  · rfl

/-- The inverse-square analytic multiplicity is supported on the zero set.
At any nonzero value the analytic order is zero, even without analyticity assumptions.
This permits extension of the zero-subtype mass by zero to the whole plane. -/
private theorem analyticMultiplicityMass_support (F : ℂ → ℂ) :
    Function.support (fun z : ℂ ↦ (analyticOrderNatAt F z : ℝ) / ‖z‖ ^ 2) ⊆ {z : ℂ | F z = 0} := by
  intro z hz
  by_contra hn
  have ho : analyticOrderAt F z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hn)
  exact hz (by simp only [analyticOrderNatAt, ho, ENat.toNat_zero, Nat.cast_zero, zero_div])

/-- For an entire function, analytic and divisor inverse-square mass terms agree pointwise.
Convert the multiplicity and squared norm. This is the summand comparison in the mass bridge. -/
private theorem analyticMultiplicityMass_eq_divisor_term {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (z : ℂ) :
    (analyticOrderNatAt F z : ℝ) / ‖z‖ ^ 2 =
      (MeromorphicOn.divisor F Set.univ z : ℝ) / Complex.normSq z := by
  rw [divisor_eq_natCast_analyticOrderNatAt hF]
  simp only [Int.cast_natCast, ← Complex.norm_mul_self_eq_normSq, pow_two]

/-- The zero-subtype analytic mass of an entire function equals its divisor-weighted mass.
Extend by zero outside the zero set, then compare each summand.
This identity uses the same default at infinite order and does not assert summability.
It connects general completed-zero mass to the existing character divisor estimates. -/
theorem tsum_zeroMultiplicity_eq_divisor {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    (∑' z : { z : ℂ // F z = 0 }, (analyticOrderNatAt F (z : ℂ) : ℝ) / ‖(z : ℂ)‖ ^ 2) =
      ∑' z : ℂ, (MeromorphicOn.divisor F Set.univ z : ℝ) / Complex.normSq z := by
  change (∑' z : {z : ℂ | F z = 0}, (analyticOrderNatAt F (z : ℂ) : ℝ) / ‖(z : ℂ)‖ ^ 2) = _
  rw [tsum_subtype_eq_of_support_subset (analyticMultiplicityMass_support F)]
  exact tsum_congr (analyticMultiplicityMass_eq_divisor_term hF)

end PseudoPrime.AnalyticNumberTheory.General
