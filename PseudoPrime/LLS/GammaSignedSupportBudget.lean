/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSignedReciprocalBounds
public import PseudoPrime.LLS.GammaScaleJointBudget

/-! # Smaller exact support for the signed joint dual budget -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a scale x. Definition: the odd primes through floor(1+6 sqrt x).
Output: a finite prime set. Role: retain exactly all potentially positive signed dual excess. -/
noncomputable def gammaSignedSupportPrimeSet (x : ℝ) : Finset ℕ :=
  (Finset.Icc 3 ⌊1 + 6 * Real.sqrt x⌋₊).filter Nat.Prime

/-- Input: any real scale. Claim: the smaller support is contained in the former support.
Proof: compare the cutoffs and use monotonicity of the natural floor.
Role: restrict the existing scalar dual sum without changing its value. -/
theorem gamma_signed_support_subset (x : ℝ) :
    gammaSignedSupportPrimeSet x ⊆ Analysis.gammaRamifiedDualPrimeSet x := by
  intro p hp
  obtain ⟨hi, hp⟩ := Finset.mem_filter.mp hp
  obtain ⟨h3, hbound⟩ := Finset.mem_Icc.mp hi
  have hc : 1 + 6 * Real.sqrt x ≤ 1 + (79977719 / 6250000 : ℝ) * Real.sqrt x := by
    nlinarith only [Real.sqrt_nonneg x]
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h3, hbound.trans (Nat.floor_mono hc)⟩, hp⟩

/-- Input: logarithmic allowance L and x>=1. Claim: the dual budget equals its sum
over primes through 1+6 sqrt x. Proof: all removed terms vanish by the signed tail bound.
Role: reduce the finite scalar computation needed by witness separation. -/
theorem gamma_scale_signed_dual_budget_eq_small_support (L : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    gammaScaleSignedDualBudget L x =
      Analysis.gammaRamifiedDualParameter x * L +
        ∑ p ∈ gammaSignedSupportPrimeSet x,
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
              0 := by
  have he :=
    Finset.sum_subset (gamma_signed_support_subset x) (f := fun p : ℕ ↦
      Real.log p *
        max (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
          0)
      (fun p hp hn ↦ by
        obtain ⟨hi, hp⟩ := Finset.mem_filter.mp hp
        have h3 := (Finset.mem_Icc.mp hi).1
        have hfloor : ⌊1 + 6 * Real.sqrt x⌋₊ < p := by
          apply lt_of_not_ge
          intro hle
          exact hn (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h3, hle⟩, hp⟩)
        have hbig :=
          (Nat.floor_lt (by nlinarith only [Real.sqrt_nonneg x] : (0 : ℝ) ≤ 1 + 6 * Real.sqrt x)).mp
            hfloor
        rw [Analysis.gamma_ramified_signed_excess_eq_zero_of_six_sqrt hp.one_lt hx hbig, mul_zero])
  exact congrArg (fun z : ℝ ↦ Analysis.gammaRamifiedDualParameter x * L + z) he.symm

/-- Input: odd nonsquare n, log n<=L, and x>=4096.
Claim: the actual character budget is bounded by the smaller signed-support expression.
Proof: rewrite the established factor-free bound using exact support restriction.
Role: connect the improved Euler envelope to the actual witness comparison. -/
theorem gamma_joint_prefix_le_small_signed_support {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    {L b x : ℝ} (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn) b x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 +
            (Analysis.gammaRamifiedDualParameter x * L +
              ∑ p ∈ gammaSignedSupportPrimeSet x,
                Real.log p *
                  max
                    (Analysis.gammaRamifiedSignedCombinedCost p x -
                      Analysis.gammaRamifiedDualParameter x)
                    0) -
          2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
        7 / 60 := by
  have h := gamma_joint_prefix_le_factor_free_budget_small_scale (b := b) hn hns hlog hx
  rw [gammaFactorFreeJointBudget,
    gamma_scale_signed_dual_budget_eq_small_support L (by linarith only [hx])] at h
  exact h

end PseudoPrime.LLS
