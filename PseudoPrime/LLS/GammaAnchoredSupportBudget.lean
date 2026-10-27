/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaAnchoredReciprocalBounds
public import PseudoPrime.LLS.GammaSignedSupportBudget
public import PseudoPrime.LLS.GammaEulerBoundary89100

/-! # Exact anchored support for the actual signed dual budget -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: scale x. Definition: odd primes through floor(1+(71/25)sqrt x).
Output: a finite support. Role: retain all potentially positive signed excess at x>=100. -/
noncomputable def gammaAnchoredSupportPrimeSet (x : ℝ) : Finset ℕ :=
  (Finset.Icc 3 ⌊1 + (71 / 25 : ℝ) * Real.sqrt x⌋₊).filter Nat.Prime

/-- Input: any scale. Claim: the anchored support is contained in the six-root support.
Proof: compare nonnegative square-root cutoffs and natural floors.
Role: restrict the established exact dual sum. -/
theorem gamma_anchored_support_subset (x : ℝ) :
    gammaAnchoredSupportPrimeSet x ⊆ gammaSignedSupportPrimeSet x := by
  intro p hp
  obtain ⟨hi, hp⟩ := Finset.mem_filter.mp hp
  obtain ⟨h3, hb⟩ := Finset.mem_Icc.mp hi
  have hc : 1 + (71 / 25 : ℝ) * Real.sqrt x ≤ 1 + 6 * Real.sqrt x := by
    nlinarith only [Real.sqrt_nonneg x]
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h3, hb.trans (Nat.floor_mono hc)⟩, hp⟩

/-- Input: real L and x>=100. Claim: the actual signed dual budget equals its sum over
the smaller anchored support. Proof: the removed excess terms vanish exactly.
Role: reduce numerical certification without replacing the finite summands by coarse costs. -/
theorem gamma_scale_signed_dual_budget_eq_anchored_support (L : ℝ) {x : ℝ} (hx : 100 ≤ x) :
    gammaScaleSignedDualBudget L x =
      Analysis.gammaRamifiedDualParameter x * L +
        ∑ p ∈ gammaAnchoredSupportPrimeSet x,
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
              0 := by
  have he :=
    Finset.sum_subset (gamma_anchored_support_subset x) (f := fun p : ℕ ↦
      Real.log p *
        max (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
          0)
      (fun p hp hn ↦ by
        obtain ⟨hi, hp⟩ := Finset.mem_filter.mp hp
        have h3 := (Finset.mem_Icc.mp hi).1
        have hfloor : ⌊1 + (71 / 25 : ℝ) * Real.sqrt x⌋₊ < p := by
          apply lt_of_not_ge
          intro hle
          exact hn (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h3, hle⟩, hp⟩)
        have hbig :=
          (Nat.floor_lt
                (by nlinarith only [Real.sqrt_nonneg x] :
                  (0 : ℝ) ≤ 1 + (71 / 25 : ℝ) * Real.sqrt x)).mp
            hfloor
        rw [Analysis.gamma_ramified_signed_excess_eq_zero_of_anchor20 hp.one_lt hx hbig, mul_zero])
  rw [gamma_scale_signed_dual_budget_eq_small_support L (by linarith only [hx])]
  exact congrArg (fun z : ℝ ↦ Analysis.gammaRamifiedDualParameter x * L + z) he.symm

/-- Input: RH, odd nonsquare n, log n<=L, x>=4096 and b>=89100.
Claim: the actual joint budget is bounded by the smaller-support expression and proved prefix gain.
Proof: rewrite the half-line prefix comparison by exact support restriction.
Role: connect the refined large-prime envelope to the witness comparison. -/
theorem gamma_joint_prefix_le_anchored_support (hRH : RiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {b L x : ℝ} (hb : 89100 ≤ b) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn) b x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 +
            (Analysis.gammaRamifiedDualParameter x * L +
              ∑ p ∈ gammaAnchoredSupportPrimeSet x,
                Real.log p *
                  max
                    (Analysis.gammaRamifiedSignedCombinedCost p x -
                      Analysis.gammaRamifiedDualParameter x)
                    0) -
          28923 / 2500 +
        7 / 60 := by
  have h :=
    gamma_joint_prefix89100_bound_halfline hRH hn hns hb hlog hx
      (le_refl (gammaScaleSignedDualBudget L x))
  rw [gamma_scale_signed_dual_budget_eq_anchored_support L (by linarith only [hx])] at h
  exact h

end PseudoPrime.LLS
