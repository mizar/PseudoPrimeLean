/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaEulerSeed100
public import PseudoPrime.LLS.GammaEulerPrefixTransport

/-! # Prefix transport and actual character budgets from the certified seed -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Claim: the certified seed also bounds the prefix written with a real cutoff.
Proof: evaluate the natural floor. Role: supply the transport interface's exact type. -/
theorem gamma_seed100_real_prefix_lower :
    (317 / 100 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊(100 : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  simpa only [Nat.floor_ofNat] using Analysis.gamma_euler_prefix_lower_100

/-- Input: RH, a target cutoff at least one, boundary-tail bounds and an error cap.
Claim: 317/100+A-B-E bounds the target prefix below, with no seed-prefix assumption.
Proof: apply analytic transport to the kernel-checked seed.
Role: replace large finite prefix data by compact scalar boundary obligations. -/
theorem gamma_euler_prefix_lower_from_seed100 (hRH : RiemannHypothesis) {b A B E : ℝ} (hb : 1 ≤ b)
    (hA : A ≤ gammaEulerBoundaryTail 100) (hB : gammaEulerBoundaryTail b ≤ B)
    (hE : gammaEulerTailErrorBudget 100 + gammaEulerTailErrorBudget b ≤ E) :
    317 / 100 + A - B - E ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  exact
    gamma_euler_prefix_lower_of_transport_bounds hRH (by norm_num only : (1 : ℝ) ≤ 100) hb
      gamma_seed100_real_prefix_lower hA hB hE

/-- Input: RH, odd nonsquare n, log n<=L, x>=4096 and scalar boundary/error/dual caps.
Claim: the actual Jacobi joint budget has the displayed bound using the certified seed.
Proof: instantiate the actual prefix-transport comparison at cutoff 100.
Role: eliminate the seed-prefix field from the witness comparison. -/
theorem gamma_joint_prefix_le_from_seed100 (hRH : RiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {b A B E L x D : ℝ} (hb : 1 ≤ b) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x)
    (hA : A ≤ gammaEulerBoundaryTail 100) (hB : gammaEulerBoundaryTail b ≤ B)
    (hE : gammaEulerTailErrorBudget 100 + gammaEulerTailErrorBudget b ≤ E)
    (hD : gammaScaleSignedDualBudget L x ≤ D) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn) b x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + D - 2 * (317 / 100 + A - B - E) +
        7 / 60 := by
  exact
    gamma_joint_prefix_le_of_prefix_transport hRH hn hns (by norm_num only : (1 : ℝ) ≤ 100) hb hlog
      hx gamma_seed100_real_prefix_lower hA hB hE hD

end PseudoPrime.LLS
