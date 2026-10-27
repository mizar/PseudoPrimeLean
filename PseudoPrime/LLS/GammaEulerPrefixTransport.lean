/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaEulerTailErrorBounds
public import PseudoPrime.LLS.GammaScaleJointBudget

/-! # Analytic transport of signed Euler prefixes between finite cutoffs -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a real cutoff a. Definition: the two signed lower boundary terms plus
the explicit main tail. Output: the non-prefix part of the Euler mass center.
Role: cancel the infinite Euler mass between two finite cutoffs. -/
noncomputable def gammaEulerBoundaryTail (a : ℝ) : ℝ :=
  -Analysis.gammaResolventEulerWeight a * Chebyshev.psi a +
    gammaEulerLogSlope a * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a +
    gammaEulerTailMain a

/-- Input: RH and two cutoffs at least one. Claim: the prefix difference equals
the difference of signed boundary tails and errors. Proof: subtract the two mass identities.
Role: avoid a large finite prefix or an independently certified infinite Euler mass. -/
theorem gamma_euler_prefix_transport_identity (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) -
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m) =
      gammaEulerBoundaryTail a - gammaEulerBoundaryTail b + gammaEulerTailError a -
        gammaEulerTailError b := by
  have h1 := gammaEulerMass_eq_center_add_error hRH ha
  have h2 := gammaEulerMass_eq_center_add_error hRH hb
  dsimp only [gammaEulerMassCenter, gammaEulerBoundaryTail] at *
  linarith only [h1, h2]

/-- Input: RH and two cutoffs at least one. Claim: the boundary-tail difference
minus both error budgets bounds the prefix gain below. Proof: retain the lower first error
and upper second error. Role: analytically transport a small prefix to a larger cutoff. -/
theorem gamma_euler_prefix_transport_lower (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    gammaEulerBoundaryTail a - gammaEulerBoundaryTail b - gammaEulerTailErrorBudget a -
        gammaEulerTailErrorBudget b ≤
      (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) -
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m) := by
  have hi := gamma_euler_prefix_transport_identity hRH ha hb
  have he1 := abs_le.mp (gammaEulerTailError_abs_le_budget hRH ha)
  have he2 := abs_le.mp (gammaEulerTailError_abs_le_budget hRH hb)
  linarith only [hi, he1.1, he2.2]

/-- Input: RH, a small prefix lower bound, signed boundary-tail bounds and an error cap.
Claim: c+A-B-E bounds the target prefix below. Proof: combine the transport inequalities.
Role: expose compact scalar certificate obligations instead of listing the large prefix. -/
theorem gamma_euler_prefix_lower_of_transport_bounds (hRH : RiemannHypothesis) {a b c A B E : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : c ≤ ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m)
    (hA : A ≤ gammaEulerBoundaryTail a) (hB : gammaEulerBoundaryTail b ≤ B)
    (hE : gammaEulerTailErrorBudget a + gammaEulerTailErrorBudget b ≤ E) :
    c + A - B - E ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h := gamma_euler_prefix_transport_lower hRH ha hb
  linarith only [h, hc, hA, hB, hE]

/-- Input: nonnegative lower bounds for the Euler weight, psi and smoothed sum,
a nonpositive upper slope, and an upper main tail. Claim: the resulting signed expression
bounds the boundary tail above. Proof: preserve both negative products.
Role: use analytic arithmetic bounds at the large target cutoff. -/
theorem gamma_euler_boundary_tail_upper {b w ψ s v M : ℝ} (hw0 : 0 ≤ w)
    (hw : w ≤ Analysis.gammaResolventEulerWeight b) (hψ0 : 0 ≤ ψ) (hψ : ψ ≤ Chebyshev.psi b)
    (hs : gammaEulerLogSlope b ≤ s) (hs0 : s ≤ 0) (hv0 : 0 ≤ v)
    (hv : v ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b)
    (hM : gammaEulerTailMain b ≤ M) : gammaEulerBoundaryTail b ≤ -w * ψ + s * v + M := by
  have hp := mul_le_mul hw hψ hψ0 (hw0.trans hw)
  have h1 := mul_le_mul_of_nonpos_left hv (hs.trans hs0)
  have h2 := mul_le_mul_of_nonneg_right hs hv0
  dsimp only [gammaEulerBoundaryTail]
  linarith only [hp, h1, h2, hM]

/-- Input: RH, prefix-transport scalar bounds and an upper signed dual budget.
Claim: the actual factor-free joint budget is bounded with the transported prefix gain.
Proof: substitute the proved prefix lower bound before multiplying by negative two.
Role: connect small-prefix transport to the established witness separation. -/
theorem gamma_factor_free_joint_budget_le_of_prefix_transport (hRH : RiemannHypothesis)
    {a b c A B E L x D : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : c ≤ ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m)
    (hA : A ≤ gammaEulerBoundaryTail a) (hB : gammaEulerBoundaryTail b ≤ B)
    (hE : gammaEulerTailErrorBudget a + gammaEulerTailErrorBudget b ≤ E)
    (hD : gammaScaleSignedDualBudget L x ≤ D) :
    gammaFactorFreeJointBudget L b x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + D - 2 * (c + A - B - E) := by
  have hp := gamma_euler_prefix_lower_of_transport_bounds hRH ha hb hc hA hB hE
  dsimp only [gammaFactorFreeJointBudget]
  linarith only [hp, hD]

/-- Input: RH, an odd nonsquare input with log n<=L and x>=4096, and compact
prefix-transport and dual bounds. Claim: these bound the actual Jacobi joint budget.
Proof: compose the actual-to-factor-free comparison with prefix transport.
Role: replace a large prefix payload in the witness comparison by small-cutoff data. -/
theorem gamma_joint_prefix_le_of_prefix_transport (hRH : RiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {a b c A B E L x D : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hlog : Real.log n ≤ L)
    (hx : 4096 ≤ x) (hc : c ≤ ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m)
    (hA : A ≤ gammaEulerBoundaryTail a) (hB : gammaEulerBoundaryTail b ≤ B)
    (hE : gammaEulerTailErrorBudget a + gammaEulerTailErrorBudget b ≤ E)
    (hD : gammaScaleSignedDualBudget L x ≤ D) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn) b x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + D - 2 * (c + A - B - E) + 7 / 60 := by
  have hj := gamma_joint_prefix_le_factor_free_budget_small_scale (b := b) hn hns hlog hx
  have ht := gamma_factor_free_joint_budget_le_of_prefix_transport hRH ha hb hc hA hB hE hD
  linarith only [hj, ht]

end PseudoPrime.LLS
