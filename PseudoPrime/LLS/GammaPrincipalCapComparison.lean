/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSignedVariationPrincipalBounds
public import PseudoPrime.LLS.GammaJointPrefixComparison

/-! # Joint prefix comparisons with an arbitrary actual principal upper cap -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: ambient level, character, prefix, scale, Gamma cap and actual principal cap P.
Definition: twice the paired ramp lower bound minus P and the joint character budget.
Output: a sufficient scalar witness margin. Role: admit improved principal bounds
without changing the conductor or ramified-cost interfaces. -/
noncomputable def gammaJointPrefixSeparationWithPrincipalCap {q : ℕ} (Q : ℕ)
    (χ : DirichletCharacter ℂ q) (b x A P : ℝ) : ℝ :=
  2 *
      ((∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x -
        gammaRampPairedErrorNumerator x / Real.sqrt x) -
    P -
    (gammaJointPrefixLocalBudget χ b x + 25 / 2 + A + ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
      43 * x ^ (-9 / 16 : ℝ))

/-- Input: GRH, nonprincipal quadratic character data and an upper cap for the
actual principal Gamma sum. A nonnegative displayed margin contradicts prime
triviality through the ramp cutoff. Combine the joint character estimate and
actual ramp comparison. Role: connect sharper principal estimates to witnesses. -/
theorem gamma_ramp_prime_trivial_false_of_principal_cap {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q)
    (hqQ : q ≤ Q) (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b A P : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hA : PaperStatements.gammaSignedGammaCost χ.primitiveCharacter.gammaFactor ≤ A)
    (hP :
      (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤ P)
    (hgap : 0 ≤ gammaJointPrefixSeparationWithPrincipalCap Q χ b x A P) :
    ¬(∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  intro hsmall
  have hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p q → χ p = 1 := fun p hp hpb hcop ↦
    hsmall p hp (hp.coprime_iff_not_dvd.mp hcop) (hpb.trans hbx)
  have hC := gamma_primitive_sum_add_local_lt_joint_prefix_cap hQ hqQ χ hne hGRH hx hb hone hA
  have hx1 : 1 ≤ x := le_trans (by norm_num only) hx
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann hx1
  have hN := gamma_ramp_no_witness_comparison χ hquad (zero_lt_one.trans_le hx1) hsmall
  dsimp only [gammaJointPrefixSeparationWithPrincipalCap] at hgap
  linarith only [hC, hT, hP, hN, hgap]

/-- Input: a scale x. Definition: the improved upper bound for the normalized
principal Gamma sum. Role: use the signed-variation estimate in joint margins. -/
noncomputable def gammaSignedVariationPrincipalCap (x : ℝ) : ℝ :=
  Real.sqrt x + (Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800) / Real.sqrt x

/-- Under RH and x >= 1, the actual principal Gamma sum is below the named cap.
Apply the signed-variation theorem. Role: discharge the principal input in witness extraction. -/
theorem gamma_level_one_sum_le_signed_variation_cap (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤
      gammaSignedVariationPrincipalCap x := by
  exact gamma_level_one_sum_upper_signed_variation hRH hx

/-- At every scale x >= 1, the signed-variation principal cap is strictly
smaller than the previous variable-scale upper bound. Compare the numerators
using log(x) >= 0. Role: certify that the new witness margin is a strict improvement. -/
theorem gamma_signed_variation_principal_cap_lt_variable {x : ℝ} (hx : 1 ≤ x) :
    gammaSignedVariationPrincipalCap x <
      Real.sqrt x +
        (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x := by
  have hn :
    Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800 <
      Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10 := by
    nlinarith only [Real.sqrt_nonneg x, Real.log_nonneg hx]
  simpa only [gammaSignedVariationPrincipalCap, add_comm] using
    add_lt_add_left (div_lt_div_of_pos_right hn (Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)))
      (Real.sqrt x)

end PseudoPrime.LLS
