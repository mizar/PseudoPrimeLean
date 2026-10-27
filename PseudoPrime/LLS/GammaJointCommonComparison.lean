/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaRetainedCommonCostBounds
public import PseudoPrime.LLS.JointRampPrincipalWitnessBounds

/-! # Joint principal and real-axis Euler bounds at arbitrary prefix scales -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Complete arbitrary-prefix margin with a joint ramp-principal lower bound and a
shared Euler-Gamma cost cap. This keeps the common arithmetic error combined
before estimating it. Nonnegative margin is later used for witness extraction. -/
noncomputable def gammaJointCommonSeparation {q : ℕ} (Q : ℕ) (χ : DirichletCharacter ℂ q)
    (b x C : ℝ) : ℝ :=
  jointRampPrincipalLower x -
    (gammaJointPrefixLocalBudget χ b x + C + ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
      43 * x ^ (-9 / 16 : ℝ))

/-- At x>0 the new margin equals the former signed-principal common-cap margin
plus the displayed positive saving. Reuse the exact joint principal identity;
all character and local-prefix costs cancel without additional hypotheses. -/
theorem gammaJointCommonSeparation_eq_signed {q : ℕ} (Q : ℕ) (χ : DirichletCharacter ℂ q) (b C : ℝ)
    {x : ℝ} (hx : 0 < x) :
    gammaJointCommonSeparation Q χ b x C =
      gammaJointPrefixSeparationWithCommonCap Q χ b x C (gammaSignedVariationPrincipalCap x) +
        2029 / 16000 +
        ((42297 / 12500 : ℝ) * Real.log x + (23907 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
            8757 / 3200) /
          Real.sqrt x := by
  have h := jointRampPrincipalGap_eq_signed (A := 1) (C := 0) hx
  dsimp only [jointRampPrincipalGap, twoPoleSignedVariationGap, twoPolePrincipalCapGap] at h
  dsimp only [gammaJointCommonSeparation, gammaJointPrefixSeparationWithCommonCap]
  linarith only [h]

/-- At x>=1 the new arbitrary-prefix margin exceeds the former common-cap margin
by more than 1/8. Transfer the joint principal improvement without a sampled bound. -/
theorem gammaJointCommonSeparation_gt_signed {q : ℕ} (Q : ℕ) (χ : DirichletCharacter ℂ q) (b C : ℝ)
    {x : ℝ} (hx : 1 ≤ x) :
    gammaJointPrefixSeparationWithCommonCap Q χ b x C (gammaSignedVariationPrincipalCap x) + 1 / 8 <
      gammaJointCommonSeparation Q χ b x C := by
  have h := jointRampPrincipalGap_gt_signed (A := 1) (C := 0) hx
  dsimp only [jointRampPrincipalGap, twoPoleSignedVariationGap, twoPolePrincipalCapGap] at h
  dsimp only [gammaJointCommonSeparation, gammaJointPrefixSeparationWithCommonCap]
  linarith only [h]

/-- Under GRH and quadratic nonprincipal data, admissible scale and prefix, a common
Euler-Gamma cost cap and nonnegative joint margin contradict unit-prime triviality.
Use the actual joint lower bound directly; no separate principal-series cap remains. -/
theorem gamma_prime_trivial_false_of_joint_common {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q)
    (hqQ : q ≤ Q) (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b C : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hCost :
      (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) +
          PaperStatements.gammaSignedGammaCost χ.primitiveCharacter.gammaFactor <
        C)
    (hgap : 0 ≤ gammaJointCommonSeparation Q χ b x C) :
    ¬(∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  intro hsmall
  have hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p q → χ p = 1 := fun p hp hpb hc ↦
    hsmall p hp (hp.coprime_iff_not_dvd.mp hc) (hpb.trans hbx)
  have hC := gamma_primitive_sum_add_local_lt_common_cost hQ hqQ χ hne hGRH hx hb hone hCost
  have hx1 : 1 ≤ x := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hx
  have hJ := jointRampPrincipalLower_le_actual hGRH.riemann hx1
  have hN := gamma_ramp_no_witness_comparison χ hquad (zero_lt_one.trans_le hx1) hsmall
  dsimp only [gammaJointCommonSeparation] at hgap
  linarith only [hC, hJ, hN, hgap]

/-- Under the joint common-margin hypotheses a unit prime of value minus one
exists through 99x/40. Contradict prime triviality, then use quadraticity and
nonvanishing on units to identify the character value. -/
theorem exists_prime_neg_one_of_joint_common {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q) (hqQ : q ≤ Q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b C : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hCost :
      (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) +
          PaperStatements.gammaSignedGammaCost χ.primitiveCharacter.gammaFactor <
        C)
    (hgap : 0 ≤ gammaJointCommonSeparation Q χ b x C) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  classical
  have hex : ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
    by_contra hnone
    apply gamma_prime_trivial_false_of_joint_common hQ hqQ χ hquad hne hGRH hx hb hbx hCost hgap
    intro p hp hd hpb
    exact Classical.byContradiction (fun hv ↦ hnone ⟨p, hp, hd, hpb, hv⟩)
  obtain ⟨p, hp, hd, hpb, hv⟩ := hex
  have hz : χ p ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr
      ((ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd))
  refine ⟨p, hp, hd, hpb, ?_⟩
  rcases hquad (p : ZMod q) with h0 | h1 | hm
  · exact False.elim (hz h0)
  · exact False.elim (hv h1)
  · exact hm

/-- For an even quadratic character, specialize the common cost to 541/50.
Primitive parity supplies the proved signed Euler-Gamma cap; apply the generic
unit-prime witness theorem at arbitrary admissible scale and prefix. -/
theorem exists_prime_neg_one_of_even_joint_common {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q)
    (hqQ : q ≤ Q) (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1)
    (heven : χ.Even) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ}
    (hx : 2 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 ≤ gammaJointCommonSeparation Q χ b x (541 / 50)) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  have hp := (NumberTheory.primitiveCharacter_even_iff χ).mpr heven
  exact
    exists_prime_neg_one_of_joint_common hQ hqQ χ hquad hne hGRH hx hb hbx
      (gamma_even_common_cost_lt_precise hGRH.riemann hp) hgap

/-- Factor-free scalar margin using the joint ramp-principal lower bound and
the existing factor-free prefix budget. The logarithmic input endpoint is L;
later bounds transfer this margin to every odd nonsquare input with log n<=L. -/
noncomputable def gammaJointFactorFreeSeparation (L b x : ℝ) : ℝ :=
  jointRampPrincipalLower x -
    (gammaFactorFreeJointBudget L b x + 541 / 50 + ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x +
      43 * x ^ (-9 / 16 : ℝ))

/-- At x>0 the scalar margin equals its signed-principal predecessor plus the
retained 9/50 common-cost credit and the explicit joint principal saving.
Expand the scalar definitions and reuse the exact common-error identity. -/
theorem gammaJointFactorFreeSeparation_eq_signed (L b : ℝ) {x : ℝ} (hx : 0 < x) :
    gammaJointFactorFreeSeparation L b x =
      gammaSignedPrincipalFactorFreeSeparation L b x + 9 / 50 + 2029 / 16000 +
        ((42297 / 12500 : ℝ) * Real.log x + (23907 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
            8757 / 3200) /
          Real.sqrt x := by
  have h := jointRampPrincipalGap_eq_signed (A := 1) (C := 0) hx
  dsimp only [jointRampPrincipalGap, twoPoleSignedVariationGap, twoPolePrincipalCapGap] at h
  dsimp only [gammaJointFactorFreeSeparation, gammaSignedPrincipalFactorFreeSeparation]
  linarith only [h]

/-- At x>=1 the scalar margin improves the retained signed-principal margin by
more than 1/8. This permits weaker numerical separation hypotheses at fixed scale. -/
theorem gammaJointFactorFreeSeparation_gt_signed (L b : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    gammaSignedPrincipalFactorFreeSeparation L b x + 9 / 50 + 1 / 8 <
      gammaJointFactorFreeSeparation L b x := by
  have h := jointRampPrincipalGap_gt_signed (A := 1) (C := 0) hx
  dsimp only [jointRampPrincipalGap, twoPoleSignedVariationGap, twoPolePrincipalCapGap] at h
  dsimp only [gammaJointFactorFreeSeparation, gammaSignedPrincipalFactorFreeSeparation]
  linarith only [h]

/-- For odd nonsquare n with log n<=L, x>=4096 and the displayed pole-level bound,
the scalar margin is at most the actual joint margin plus 7/60. Transfer the
existing local and pole budgets while keeping the common principal lower bound. -/
theorem gammaJointFactorFreeSeparation_le_actual {n Q : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    {L b x : ℝ} (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hlogQ : Real.log Q ≤ L + 7 / 5) :
    gammaJointFactorFreeSeparation L b x ≤
      gammaJointCommonSeparation Q (NumberTheory.complexQuadraticCharacter n hn) b x (541 / 50) +
        7 / 60 := by
  have hJ := gamma_joint_prefix_le_factor_free_budget_small_scale (b := b) hn hns hlog hx
  have hN :
    ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x ≤ ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x :=
    div_le_div_of_nonneg_right (by linarith only [hlogQ]) (Real.sqrt_nonneg x)
  dsimp only [gammaJointFactorFreeSeparation, gammaJointCommonSeparation]
  linarith only [hJ, hN]

end PseudoPrime.LLS
