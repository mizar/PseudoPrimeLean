/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaPrincipalCapComparison
public import PseudoPrime.LLS.GammaSignedPrincipalCellCertificate

/-! # Retain signed pole and Gamma precision in the common Euler cost -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: any even Dirichlet character. Claim: its signed Gamma cost is at most
-15709/10000. Identify the real Gamma derivatives with the already certified
signed digamma expression. Role: retain precision previously rounded to -3/2. -/
theorem gamma_even_signed_cost_le_precise {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Even) :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum ≤
      -(15709 / 10000 : ℝ) := by
  have ht := AnalyticNumberTheory.Gamma.signed_digamma_0_le_precise
  have hm :
    (Analysis.gammaResolventCoefficients.map
        (fun ab ↦ (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)) =
      (Analysis.gammaResolventCoefficients.map
        (fun ab ↦
          (ab.2 : ℝ) *
            (((Complex.digamma ((((1 / 2 : ℝ) + (ab.1 : ℝ) + 0) / 2) : ℂ)).re - Real.log Real.pi) /
              2))) := by
    apply List.map_congr_left
    intro ab hab
    have ha :=
      Rat.cast_lt (K := ℝ) |>.mpr
        (List.forall_iff_forall_mem.mp Analysis.gammaResolvent_scales_gt_half ab hab)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at ha
    have hh :=
      AnalyticNumberTheory.DirichletLFunction.re_gammaFactor_even he
        (show (0 : ℝ) < 1 / 2 + (ab.1 : ℝ) by linarith only [ha])
    simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Complex.ofReal_zero, add_zero] using congrArg (fun z : ℝ ↦ (ab.2 : ℝ) * z) hh
  rw [hm]
  exact ht

/-- Claim: the signed pole sum is less than 13961/1000. Evaluate the ten rational
nodes exactly. Role: avoid rounding the pole allowance to fourteen. -/
theorem gamma_resolvent_pole_sum_lt_precise :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦ (ab.2 : ℝ) * (1 / ((1 / 2 : ℝ) + (ab.1 : ℝ)) + 1 / ((ab.1 : ℝ) - 1 / 2)))).sum <
      (13961 / 1000 : ℝ) := by
  norm_num only [Analysis.gammaResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]

/-- Input: RH. Claim: the full nonnegative resolvent Euler mass is less than
123901/10000. Combine xi zero-mass positivity with the precise poles and even
Gamma cost. Role: strengthen the principal Euler budget without finite prime tables. -/
theorem gamma_principal_euler_lt_precise (hRH : RiemannHypothesis) :
    (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) < (123901 / 10000 : ℝ) := by
  have he := AnalyticNumberTheory.RiemannXi.gammaResolvent_euler_le_poles_gamma hRH
  have hp := gamma_resolvent_pole_sum_lt_precise
  have hg :=
    gamma_even_signed_cost_le_precise
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even
  linarith only [he, hp, hg]

/-- Input: RH and any even character. Claim: principal Euler mass plus its signed
Gamma cost is less than 541/50. Keep the two signed contributions together.
Role: replace fixed cost eleven by 10.82 in quadratic and MR comparisons. -/
theorem gamma_even_common_cost_lt_precise {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hRH : RiemannHypothesis) (heven : χ.Even) :
    (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) +
        PaperStatements.gammaSignedGammaCost χ.gammaFactor <
      (541 / 50 : ℝ) := by
  have he := gamma_principal_euler_lt_precise hRH
  have hg := gamma_even_signed_cost_le_precise heven
  dsimp only [PaperStatements.gammaSignedGammaCost]
  linarith only [he, hg]

/-- Input: GRH, nonprincipal character, admissible scale and prefix, prime
triviality and any upper cap C on Euler mass plus the primitive Gamma cost.
Claim: the actual primitive sum plus local correction is below the joint budget
with fixed cost C. Role: preserve a shared cap before separate numerical rounding. -/
theorem gamma_primitive_sum_add_local_lt_common_cost {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q)
    (hqQ : q ≤ Q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p q → χ p = 1) {C : ℝ}
    (hCost :
      (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) +
          PaperStatements.gammaSignedGammaCost χ.primitiveCharacter.gammaFactor <
        C) :
    (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x k).re +
        gammaQuadraticLocalCorrection χ x <
      gammaJointPrefixLocalBudget χ b x + C + ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hz :=
    AnalyticNumberTheory.DirichletLFunction.gammaResolvent_zeroMass_le_signed_prefix
      (le_trans (by norm_num only : (2 : ℕ) ≤ 3) hm) (hGRH _ χ.primitiveCharacter hp) hp hnp
      (inv_ne_one.mpr hnp) (Finset.Ioc 0 ⌊b⌋₊)
  have hu :=
    PaperStatements.gamma_primitive_sum_re_le_resolvent_conductor_free hQ hm (hmq.trans hqQ) hGRH hp
      hnp (inv_ne_one.mpr hnp) hx
  have he :=
    AnalyticNumberTheory.DirichletLFunction.gamma_character_prefix_add_ambient_ramp_eq_local_cost
      χ.primitiveCharacter (Nat.pos_of_ne_zero (NeZero.ne q)) hb
      (fun p hp hpb hcop ↦
        PaperStatements.primitiveCharacter_apply_one_of_apply_one χ (hone p hp hpb hcop))
      x
  have hl :
    gammaQuadraticLocalCorrection χ x =
      ∑ p ∈ q.primeFactors,
        Real.log p *
          ((∑' k : ℕ,
              Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter p)
                ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
            Real.sqrt x) := by
    simp only [gammaQuadraticLocalCorrection, Finset.sum_div, mul_div_assoc]
  dsimp only [PaperStatements.gammaSignedGammaCost] at hCost
  dsimp only [gammaJointPrefixLocalBudget]
  linarith only [hz, hu, he, hl, hCost]

/-- Input: ambient level, character, prefix, scale, common cost C and principal
cap P. Definition: twice the paired ramp lower bound minus P and the character
budget with cost C. Role: use stronger common bounds in witness separation. -/
noncomputable def gammaJointPrefixSeparationWithCommonCap {q : ℕ} (Q : ℕ)
    (χ : DirichletCharacter ℂ q) (b x C P : ℝ) : ℝ :=
  2 *
      ((∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x -
        gammaRampPairedErrorNumerator x / Real.sqrt x) -
    P -
    (gammaJointPrefixLocalBudget χ b x + C + ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
      43 * x ^ (-9 / 16 : ℝ))

/-- Under GRH and quadratic nonprincipal data, a principal cap, common cost cap
and nonnegative displayed margin contradict prime triviality through the cutoff.
Combine exact common-cost and ramp inequalities. Role: extract witnesses without
assuming an artificially small bound on the Gamma term alone. -/
theorem gamma_ramp_prime_trivial_false_of_common_cap {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q)
    (hqQ : q ≤ Q) (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b C P : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hCost :
      (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) +
          PaperStatements.gammaSignedGammaCost χ.primitiveCharacter.gammaFactor <
        C)
    (hP :
      (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤ P)
    (hgap : 0 ≤ gammaJointPrefixSeparationWithCommonCap Q χ b x C P) :
    ¬(∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  intro hsmall
  have hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p q → χ p = 1 := fun p hp hpb hcop ↦
    hsmall p hp (hp.coprime_iff_not_dvd.mp hcop) (hpb.trans hbx)
  have hC := gamma_primitive_sum_add_local_lt_common_cost hQ hqQ χ hne hGRH hx hb hone hCost
  have hx1 : 1 ≤ x := le_trans (by norm_num only) hx
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann hx1
  have hN := gamma_ramp_no_witness_comparison χ hquad (zero_lt_one.trans_le hx1) hsmall
  dsimp only [gammaJointPrefixSeparationWithCommonCap] at hgap
  linarith only [hC, hT, hP, hN, hgap]

/-- Under odd-nonsquare input data and the displayed scale and pole bounds,
the factor-free signed-principal margin gains 9/50 when the common cost falls
from eleven to 541/50. Compare local and pole budgets. Role: transfer the
retained common cost to the factor-independent witness criterion. -/
theorem gamma_retained_common_factor_free_le_joint {n Q : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    {L b x : ℝ} (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hlogQ : Real.log Q ≤ L + 7 / 5) :
    gammaSignedPrincipalFactorFreeSeparation L b x + 9 / 50 ≤
      gammaJointPrefixSeparationWithCommonCap Q (NumberTheory.complexQuadraticCharacter n hn) b x
          (541 / 50) (gammaSignedVariationPrincipalCap x) +
        7 / 60 := by
  have hJ := gamma_joint_prefix_le_factor_free_budget_small_scale (b := b) hn hns hlog hx
  have hN :
    ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x ≤ ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x :=
    div_le_div_of_nonneg_right (by linarith only [hlogQ]) (Real.sqrt_nonneg x)
  dsimp only [gammaSignedPrincipalFactorFreeSeparation, gammaJointPrefixSeparationWithCommonCap]
  linarith only [hJ, hN]

end PseudoPrime.LLS
