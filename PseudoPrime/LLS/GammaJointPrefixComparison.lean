/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSignedPrefixCharacterBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaPrimeIndexedPrefix
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaPrincipalEulerBudget
public import PseudoPrime.LLS.GammaQuadraticLocalCorrection
public import PseudoPrime.LLS.GammaSmoothedPrincipalBounds
public import PseudoPrime.LLS.GammaVariablePrincipalBounds
public import PseudoPrime.LLS.GammaQuadraticNoWitness

/-! # Joint integer-prefix and local costs at arbitrary positive scales -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: an original character, prefix endpoint b and real scale x.
Definition: retain the primitive conductor, actual ambient-prime local costs and twice the prefix.
Output: the signed joint arithmetic cost before adding Gamma and contour allowances.
Role: compare finite scales without a prescribed logarithmic profile. -/
noncomputable def gammaJointPrefixLocalBudget {q : ℕ} (χ : DirichletCharacter ℂ q) (b x : ℝ) : ℝ :=
  (11783423 / 25000000 : ℝ) * Real.log χ.conductor +
      (∑ p ∈ q.primeFactors,
        Analysis.gammaActualPrimeLocalCost χ.primitiveCharacter p
          (AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b p) x) -
    2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)

/-- Input: GRH, a nonprincipal character, Q >= max(20000,q), x >= 2 and b >= 1.
Assume unit-prime triviality through b and a signed primitive Gamma cap A.
Claim: the actual primitive sum plus local correction obeys the joint prefix budget.
Proof: regroup the original integer correction and ramp by the same ambient primes.
Role: preserve conductor and ramified losses in one arbitrary-scale analytic comparison. -/
theorem gamma_primitive_sum_add_local_lt_joint_prefix_cap {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q)
    (hqQ : q ≤ Q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p q → χ p = 1) {A : ℝ}
    (hA : PaperStatements.gammaSignedGammaCost χ.primitiveCharacter.gammaFactor ≤ A) :
    (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x k).re +
        gammaQuadraticLocalCorrection χ x <
      gammaJointPrefixLocalBudget χ b x + 25 / 2 + A +
        ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
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
  have hE :=
    AnalyticNumberTheory.DirichletLFunction.gammaResolvent_euler_lt_twelve_half hGRH.riemann
  dsimp only [PaperStatements.gammaSignedGammaCost] at hA
  dsimp only [gammaJointPrefixLocalBudget]
  linarith only [hz, hu, he, hl, hE, hA]

/-- Input: the same arbitrary-scale data and unit-prime triviality through b.
Claim: the primitive sum plus local correction has fixed allowance 117/10.
Proof: insert the parity-uniform signed Gamma cap into the generic joint comparison.
Role: provide a fully certified constant without a large-input hypothesis. -/
theorem gamma_primitive_sum_add_local_lt_joint_prefix {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q)
    (hqQ : q ≤ Q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p q → χ p = 1) :
    (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x k).re +
        gammaQuadraticLocalCorrection χ x <
      gammaJointPrefixLocalBudget χ b x + 117 / 10 + ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hA :=
    AnalyticNumberTheory.DirichletLFunction.gammaResolvent_gammaFactor_le χ.primitiveCharacter
  have h := gamma_primitive_sum_add_local_lt_joint_prefix_cap hQ hqQ χ hne hGRH hx hb hone hA
  linarith only [h]

/-- Input: the arbitrary-scale data, an even character and unit-prime triviality through b.
Claim: the primitive sum plus local correction has fixed allowance 11.
Proof: primitive normalization preserves parity, so the even Gamma cap applies.
Role: retain the sharper constant for even quadratic characters. -/
theorem gamma_primitive_sum_add_local_lt_even_joint_prefix {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q)
    (hqQ : q ≤ Q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p q → χ p = 1) :
    (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x k).re +
        gammaQuadraticLocalCorrection χ x <
      gammaJointPrefixLocalBudget χ b x + 11 + ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hp := (NumberTheory.primitiveCharacter_even_iff χ).mpr heven
  have hA := AnalyticNumberTheory.DirichletLFunction.gammaResolvent_gammaFactor_0_le hp
  have h := gamma_primitive_sum_add_local_lt_joint_prefix_cap hQ hqQ χ hne hGRH hx hb hone hA
  linarith only [h]

/-- Input: ambient Q, a character, prefix b, scale x and signed Gamma cap A.
Definition: twice the paired ramp lower bound minus principal and joint upper bounds.
Output: a sufficient scalar separation margin, with the actual local terms retained.
Role: state the remaining numerical condition independently of witness existence. -/
noncomputable def gammaJointPrefixSeparation {q : ℕ} (Q : ℕ) (χ : DirichletCharacter ℂ q)
    (b x A : ℝ) : ℝ :=
  2 *
      ((∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x -
        gammaRampPairedErrorNumerator x / Real.sqrt x) -
    (Real.sqrt x +
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x) -
    (gammaJointPrefixLocalBudget χ b x + 25 / 2 + A + ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
      43 * x ^ (-9 / 16 : ℝ))

/-- Input: GRH, nonprincipal quadratic data, Q >= max(20000,q), x >= 2 and 1 <= b <= 99x/40.
Assume a valid signed Gamma cap and a nonnegative joint separation margin.
Claim: some eligible prime through 99x/40 has character value different from one.
Proof: prime triviality gives the joint upper bound, contradicting the actual ramp comparison.
Role: connect arbitrary finite-scale budget estimates to quadratic witness extraction. -/
theorem gamma_ramp_prime_trivial_false_joint_prefix {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q)
    (hqQ : q ≤ Q) (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b A : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hA : PaperStatements.gammaSignedGammaCost χ.primitiveCharacter.gammaFactor ≤ A)
    (hgap : 0 ≤ gammaJointPrefixSeparation Q χ b x A) :
    ¬(∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  intro hsmall
  have hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p q → χ p = 1 := fun p hp hpb hcop ↦
    hsmall p hp (hp.coprime_iff_not_dvd.mp hcop) (hpb.trans hbx)
  have hC := gamma_primitive_sum_add_local_lt_joint_prefix_cap hQ hqQ χ hne hGRH hx hb hone hA
  have hx1 : 1 ≤ x := le_trans (by norm_num only) hx
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann hx1
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann hx1
  have hN := gamma_ramp_no_witness_comparison χ hquad (zero_lt_one.trans_le hx1) hsmall
  dsimp only [gammaJointPrefixSeparation] at hgap
  linarith only [hC, hT, hP, hN, hgap]

end PseudoPrime.LLS
