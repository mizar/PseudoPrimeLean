/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaVariableScaleLocalBridge
public import PseudoPrime.PseudoSquare.Bounds.GammaSignedVariationBounds
public import PseudoPrime.LLS.GammaEulerGrowthChebyshev
public import PseudoPrime.LLS.GammaEulerLeadingGrowth

/-! # Quadratic witnesses and full maxima from variable-scale local costs -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, odd nonsquare n, an ambient modulus bounding 4n,
x>=2 and an admissible prefix. Claim: the strict variable-budget gap yields
a negative odd-prime Jacobi witness through 99x/40.
Proof: supply the arithmetic bridge and bound its conductor by 4n.
Role: export the local comparison without a scale-4096 gate. -/
theorem exists_prime_neg_one_witness_of_variable_scale_gap {n Q : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hQ : 20000 ≤ Q) (hnQ : 4 * n ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      LLS.gammaVariableScaleArithmeticBudget n Q x b <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData hn.pos hn hns
  have hm : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ 4 * n :=
    Nat.le_of_dvd (Nat.mul_pos (by norm_num only) hn.pos)
      (NumberTheory.complexQuadraticCharacter n hn).conductor_dvd_level
  exact
    LLS.exists_odd_prime_negative_of_variable_scale_gap bridge hGRH hQ (hm.trans hnQ) hx hb hbx hgap

/-- Under the displayed variable-budget gap, a non-one odd-prime witness
also lies through 99x/40. Proof: use the negative witness.
Role: expose the second quadratic witness predicate at the same scale. -/
theorem exists_prime_ne_one_witness_of_variable_scale_gap {n Q : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hQ : 20000 ≤ Q) (hnQ : 4 * n ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      LLS.gammaVariableScaleArithmeticBudget n Q x b <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hbound, hv⟩ :=
    exists_prime_neg_one_witness_of_variable_scale_gap hn hns hQ hnQ hGRH hx hb hbx hgap
  exact
    ⟨p, hp, ho, hbound, by
      rw [hv]; norm_num only⟩

/-- Under the displayed variable-budget gap and nonempty witness set,
the least odd-prime witness is at most 99x/40. Proof: compare with the
constructed witness. Role: preserve minimality over the whole witness set. -/
theorem primeNegOneWitness_cast_le_of_variable_scale_gap {n Q : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hQ : 20000 ≤ Q) (hnQ : 4 * n ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      LLS.gammaVariableScaleArithmeticBudget n Q x b <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hbound, hv⟩ :=
    exists_prime_neg_one_witness_of_variable_scale_gap hn hns hQ hnQ hGRH hx hb hbx hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hbound

/-- Under the displayed variable-budget gap and nonempty witness set,
the least odd-prime witness is at most 99x/40. Proof: compare with the
constructed witness. Role: preserve minimality over the whole witness set. -/
theorem primeNeOneWitness_cast_le_of_variable_scale_gap {n Q : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hQ : 20000 ≤ Q) (hnQ : 4 * n ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      LLS.gammaVariableScaleArithmeticBudget n Q x b <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hbound, hv⟩ :=
    exists_prime_ne_one_witness_of_variable_scale_gap hn hns hQ hnQ hGRH hx hb hbx hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hbound

/-- Input: GRH, an ambient modulus bounding 4B, x>=2, admissible prefix
and one gap at B. Claim: the full negative witness maximum through B is
at most 99x/40. Proof: use monotonicity of the budget and minimize each witness.
Role: cover every admissible input, including those below the analytic scale. -/
theorem QNegOne_le_of_variable_scale_gap {B Q : ℕ} (hQ : 20000 ≤ Q) (hBQ : 4 * B ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      LLS.gammaVariableScaleArithmeticBudget B Q x b <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  apply
    QNegOne_cast_le_of_forall
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (by linarith only [hx]))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hg := (LLS.gamma_variable_scale_budget_mono ha.odd.pos ha.le).trans_lt hgap
  exact
    primeNegOneWitness_cast_le_of_variable_scale_gap ha.odd ha.not_isSquare hQ
      ((Nat.mul_le_mul_left 4 ha.le).trans hBQ) hGRH hx hb hbx hg
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- Under the same uniform variable-budget gap, the full non-one witness
maximum through B is at most 99x/40. Proof: it is bounded by the negative
maximum. Role: expose both full maxima without new finite certificates. -/
theorem QNeOne_le_of_variable_scale_gap {B Q : ℕ} (hQ : 20000 ≤ Q) (hBQ : 4 * B ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      LLS.gammaVariableScaleArithmeticBudget B Q x b <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  exact
    (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans
      (QNegOne_le_of_variable_scale_gap hQ hBQ hGRH hx hb hbx hgap)

/-- Input: GRH, odd nonsquare n, L>=10, log n<=L, x>=2, an admissible
prefix, variable effective credit, a signed dual cap and the shared polynomial.
Claim: a negative odd-prime witness lies through 99x/40.
Proof: compare the variable budget with the common-cost polynomial margin.
Role: expose the lower-scale analytic criterion without local-cost hypotheses. -/
theorem exists_prime_neg_one_witness_of_variable_scale_polynomial {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {L b x C D : ℝ} (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 2 ≤ x) (hb : 1 ≤ b)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcredit :
      C +
          ((Analysis.gammaVariableSquareMass x - 11783423 / 25000000) * (L + 7 / 5) +
              Analysis.gammaVariableDyadicAllowance x +
              D) /
            2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : LLS.gammaScaleSignedDualBudget L x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (L + 7 / 5) x C) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  have hg :=
    LLS.gamma_common_margin_pos_of_variable_scale_polynomial hn hns hlog (by linarith only [hx])
      (LLS.gamma_log_pole_level_le_of_common_endpoint hn hL hlog) hcredit hdual hpoly
  exact
    exists_prime_neg_one_witness_of_retained_common_separation hn hns (le_max_left _ _)
      (le_max_right _ _) hGRH hx hb hbx hg.le

/-- Under the displayed variable-cost polynomial criterion, a non-one
odd-prime witness lies through 99x/40. Proof: use the negative witness.
Role: connect the lower-scale criterion to the second quadratic predicate. -/
theorem exists_prime_ne_one_witness_of_variable_scale_polynomial {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {L b x C D : ℝ} (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 2 ≤ x) (hb : 1 ≤ b)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcredit :
      C +
          ((Analysis.gammaVariableSquareMass x - 11783423 / 25000000) * (L + 7 / 5) +
              Analysis.gammaVariableDyadicAllowance x +
              D) /
            2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : LLS.gammaScaleSignedDualBudget L x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (L + 7 / 5) x C) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hbound, hv⟩ :=
    exists_prime_neg_one_witness_of_variable_scale_polynomial hn hns hGRH hL hlog hx hb hbx hcredit
      hdual hpoly
  exact
    ⟨p, hp, ho, hbound, by
      rw [hv]; norm_num only⟩

/-- Under the displayed variable-cost polynomial criterion and nonempty
witness set, the least witness is at most 99x/40. Proof: compare it with the
constructed witness. Role: retain minimality over the complete witness set. -/
theorem primeNegOneWitness_cast_le_of_variable_scale_polynomial {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {L b x C D : ℝ} (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 2 ≤ x) (hb : 1 ≤ b)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcredit :
      C +
          ((Analysis.gammaVariableSquareMass x - 11783423 / 25000000) * (L + 7 / 5) +
              Analysis.gammaVariableDyadicAllowance x +
              D) /
            2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : LLS.gammaScaleSignedDualBudget L x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (L + 7 / 5) x C)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hbound, hv⟩ :=
    exists_prime_neg_one_witness_of_variable_scale_polynomial hn hns hGRH hL hlog hx hb hbx hcredit
      hdual hpoly
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hbound

/-- Under the displayed variable-cost polynomial criterion and nonempty
witness set, the least witness is at most 99x/40. Proof: compare it with the
constructed witness. Role: retain minimality over the complete witness set. -/
theorem primeNeOneWitness_cast_le_of_variable_scale_polynomial {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {L b x C D : ℝ} (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 2 ≤ x) (hb : 1 ≤ b)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcredit :
      C +
          ((Analysis.gammaVariableSquareMass x - 11783423 / 25000000) * (L + 7 / 5) +
              Analysis.gammaVariableDyadicAllowance x +
              D) /
            2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : LLS.gammaScaleSignedDualBudget L x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (L + 7 / 5) x C)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hbound, hv⟩ :=
    exists_prime_ne_one_witness_of_variable_scale_polynomial hn hns hGRH hL hlog hx hb hbx hcredit
      hdual hpoly
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hbound

/-- Input: GRH, log B>=10, x>=2 and the displayed uniform variable-cost
polynomial criterion. Claim: the full negative witness maximum is at most
99x/40. Proof: apply the pointwise theorem to every admissible n<=B.
Role: avoid finite verification of the individual inputs. -/
theorem QNegOne_le_of_variable_scale_polynomial {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x C D : ℝ}
    (hB : 10 ≤ Real.log B) (hx : 2 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcredit :
      C +
          ((Analysis.gammaVariableSquareMass x - 11783423 / 25000000) * (Real.log B + 7 / 5) +
              Analysis.gammaVariableDyadicAllowance x +
              D) /
            2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  apply
    QNegOne_cast_le_of_forall
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (by linarith only [hx]))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_of_variable_scale_polynomial ha.odd ha.not_isSquare hGRH hB
      (Real.log_le_log (Nat.cast_pos.mpr ha.odd.pos) (Nat.cast_le.mpr ha.le)) hx hb hbx hcredit
      hdual hpoly
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- Under the same uniform variable-cost polynomial criterion, the full
non-one witness maximum is at most 99x/40. Proof: bound it by the negative
maximum. Role: expose both full maxima from the same analytic data. -/
theorem QNeOne_le_of_variable_scale_polynomial {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x C D : ℝ}
    (hB : 10 ≤ Real.log B) (hx : 2 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcredit :
      C +
          ((Analysis.gammaVariableSquareMass x - 11783423 / 25000000) * (Real.log B + 7 / 5) +
              Analysis.gammaVariableDyadicAllowance x +
              D) /
            2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C) :
    (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  exact
    (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans
      (QNegOne_le_of_variable_scale_polynomial hGRH hB hx hb hbx hcredit hdual hpoly)

/-- Input: GRH, admissible endpoints and scale, an initial Euler credit,
and the displayed analytic-block, dual and polynomial conditions. Claim:
both full quadratic witness maxima are at most (99/40)x. Use asymmetric
Chebyshev differences before polynomial extraction. Role: remove the fixed
large-scale entrance from the short-block witness interface. -/
theorem Q_witness_maxima_le_of_variable_scale_asymmetric_block_polynomial {B a b : ℕ}
    {x C D P s t : ℝ} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hB : 10 ≤ Real.log B) (hx : 2 ≤ x) (hab : a ≤ b) (hs : 1 < s) (hsb : s < b) (ha : (1 : ℝ) < a)
    (hat : (a : ℝ) < t) (hbx : (b : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hP : P ≤ ∑ j ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight j)
    (hcredit :
      C +
          ((Analysis.gammaVariableSquareMass x - 11783423 / 25000000) * (Real.log B + 7 / 5) +
              Analysis.gammaVariableDyadicAllowance x +
              D) /
            2 ≤
        P + (1 / 2 : ℝ) * (b : ℝ) ^ (-21 / 20 : ℝ) * LLS.psiAsymmetricBlockLower a b s t)
    (hdual : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x ∧ (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hg :=
    LLS.gamma_euler_prefix_lower_growth_of_asymmetric_rh_errors hGRH.riemann hab hs hsb ha hat hP
  have hp :
    C +
        ((Analysis.gammaVariableSquareMass x - 11783423 / 25000000) * (Real.log B + 7 / 5) +
            Analysis.gammaVariableDyadicAllowance x +
            D) /
          2 ≤
      ∑ j ∈ Finset.Ioc 0 ⌊(b : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight j := by
    simpa only [Nat.floor_natCast] using hcredit.trans hg
  have habR : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
  have hbR : (1 : ℝ) ≤ b := (ha.trans_le habR).le
  exact
    ⟨QNegOne_le_of_variable_scale_polynomial hGRH hB hx hbR hbx hp hdual hpoly,
      QNeOne_le_of_variable_scale_polynomial hGRH hB hx hbR hbx hp hdual hpoly⟩

/-- Input: GRH, endpoints with 3<=a<=b and scale, an initial Euler credit,
and the displayed analytic-block, dual and polynomial conditions. Claim:
both full quadratic witness maxima are at most (99/40)x. Use asymmetric
Chebyshev differences before polynomial extraction. Role: remove the fixed
large-scale entrance from the short-block witness interface. -/
theorem Q_witness_maxima_le_of_leading_variable_scale_asymmetric_block {B a b : ℕ} {x C D P s t : ℝ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hB : 10 ≤ Real.log B)
    (hx : 2 ≤ x) (hab : a ≤ b) (hs : 1 < s) (hsb : s < b) (ha : 3 ≤ a) (hat : (a : ℝ) < t)
    (hbx : (b : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hP : P ≤ ∑ j ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight j)
    (hcredit :
      C +
          ((Analysis.gammaVariableSquareMass x - 11783423 / 25000000) * (Real.log B + 7 / 5) +
              Analysis.gammaVariableDyadicAllowance x +
              D) /
            2 ≤
        P +
          (56157519 / 100000000 : ℝ) * (b : ℝ) ^ (-21 / 20 : ℝ) *
            LLS.psiAsymmetricBlockLower a b s t)
    (hdual : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x ∧ (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hg :=
    LLS.gamma_euler_prefix_lower_growth_leading_asymmetric hGRH.riemann ha hab hs hsb hat hP
  have hp :
    C +
        ((Analysis.gammaVariableSquareMass x - 11783423 / 25000000) * (Real.log B + 7 / 5) +
            Analysis.gammaVariableDyadicAllowance x +
            D) /
          2 ≤
      ∑ j ∈ Finset.Ioc 0 ⌊(b : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight j := by
    simpa only [Nat.floor_natCast] using hcredit.trans hg
  have habR : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
  have haR : (3 : ℝ) ≤ a := Nat.cast_le.mpr ha
  have hbR : (1 : ℝ) ≤ b := by linarith only [haR, habR]
  exact
    ⟨QNegOne_le_of_variable_scale_polynomial hGRH hB hx hbR hbx hp hdual hpoly,
      QNeOne_le_of_variable_scale_polynomial hGRH hB hx hbR hbx hp hdual hpoly⟩

end PseudoPrime.PseudoSquare
