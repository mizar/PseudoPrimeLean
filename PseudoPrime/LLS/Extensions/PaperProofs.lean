/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.PaperStatements
public import PseudoPrime.LLS.Extensions.QNeOneBranchProofs
public import PseudoPrime.LLS.Extensions.ArithmeticCoefficients
public import PseudoPrime.LLS.Extensions.LogValueFormulaDerivation
public import PseudoPrime.LLS.Extensions.ShiftedMellinFormula
public import PseudoPrime.LLS.Extensions.ReciprocalFormulaDerivation
public import PseudoPrime.LLS.Extensions.ZeroMassReciprocalFormula

/-!
# Public proofs of extension statements

Each declaration proves its matching PaperStatements proposition and carries the `_proof` suffix.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- For an admissible general L-function satisfying its Riemann hypothesis, the
logarithmic value has the weighted arithmetic formula with the stated real errors.
Mellin inversion, the Hadamard zero expansion and the gamma resolvent series give
the shifted identity; integration and the zero and gamma bounds give the formula.
This is the public proof of the generalization of Lemma 2.5. -/
theorem lls_propL1_general_proof : lls_propL1_general := by
  apply lls_propL1_general_of_shifted_formula
  intro f hf hRH x hx σ hσ
  exact
    GeneralLFunction.shiftedArithmeticSum_eq_origin_zero_sub_gamma f hf hRH hσ
      (lt_of_lt_of_le (show (1 : ℝ) < 2 by norm_num only) hx)

/-- For each fixed admissible general L-function satisfying its Riemann hypothesis,
the reciprocal formula holds with a real zero coefficient of absolute value at most one
and the stated Big-O remainder. Reciprocal Mellin inversion identifies the arithmetic sum;
the completed zero expansion gives the bounded coefficient, while summable gamma residues
give the remainder estimate. This is the public proof of the general reciprocal formula. -/
theorem lls_propL2_proof : lls_propL2 := by
  apply lls_propL2_of_reciprocalRemainder
  exact GeneralLFunction.isBigO_reciprocalRemainder

/-- For each fixed admissible general L-function satisfying its Riemann hypothesis, the
completed-zero mass equals the logarithmic analytic conductor minus twice the real reciprocal
sum, with the stated Big-O error. The completed reciprocal formula bounds the smoothed sum;
Chebyshev's bound removes smoothing, and positive degree controls the asymptotic scale.
The Big-O constant may depend on the fixed function. This is the public zero-mass formula. -/
theorem lls_sumzeros_proof : lls_sumzeros := by
  intro f hf hRH
  refine
    ⟨GeneralLFunction.summable_zeroMassTerm_of_admissible f hf hRH, f.zeroMassReciprocalRemainder,
      ?_, GeneralLFunction.isBigO_zeroMassReciprocalRemainder f hf hRH⟩
  intro x _
  unfold GeneralLFunction.zeroMassReciprocalRemainder
  ring

/-- GRH, the two Riemann lower bounds, y ≥ 12 and the zero-branch character assumptions
imply a contradiction. Apply the common weighted-sum sandwich and numerical separation.
This proves the external zero-branch proposition. -/
theorem lls_qNeOne_zero_branch_proof : lls_qNeOne_zero_branch := by
  exact primitiveLogWeightedBounds_of_qneOne_zero_branch_even_false_common

/-- Under the stated GRH, Riemann bounds, cutoff and negative-one branch assumptions,
the corrected weighted sum contradicts numerical separation.
Apply the negative-one branch derivation to prove its external proposition. -/
theorem lls_qNeOne_neg_one_branch_proof : lls_qNeOne_neg_one_branch := by
  exact primitiveLogWeightedBounds_of_qneOne_neg_one_branch_false_common

/-- Under the stated GRH, Riemann bounds, cutoff and one-branch assumptions,
the weighted sum contradicts numerical separation.
Apply the one-branch derivation to prove its external proposition. -/
theorem lls_qNeOne_one_branch_proof : lls_qNeOne_one_branch := by
  exact primitiveLogWeightedBounds_of_qneOne_one_branch_false_common

end PseudoPrime.LLS.Extensions
