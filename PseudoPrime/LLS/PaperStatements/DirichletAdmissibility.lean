/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.DirichletSpecialization
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.EulerProduct.ExpLog
public import PseudoPrime.AnalyticNumberTheory.General.EntireOrder
public import PseudoPrime.LLS.Extensions.GeneralLFunction.DirichletAdmissibility

/-!
# Analytic admissibility of degree-one Dirichlet L-function data

Character series and Euler products, entire continuation, gamma normalization, logarithmic
growth and the conjugate functional equation verify all fields of general admissibility.
The final conditional theorem specializes the generalized logarithmic formula to Lemma 2.5.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The general logarithmic formula implies the original Lemma 2.5 with individual RH.
Prove admissibility of every primitive degree-one character datum at modulus at least three,
then apply the specialization implication. Only the general formula is an explicit premise;
the public proof of Lemma 2.5 supplies it using `lls_propL1_general_proof`. -/
theorem lls_lemma25_of_general_formula (hformula : Extensions.lls_propL1_general) :
    lls_lemma25 := by
  apply lls_lemma25_of_general hformula
  intro q _ χ hq hp
  exact
    Extensions.GeneralLFunction.ofDirichletCharacter_isAdmissible χ
      (Nat.le_trans (by norm_num only : 2 ≤ 3) hq) hp (primitiveCharacter_ne_one_of_three_le hq hp)

end PseudoPrime.LLS.PaperStatements
