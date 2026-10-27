/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroCounting
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.OccurrenceCounting

/-! # Finite sums of primitive Dirichlet zero counts -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Purpose: express the primitive-character family zero count through a finite dependent sum.

Definition: for each modulus `q` from `1` through `T`, sum the completed zero count over
nonprincipal primitive characters modulo `q`, using analytic multiplicity.

Inputs: a natural cutoff `T` for the moduli and zero heights, and a real threshold `σ`.

Output: the finite sum corresponding to the left side of the log-free family density estimate.
The range `Fin T` with modulus `q.val + 1` includes each positive modulus at most `T` once.

Role: fixes the family and multiplicity conventions before proving a uniform density bound.
-/
noncomputable def primitiveCharacterFamilyZeroCount (T : ℕ) (σ : ℝ) : ℝ := by
  classical
    exact
    ∑ q : Fin T,
      ∑ χ : DirichletCharacter ℂ (q.val + 1),
        if hχ : χ ≠ 1 then
          if hprim : χ.IsPrimitive then
            PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ (T : ℝ)
          else 0
        else 0

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Purpose: count the zeros in the primitive family after removing a selected point per character.

Definition: sum analytic multiplicities over each eligible character's zero rectangle with its
selected complex point erased.

Inputs: a height and modulus cutoff, a real-part threshold, and a point selector indexed by
modulus and character.

Output: the family zero count with at most one selected point removed from each eligible
character's zero set.

Role: separates selected near-one zeros from the ordinary zeros in a finite density estimate.
-/
noncomputable def primitiveCharacterFamilyZeroCountExcept (T : ℕ) (σ : ℝ)
    (ρ : ∀ q : Fin T, DirichletCharacter ℂ (q.val + 1) → ℂ) : ℝ := by
  classical
    exact
    ∑ q : Fin T,
      ∑ χ : DirichletCharacter ℂ (q.val + 1),
        if hχ : χ ≠ 1 then
          if hprim : χ.IsPrimitive then
            completedZeroMultiplicityCountInRectangleExcept χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
              ((1 : ℂ) + (T : ℝ) * Complex.I) (ρ q χ)
          else 0
        else 0

/--
Purpose: count the multiplicity of each selected zero in the primitive family.

Definition: for each nonprincipal primitive character, add the analytic multiplicity of its
selected point when that point lies in the zero rectangle; otherwise add zero.

Inputs: a height and modulus cutoff, a real-part threshold, and a point selector indexed by
modulus and character.

Output: the total analytic multiplicity contributed by selected points that are actually zeros
in their corresponding rectangles.

Role: records the exact exceptional-zero contribution separated by
primitiveCharacterFamilyZeroCountExcept.
-/
noncomputable def primitiveCharacterFamilySelectedZeroCount (T : ℕ) (σ : ℝ)
    (ρ : ∀ q : Fin T, DirichletCharacter ℂ (q.val + 1) → ℂ) : ℝ := by
  classical
    exact
    ∑ q : Fin T,
      ∑ χ : DirichletCharacter ℂ (q.val + 1),
        if hχ : χ ≠ 1 then
          if hprim : χ.IsPrimitive then
            if
                ρ q χ ∈
                  PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZerosInRectangle χ hχ
                    ((σ : ℂ) - (T : ℝ) * Complex.I) ((1 : ℂ) + (T : ℝ) * Complex.I) then
              (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (ρ q χ) : ℝ)
            else 0
          else 0
        else 0

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Inputs: a family cutoff, a real-part threshold, and a selected point for each character.

Claim: the family zero count equals the family with those points erased plus their zero
multiplicities.

Proof: apply the per-character finite-sum decomposition at every modulus and character, then
distribute the nested finite sums.

Role: makes the exceptional-zero correction explicit in the family count, preserving analytic
multiplicity and the primitive-character filtering.
-/
theorem primitiveCharacterFamilyZeroCount_eq_except_add_selected (T : ℕ) (σ : ℝ)
    (ρ : ∀ q : Fin T, DirichletCharacter ℂ (q.val + 1) → ℂ) :
    primitiveCharacterFamilyZeroCount T σ =
      primitiveCharacterFamilyZeroCountExcept T σ ρ +
        primitiveCharacterFamilySelectedZeroCount T σ ρ := by
  classical
  let f : ∀ q : Fin T, DirichletCharacter ℂ (q.val + 1) → ℝ := fun q χ =>
    if hχ : χ ≠ 1 then if hprim : χ.IsPrimitive then completedZeroCount χ hχ σ (T : ℝ) else 0 else 0
  let g : ∀ q : Fin T, DirichletCharacter ℂ (q.val + 1) → ℝ := fun q χ =>
    if hχ : χ ≠ 1 then
      if hprim : χ.IsPrimitive then
        completedZeroMultiplicityCountInRectangleExcept χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
          ((1 : ℂ) + (T : ℝ) * Complex.I) (ρ q χ)
      else 0
    else 0
  let h : ∀ q : Fin T, DirichletCharacter ℂ (q.val + 1) → ℝ := fun q χ =>
    if hχ : χ ≠ 1 then
      if hprim : χ.IsPrimitive then
        if
            ρ q χ ∈
              completedZerosInRectangle χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
                ((1 : ℂ) + (T : ℝ) * Complex.I) then
          (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (ρ q χ) : ℝ)
        else 0
      else 0
    else 0
  change
    (∑ q : Fin T, ∑ χ : DirichletCharacter ℂ (q.val + 1), f q χ) =
      (∑ q : Fin T, ∑ χ : DirichletCharacter ℂ (q.val + 1), g q χ) +
        ∑ q : Fin T, ∑ χ : DirichletCharacter ℂ (q.val + 1), h q χ
  have hpoint : ∀ q χ, f q χ = g q χ + h q χ := by
    intro q χ
    dsimp only [f, g, h]
    by_cases hχ : χ ≠ 1
    · simp only [dite_eq_left hχ]
      by_cases hprim : χ.IsPrimitive
      · simp only [dite_eq_left hprim]
        rw [completedZeroCount]
        exact
          completedZeroMultiplicityCountInRectangle_eq_except_add_if_mem χ hχ
            ((σ : ℂ) - (T : ℝ) * Complex.I) ((1 : ℂ) + (T : ℝ) * Complex.I) (ρ q χ)
      · simp only [dite_eq_right hprim, add_zero]
    · simp only [dite_eq_right hχ, add_zero]
  calc
    _ = ∑ q : Fin T, ∑ χ : DirichletCharacter ℂ (q.val + 1), (g q χ + h q χ) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro χ hχ
      exact hpoint q χ
    _ = _ := by simp only [Finset.sum_add_distrib]

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Inputs: a family cutoff, a real-part threshold, and one selected point per character.

Claim: the zero count with the selected points erased is nonnegative.

Proof: each retained analytic order is a natural number cast to the reals; sum nonnegativity
over zeros, characters, and moduli.

Role: lets upper bounds on the full family count pass to the family with selected zeros removed.
-/
theorem primitiveCharacterFamilyZeroCountExcept_nonneg (T : ℕ) (σ : ℝ)
    (ρ : ∀ q : Fin T, DirichletCharacter ℂ (q.val + 1) → ℂ) :
    0 ≤ primitiveCharacterFamilyZeroCountExcept T σ ρ := by
  classical
  unfold primitiveCharacterFamilyZeroCountExcept
  apply Finset.sum_nonneg
  intro q hq
  apply Finset.sum_nonneg
  intro χ hχmem
  split_ifs with hχ hprim
  · unfold completedZeroMultiplicityCountInRectangleExcept
    apply Finset.sum_nonneg
    intro ξ hξ
    exact Nat.cast_nonneg _
  · exact le_of_eq rfl
  · exact le_of_eq rfl

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Inputs: a family cutoff, a real-part threshold, and one selected point per character.

Claim: the total selected zero multiplicity is nonnegative.

Proof: every selected contribution is either zero or the cast of a natural analytic order.

Role: treats the exceptional contribution as a nonnegative correction in the family identity.
-/
theorem primitiveCharacterFamilySelectedZeroCount_nonneg (T : ℕ) (σ : ℝ)
    (ρ : ∀ q : Fin T, DirichletCharacter ℂ (q.val + 1) → ℂ) :
    0 ≤ primitiveCharacterFamilySelectedZeroCount T σ ρ := by
  classical
  unfold primitiveCharacterFamilySelectedZeroCount
  apply Finset.sum_nonneg
  intro q hq
  apply Finset.sum_nonneg
  intro χ hχmem
  split_ifs with hχ hprim hzero
  · exact Nat.cast_nonneg _
  · exact le_of_eq rfl
  · exact le_of_eq rfl
  · exact le_of_eq rfl

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Inputs: a finite set of moduli below `T`, a real-part threshold, and a selected point for each
character.

Claim: if every modulus in the set has a selected nonprincipal primitive zero in its rectangle,
then the number of such moduli is bounded by the total selected zero multiplicity.

Proof: each selected zero has positive analytic multiplicity; retain one such term in each
modulus sum and then include the finite set into the full family.

Role: converts exceptional-modulus counts into a lower bound for the selected-zero correction.
-/
theorem finiteSet_card_le_selectedZeroCount_of_witness (T : ℕ) (σ : ℝ)
    (ρ : ∀ q : Fin T, DirichletCharacter ℂ (q.val + 1) → ℂ) (E : Finset (Fin T))
    (hzero :
      ∀ q ∈ E,
        ∃ (χ : DirichletCharacter ℂ (q.val + 1)) (hχ : χ ≠ 1) (_hprim : χ.IsPrimitive),
          ρ q χ ∈
            completedZerosInRectangle χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
              ((1 : ℂ) + (T : ℝ) * Complex.I)) :
    (E.card : ℝ) ≤ primitiveCharacterFamilySelectedZeroCount T σ ρ := by
  classical
  let f : ∀ q : Fin T, DirichletCharacter ℂ (q.val + 1) → ℝ := fun q χ =>
    if hχ : χ ≠ 1 then
      if hprim : χ.IsPrimitive then
        if hmem :
            ρ q χ ∈
              completedZerosInRectangle χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
                ((1 : ℂ) + (T : ℝ) * Complex.I) then
          (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (ρ q χ) : ℝ)
        else 0
      else 0
    else 0
  have hinner : ∀ q ∈ E, 1 ≤ ∑ χ : DirichletCharacter ℂ (q.val + 1), f q χ := by
    intro q hq
    obtain ⟨χ, hχ, hprim, hmem⟩ := hzero q hq
    have hzero' := (mem_completedZerosInRectangle_iff.mp hmem).2
    have hmult := analyticOrderNatAt_pos_of_completedLFunction_zero χ hχ hzero'
    have hsingle :=
      Finset.single_le_sum (s := Finset.univ) (f := f q)
        (fun ψ hψ => by
          dsimp only [f]
          split_ifs with hψ' hprim' hmem'
          · exact Nat.cast_nonneg _
          · exact le_of_eq rfl
          · exact le_of_eq rfl
          · exact le_of_eq rfl)
        (Finset.mem_univ χ)
    have htermEq :
      f q χ = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (ρ q χ) : ℝ) := by
      dsimp only [f]
      simp only [dite_eq_left hχ, dite_eq_left hprim]
      split
      · rfl
      · contradiction
    have hterm : 1 ≤ f q χ := by
      rw [htermEq]
      exact_mod_cast (Nat.succ_le_iff.mpr hmult)
    calc
      1 ≤ f q χ := hterm
      _ ≤ ∑ ψ : DirichletCharacter ℂ (q.val + 1), f q ψ := hsingle
  have hrestricted : (E.card : ℝ) ≤ ∑ q ∈ E, ∑ χ : DirichletCharacter ℂ (q.val + 1), f q χ := by
    calc
      (E.card : ℝ) = ∑ q ∈ E, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ q ∈ E, ∑ χ : DirichletCharacter ℂ (q.val + 1), f q χ := by
        apply Finset.sum_le_sum
        intro q hq
        exact hinner q hq
  have hall :
    (∑ q ∈ E, ∑ χ : DirichletCharacter ℂ (q.val + 1), f q χ) ≤
      ∑ q : Fin T, ∑ χ : DirichletCharacter ℂ (q.val + 1), f q χ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      exact Finset.mem_univ q
    · intro q hq hnot
      apply Finset.sum_nonneg
      intro χ hχ
      dsimp only [f]
      split_ifs with hχ' hprim' hmem'
      · exact Nat.cast_nonneg _
      · exact le_of_eq rfl
      · exact le_of_eq rfl
      · exact le_of_eq rfl
  have hfamily :
    primitiveCharacterFamilySelectedZeroCount T σ ρ =
      ∑ q : Fin T, ∑ χ : DirichletCharacter ℂ (q.val + 1), f q χ := by
    unfold primitiveCharacterFamilySelectedZeroCount
    rfl
  calc
    (E.card : ℝ) ≤ ∑ q ∈ E, ∑ χ : DirichletCharacter ℂ (q.val + 1), f q χ := hrestricted
    _ ≤ primitiveCharacterFamilySelectedZeroCount T σ ρ := by
      rw [hfamily]
      exact hall

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Inputs: a finite set of moduli below `T`, a real-part threshold, and selected points for the
characters.

Claim: if each modulus in the set has a selected nonprincipal primitive zero in its rectangle,
then the set's cardinality is at most the full family zero count.

Proof: bound the cardinality by selected multiplicity, then use the exact decomposition of the
full count and nonnegativity of the count with selected points erased.

Role: connects an exceptional-modulus count directly to any later upper bound for the family zero
count.
-/
theorem finiteSet_card_le_primitiveCharacterFamilyZeroCount_of_witness (T : ℕ) (σ : ℝ)
    (ρ : ∀ q : Fin T, DirichletCharacter ℂ (q.val + 1) → ℂ) (E : Finset (Fin T))
    (hzero :
      ∀ q ∈ E,
        ∃ (χ : DirichletCharacter ℂ (q.val + 1)) (hχ : χ ≠ 1) (_hprim : χ.IsPrimitive),
          ρ q χ ∈
            completedZerosInRectangle χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
              ((1 : ℂ) + (T : ℝ) * Complex.I)) :
    (E.card : ℝ) ≤ primitiveCharacterFamilyZeroCount T σ := by
  classical
  have hcard := finiteSet_card_le_selectedZeroCount_of_witness T σ ρ E hzero
  have hdecomp := primitiveCharacterFamilyZeroCount_eq_except_add_selected T σ ρ
  have hexcept := primitiveCharacterFamilyZeroCountExcept_nonneg T σ ρ
  have hselected :
    primitiveCharacterFamilySelectedZeroCount T σ ρ ≤ primitiveCharacterFamilyZeroCount T σ := by
    rw [hdecomp]
    calc
      primitiveCharacterFamilySelectedZeroCount T σ ρ =
          0 + primitiveCharacterFamilySelectedZeroCount T σ ρ :=
        by rw [zero_add]
      _ ≤
          primitiveCharacterFamilyZeroCountExcept T σ ρ +
            primitiveCharacterFamilySelectedZeroCount T σ ρ :=
        add_le_add_left hexcept _
  exact hcard.trans hselected

/--
Inputs: a natural cutoff `T` and a real-part threshold `σ`.

Claim: the finite primitive-character family zero count is nonnegative.

Proof: each inner term is either zero or a nonnegative completed zero count; apply finite-sum
nonnegativity first to characters and then to moduli.

Role: supplies positivity for subsequent upper bounds on the family sum.
-/
theorem primitiveCharacterFamilyZeroCount_nonneg (T : ℕ) (σ : ℝ) :
    0 ≤ primitiveCharacterFamilyZeroCount T σ := by
  classical
  unfold primitiveCharacterFamilyZeroCount
  apply Finset.sum_nonneg
  intro q hq
  apply Finset.sum_nonneg
  intro χ hχmem
  split_ifs with hχ hprim
  · exact
      PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount_nonneg χ hχ σ (T : ℝ)
  · exact le_of_eq rfl
  · exact le_of_eq rfl

/--
Inputs: a modulus index `j` below the family cutoff, a nonprincipal primitive character at that
modulus, and a real-part threshold.

Claim: the character's multiplicity-weighted completed zero count up to the common height cutoff
is bounded by the total primitive family count.

Proof: first select the character from the finite sum over its modulus, then select that modulus
from the outer finite sum; all other summands are nonnegative.

Role: converts a family density bound into the corresponding fixed-modulus bound without changing
the analytic multiplicity convention.
-/
theorem completedZeroCount_le_primitiveCharacterFamilyZeroCount {T : ℕ} (j : Fin T)
    {χ : DirichletCharacter ℂ (j.val + 1)} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (σ : ℝ) :
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ (T : ℝ) ≤
      primitiveCharacterFamilyZeroCount T σ := by
  classical
  let term := fun (ψ : DirichletCharacter ℂ (j.val + 1)) =>
    if hψ : ψ ≠ 1 then
      if hp : ψ.IsPrimitive then
        PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount ψ hψ σ (T : ℝ)
      else 0
    else 0
  have hsingle :=
    Finset.single_le_sum (s := Finset.univ) (f := term)
      (fun ψ hψmem => by
        dsimp only [term]
        split_ifs
        · exact
            PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount_nonneg ψ ‹ψ ≠ 1›
              σ (T : ℝ)
        · exact le_of_eq rfl
        · exact le_of_eq rfl)
      (Finset.mem_univ χ)
  have hselected :
    (if hψ : χ ≠ 1 then
        if hp : χ.IsPrimitive then
          PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hψ σ (T : ℝ)
        else 0
      else 0) =
      PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ (T : ℝ) := by
    split_ifs
    rfl
  have hinner :
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ (T : ℝ) ≤
      ∑ ψ : DirichletCharacter ℂ (j.val + 1), term ψ := by
    rw [← hselected]
    exact hsingle
  let inner : Fin T → ℝ := fun k =>
    ∑ ψ : DirichletCharacter ℂ (k.val + 1),
      if hψ : ψ ≠ 1 then
        if hp : ψ.IsPrimitive then
          PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount ψ hψ σ (T : ℝ)
        else 0
      else 0
  have houter : inner j ≤ ∑ k : Fin T, inner k := by
    apply Finset.single_le_sum
    · intro k hk
      dsimp only [inner]
      apply Finset.sum_nonneg
      intro ψ hψmem
      split_ifs
      · exact
          PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount_nonneg ψ ‹ψ ≠ 1› σ
            (T : ℝ)
      · exact le_of_eq rfl
      · exact le_of_eq rfl
    · exact Finset.mem_univ j
  have hFamily : primitiveCharacterFamilyZeroCount T σ = ∑ k : Fin T, inner k := by
    unfold primitiveCharacterFamilyZeroCount
    dsimp only [inner]
  rw [hFamily]
  have hterm : inner j = ∑ ψ : DirichletCharacter ℂ (j.val + 1), term ψ := by
    dsimp only [inner, term]
  calc
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ (T : ℝ) ≤
        ∑ ψ : DirichletCharacter ℂ (j.val + 1), term ψ :=
      hinner
    _ = inner j := hterm.symm
    _ ≤ ∑ k : Fin T, inner k := houter

/--
Inputs: a primitive nonprincipal character whose modulus is at most the family cutoff, and a
zero-count height bounded by that cutoff.

Claim: the character's multiplicity-weighted zero count at the requested height is bounded by
the primitive family count at the common cutoff.

Proof: enlarge the zero-count height to the family cutoff, then apply
`completedZeroCount_le_primitiveCharacterFamilyZeroCount`.

Role: provides the fixed-modulus consequence needed when a family estimate is used at a common
modulus and height scale.
-/
theorem completedZeroCount_le_primitiveCharacterFamilyZeroCount_of_height_le {T : ℕ} (j : Fin T)
    {χ : DirichletCharacter ℂ (j.val + 1)} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {σ t : ℝ}
    (hσ : σ ≤ 1) (ht : 0 ≤ t) (htT : t ≤ (T : ℝ)) :
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ t ≤
      primitiveCharacterFamilyZeroCount T σ := by
  have hmono :=
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount_mono_height χ hχ hσ ht
      htT
  exact hmono.trans (completedZeroCount_le_primitiveCharacterFamilyZeroCount j hχ hprim σ)

/--
Purpose: count zeros of all nonprincipal primitive characters at one modulus.

Definition: sum the completed zero counts up to the common height `T` over primitive characters
modulo `j.val + 1`, assigning zero to principal or imprimitive characters.

Inputs: a family cutoff `T`, a modulus index `j : Fin T`, and a real-part threshold `σ`.

Output: the multiplicity-weighted zero count at the selected modulus.

Role: isolates the fixed-modulus contribution that appears inside a family density sum.
-/
noncomputable def primitiveCharacterModulusZeroCount (T : ℕ) (j : Fin T) (σ : ℝ) : ℝ := by
  classical
    exact
    ∑ χ : DirichletCharacter ℂ (j.val + 1),
      if hχ : χ ≠ 1 then
        if hprim : χ.IsPrimitive then
          PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ (T : ℝ)
        else 0
      else 0

/--
Inputs: a modulus index below the family cutoff and a real-part threshold.

Claim: the total multiplicity-weighted zero count of primitive nonprincipal characters at that
modulus is at most the corresponding count over all moduli up to the cutoff.

Proof: select the modulus from the outer finite sum; every other modulus contribution is
nonnegative.

Role: gives the fixed-modulus form of a family log-free estimate for use in the explicit formula.
-/
theorem primitiveCharacterModulusZeroCount_le_family (T : ℕ) (j : Fin T) (σ : ℝ) :
    primitiveCharacterModulusZeroCount T j σ ≤ primitiveCharacterFamilyZeroCount T σ := by
  classical
  let inner : Fin T → ℝ := fun k =>
    ∑ χ : DirichletCharacter ℂ (k.val + 1),
      if hχ : χ ≠ 1 then
        if hprim : χ.IsPrimitive then
          PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ (T : ℝ)
        else 0
      else 0
  change inner j ≤ ∑ k : Fin T, inner k
  apply Finset.single_le_sum
  · intro k hk
    dsimp only [inner]
    apply Finset.sum_nonneg
    intro χ hχmem
    split_ifs with hχ hprim
    · exact
        PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount_nonneg χ hχ σ (T : ℝ)
    · exact le_of_eq rfl
    · exact le_of_eq rfl
  · exact Finset.mem_univ j

/--
Inputs: a fixed modulus index, two ordered real-part thresholds, and the common height cutoff.

Claim: increasing the real-part threshold cannot increase the primitive-character zero count at
that modulus.

Proof: apply the per-character antitonicity to each nonprincipal primitive character and sum the
pointwise inequalities.

Role: supports real-part interval decompositions of a fixed-modulus density estimate.
-/
theorem primitiveCharacterModulusZeroCount_antitone_sigma (T : ℕ) (j : Fin T) {σ₁ σ₂ : ℝ}
    (hσ : σ₁ ≤ σ₂) (h₂ : σ₂ ≤ 1) :
    primitiveCharacterModulusZeroCount T j σ₂ ≤ primitiveCharacterModulusZeroCount T j σ₁ := by
  classical
  unfold primitiveCharacterModulusZeroCount
  apply Finset.sum_le_sum
  intro χ hχmem
  split_ifs with hχ hprim
  · exact
      PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount_antitone_sigma χ hχ hσ
        h₂ (Nat.cast_nonneg T)
  · exact le_of_eq rfl
  · exact le_of_eq rfl

/--
Purpose: count zeros of all nonprincipal primitive characters at one modulus and an arbitrary
height cutoff.

Definition: sum the completed zero counts over primitive characters modulo `j.val + 1`, using
analytic multiplicity.

Inputs: a modulus family cutoff `T`, a modulus index `j`, a real-part threshold `σ`, and a height
cutoff `t`.

Output: the multiplicity-weighted fixed-modulus zero count up to height `t`.

Role: separates the modulus and height parameters when applying a common family density bound.
-/
noncomputable def primitiveCharacterModulusZeroCountAtHeight (T : ℕ) (j : Fin T) (σ t : ℝ) : ℝ := by
  classical
    exact
    ∑ χ : DirichletCharacter ℂ (j.val + 1),
      if hχ : χ ≠ 1 then
        if hprim : χ.IsPrimitive then
          PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ t
        else 0
      else 0

/--
Inputs: a fixed modulus index, a real-part threshold at most one, and ordered nonnegative heights.

Claim: enlarging the height cutoff cannot decrease the primitive-character zero count at that
modulus.

Proof: apply height monotonicity to each nonprincipal primitive character and sum the results.

Role: permits a fixed-modulus count to use a common family height cutoff.
-/
theorem primitiveCharacterModulusZeroCount_mono_height (T : ℕ) (j : Fin T) (σ : ℝ) (hσ : σ ≤ 1)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t₂) :
    primitiveCharacterModulusZeroCountAtHeight T j σ t₁ ≤
      primitiveCharacterModulusZeroCountAtHeight T j σ t₂ := by
  classical
  unfold primitiveCharacterModulusZeroCountAtHeight
  apply Finset.sum_le_sum
  intro χ hχmem
  split_ifs with hχ hprim
  · exact
      PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount_mono_height χ hχ hσ ht₁
        ht
  · exact le_of_eq rfl
  · exact le_of_eq rfl

/--
Inputs: a fixed modulus below a common family cutoff, a real-part threshold, and a smaller
nonnegative height cutoff.

Claim: the primitive-character zero count at the fixed modulus and requested height is bounded by
the total family count at the common cutoff.

Proof: enlarge each character's height cutoff to `T`, sum the pointwise bounds, and use the
fixed-modulus family extraction theorem.

Role: provides the primitive fixed-modulus estimate used when the explicit-formula height differs
from the modulus range.
-/
theorem primitiveCharacterModulusZeroCountAtHeight_le_family (T : ℕ) (j : Fin T) (σ t : ℝ)
    (hσ : σ ≤ 1) (ht : 0 ≤ t) (htT : t ≤ (T : ℝ)) :
    primitiveCharacterModulusZeroCountAtHeight T j σ t ≤ primitiveCharacterFamilyZeroCount T σ := by
  classical
  have hmono :
    primitiveCharacterModulusZeroCountAtHeight T j σ t ≤
      primitiveCharacterModulusZeroCount T j σ := by
    unfold primitiveCharacterModulusZeroCountAtHeight primitiveCharacterModulusZeroCount
    apply Finset.sum_le_sum
    intro χ hχmem
    split_ifs with hχ hprim
    · exact
        PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount_mono_height χ hχ hσ
          ht htT
    · exact le_of_eq rfl
    · exact le_of_eq rfl
  exact hmono.trans (primitiveCharacterModulusZeroCount_le_family T j σ)

/--
Inputs: a natural cutoff `T` and real thresholds `σ₁ ≤ σ₂ ≤ 1`.

Claim: raising the real-part threshold cannot increase the primitive-character family count.

Proof: apply the per-character antitonicity to each nonprincipal primitive character, then sum
the pointwise inequalities over characters and moduli.

Role: controls the family count when dividing the zero region into real-part intervals.
-/
theorem primitiveCharacterFamilyZeroCount_antitone_sigma (T : ℕ) {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂)
    (h₂ : σ₂ ≤ 1) :
    primitiveCharacterFamilyZeroCount T σ₂ ≤ primitiveCharacterFamilyZeroCount T σ₁ := by
  classical
  unfold primitiveCharacterFamilyZeroCount
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro χ hχmem
  split_ifs with hχ hprim
  · exact
      PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount_antitone_sigma χ hχ hσ
        h₂ (show 0 ≤ (T : ℝ) from Nat.cast_nonneg T)
  · exact le_of_eq rfl
  · exact le_of_eq rfl

/--
Inputs: a natural cutoff, a real-part threshold at most one, and the family zero counts at that
cutoff and its successor.

Claim: increasing the common modulus and height cutoff by one cannot decrease the primitive
character family count.

Proof: raise the height bound for each existing modulus using zero-count monotonicity, then add
the nonnegative contribution from the new modulus.

Role: supplies the successor step for enlarging both finite ranges in the family density sum.
-/
theorem primitiveCharacterFamilyZeroCount_succ (T : ℕ) (σ : ℝ) (hσ : σ ≤ 1) :
    primitiveCharacterFamilyZeroCount T σ ≤ primitiveCharacterFamilyZeroCount (T + 1) σ := by
  classical
  unfold primitiveCharacterFamilyZeroCount
  rw [Fin.sum_univ_castSucc]
  calc
    (∑ q : Fin T,
          ∑ χ : DirichletCharacter ℂ (q.val + 1),
            if hχ : χ ≠ 1 then
              if hprim : χ.IsPrimitive then
                PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ
                  (T : ℝ)
              else 0
            else 0) ≤
        ∑ q : Fin T,
          ∑ χ : DirichletCharacter ℂ (q.val + 1),
            if hχ : χ ≠ 1 then
              if hprim : χ.IsPrimitive then
                PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ
                  ((T + 1 : ℕ) : ℝ)
              else 0
            else 0 :=
      by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro χ hχmem
      split_ifs with hχ hprim
      · exact
          PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount_mono_height χ hχ hσ
            (Nat.cast_nonneg T) (Nat.cast_le.mpr (Nat.le_succ T))
      · exact le_rfl
      · exact le_rfl
    _ ≤
        (∑ q : Fin T,
            ∑ χ : DirichletCharacter ℂ (q.val + 1),
              if hχ : χ ≠ 1 then
                if hprim : χ.IsPrimitive then
                  PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ
                    ((T + 1 : ℕ) : ℝ)
                else 0
              else 0) +
          (∑ χ : DirichletCharacter ℂ ((Fin.last T).val + 1),
            if hχ : χ ≠ 1 then
              if hprim : χ.IsPrimitive then
                PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ
                  ((T + 1 : ℕ) : ℝ)
              else 0
            else 0) :=
      by
      exact
        le_add_of_nonneg_right
          (Finset.sum_nonneg fun χ hχmem => by
            split_ifs with hχ hprim
            · exact
                PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount_nonneg χ hχ σ
                  ((T + 1 : ℕ) : ℝ)
            · exact le_rfl
            · exact le_rfl)

/--
Inputs: two natural cutoffs in increasing order and a real-part threshold at most one.

Claim: the primitive-character family zero count is monotone in the common modulus and height
cutoff.

Proof: induct over the cutoff interval, applying the successor estimate at each step.

Role: lets the density argument enlarge a finite family cutoff while preserving an upper bound.
-/
theorem primitiveCharacterFamilyZeroCount_mono_cutoff (T U : ℕ) (hTU : T ≤ U) (σ : ℝ) (hσ : σ ≤ 1) :
    primitiveCharacterFamilyZeroCount T σ ≤ primitiveCharacterFamilyZeroCount U σ := by
  classical
    induction U, hTU using Nat.le_induction with
  | base => exact le_rfl
  | succ n htn ih => exact le_trans ih (primitiveCharacterFamilyZeroCount_succ n σ hσ)

/--
Inputs: an exponent `δ ≤ 1/2` and a dyadic height index `j`.

Claim: the power `2^(δ(j+1))` is bounded by `2*(3/2)^j`.

Proof: bound `2^δ` by `sqrt 2 ≤ 3/2`, then use monotonicity of natural powers.

Role: converts the high-real-part range of a power-shaped log-free density estimate into the
geometric envelope used by the inverse-height block sum.
-/
theorem dyadic_rpow_le_two_mul_three_halves (δ : ℝ) (hδ : δ ≤ 1 / 2) (j : ℕ) :
    Real.rpow 2 (δ * ((j + 1 : ℕ) : ℝ)) ≤ 2 * (3 / 2 : ℝ) ^ j := by
  have hbase : Real.rpow 2 δ ≤ (3 / 2 : ℝ) := by
    calc
      Real.rpow 2 δ ≤ Real.rpow 2 (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num only) hδ
      _ = Real.sqrt 2 := by rw [Real.rpow_eq_pow, ← Real.sqrt_eq_rpow]
      _ ≤ 3 / 2 := by
        apply Real.sqrt_le_iff.mpr
        exact ⟨by positivity, by norm_num only⟩
  rw [Real.rpow_eq_pow, Real.rpow_mul_natCast (by norm_num only : (0 : ℝ) ≤ 2)]
  calc
    (Real.rpow 2 δ) ^ (j + 1) ≤ (3 / 2 : ℝ) ^ (j + 1) :=
      pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num only) δ) hbase (j + 1)
    _ = (3 / 2 : ℝ) * (3 / 2 : ℝ) ^ j := by rw [pow_succ']
    _ ≤ 2 * (3 / 2 : ℝ) ^ j :=
      mul_le_mul_of_nonneg_right (by norm_num only : (3 / 2 : ℝ) ≤ 2) (by positivity)

/-- Rewrite a real power at the natural dyadic height as a power of two. -/
theorem dyadic_height_rpow_eq (δ : ℝ) (j : ℕ) :
    Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ = Real.rpow 2 (δ * ((j + 1 : ℕ) : ℝ)) := by
  rw [Nat.cast_pow]
  norm_num only
  rw [Real.rpow_eq_pow]
  rw [← Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 2) (j + 1) δ]
  rw [mul_comm ((j + 1 : ℕ) : ℝ) δ]
  exact (Real.rpow_eq_pow 2 (δ * ((j + 1 : ℕ) : ℝ))).symm

/--
Inputs: a finite sequence of nonnegative height-block counts bounded by twice a constant times
`(3/2)^j`.

Claim: weighting each block by `2^{-j}` gives a total at most eight times that constant.

Proof: the weighted block is bounded by a constant multiple of `(3/4)^j`; sum the geometric
series using its exact infinite sum.

Role: converts a log-free zero-count estimate on dyadic height intervals into a uniformly bounded
inverse-height zero sum in the high-real-part range.
-/
theorem finite_dyadic_inverse_height_sum_le_eight (J : ℕ) (C : ℝ) (hC : 0 ≤ C) (count : ℕ → ℝ)
    (hcount : ∀ j < J, count j ≤ 2 * C * (3 / 2 : ℝ) ^ j) :
    (∑ j ∈ Finset.range J, count j * (1 / 2 : ℝ) ^ j) ≤ 8 * C := by
  have hgeom :=
    summable_geometric_of_lt_one (by norm_num only : (0 : ℝ) ≤ 3 / 4)
      (by norm_num only : (3 / 4 : ℝ) < 1)
  have hsum : (∑ j ∈ Finset.range J, ((3 / 4 : ℝ) ^ j)) ≤ 4 := by
    calc
      _ ≤ ∑' j : ℕ, ((3 / 4 : ℝ) ^ j) :=
        hgeom.sum_le_tsum (Finset.range J) (fun j hj => by positivity)
      _ = (1 - (3 / 4 : ℝ))⁻¹ :=
        tsum_geometric_of_lt_one (by norm_num only : (0 : ℝ) ≤ 3 / 4)
          (by norm_num only : (3 / 4 : ℝ) < 1)
      _ = 4 := by norm_num only
  calc
    _ ≤ ∑ j ∈ Finset.range J, 2 * C * (3 / 4 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := hcount j (Finset.mem_range.mp hj)
      have hpow : 0 ≤ (1 / 2 : ℝ) ^ j := by positivity
      calc
        count j * (1 / 2 : ℝ) ^ j ≤ (2 * C * (3 / 2 : ℝ) ^ j) * (1 / 2 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hj' hpow
        _ = 2 * C * (3 / 4 : ℝ) ^ j := by
          rw [mul_assoc, ← mul_pow]
          norm_num only
    _ = 2 * C * ∑ j ∈ Finset.range J, (3 / 4 : ℝ) ^ j := by rw [Finset.mul_sum]
    _ ≤ 2 * C * 4 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 8 * C := by ring

/--
Inputs: a real-part threshold at most one, a nonnegative constant, and a cumulative family zero
count bound on each dyadic height endpoint.

Claim: the analytic-multiplicity zero counts in the dyadic height bands have inverse-height weighted
sum at most eight times the constant.

Proof: each band count is bounded by its cumulative endpoint count; apply
`finite_dyadic_inverse_height_sum_le_eight`.

Role: converts a prospective log-free density estimate for `primitiveCharacterFamilyZeroCount`
into the high-real-part zero sum used by the explicit formula.
-/
theorem primitiveCharacterFamilyZeroCount_dyadic_inverse_height_sum_le_eight (σ C : ℝ) (hσ : σ ≤ 1)
    (hC : 0 ≤ C) (J : ℕ)
    (hdensity :
      ∀ j < J, primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ ≤ 2 * C * (3 / 2 : ℝ) ^ j) :
    (∑ j ∈ Finset.range J,
        (primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ -
            primitiveCharacterFamilyZeroCount (2 ^ j) σ) *
          (1 / 2 : ℝ) ^ j) ≤
      8 * C := by
  apply finite_dyadic_inverse_height_sum_le_eight J C hC
  intro j hj
  have hscale : 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ j)
  have hmono := primitiveCharacterFamilyZeroCount_mono_cutoff (2 ^ j) (2 ^ (j + 1)) hscale σ hσ
  have hnonneg := primitiveCharacterFamilyZeroCount_nonneg (2 ^ j) σ
  exact le_trans (sub_le_self _ hnonneg) (hdensity j hj)

/--
Inputs: a real-part threshold, a nonnegative density constant, an exponent at most `1/2`, and a
power-shaped upper bound for the cumulative family zero count at every dyadic height endpoint.

Claim: the dyadic-band zero counts have inverse-height weighted sum at most eight times the density
constant.

Proof: apply `dyadic_rpow_le_two_mul_three_halves` to each endpoint bound, then use
`primitiveCharacterFamilyZeroCount_dyadic_inverse_height_sum_le_eight`.

Role: provides the high-real-part height-summation step from a power-form log-free density estimate.
-/
theorem primitiveCharacterFamilyZeroCount_dyadic_inverse_height_sum_le_eight_of_rpow_density
    (σ C δ : ℝ) (hσ : σ ≤ 1) (hC : 0 ≤ C) (hδ : δ ≤ 1 / 2) (J : ℕ)
    (hdensity :
      ∀ j < J,
        primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ ≤
          C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ) :
    (∑ j ∈ Finset.range J,
        (primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ -
            primitiveCharacterFamilyZeroCount (2 ^ j) σ) *
          (1 / 2 : ℝ) ^ j) ≤
      8 * C := by
  apply primitiveCharacterFamilyZeroCount_dyadic_inverse_height_sum_le_eight σ C hσ hC J
  intro j hj
  calc
    primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ ≤ C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ :=
      hdensity j hj
    _ = C * Real.rpow 2 (δ * ((j + 1 : ℕ) : ℝ)) := by rw [dyadic_height_rpow_eq]
    _ ≤ 2 * C * (3 / 2 : ℝ) ^ j := by
      calc
        C * Real.rpow 2 (δ * ((j + 1 : ℕ) : ℝ)) ≤ C * (2 * (3 / 2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left (dyadic_rpow_le_two_mul_three_halves δ hδ j) hC
        _ = 2 * C * (3 / 2 : ℝ) ^ j := by ring

/--
Inputs: a positive density exponent `A`, a real-part threshold in `[1/2,1]`, a nonnegative
constant, and the power-form family zero-count bound at dyadic heights.

Claim: if `A(1-σ) ≤ 1/2`, the dyadic-band inverse-height sum is at most eight times the density
constant.

Proof: specialize
`primitiveCharacterFamilyZeroCount_dyadic_inverse_height_sum_le_eight_of_rpow_density` to
`δ = A(1-σ)`.

Role: states the high-real-part consequence directly in the parameters of the log-free density
theorem sought for the AGP theta argument.
-/
theorem primitiveCharacterFamilyZeroCount_dyadic_inverse_height_sum_le_eight_of_log_free_density
    (A σ C : ℝ) (hσone : σ ≤ 1) (hδ : A * (1 - σ) ≤ 1 / 2) (hC : 0 ≤ C) (J : ℕ)
    (hdensity :
      ∀ j < J,
        primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ ≤
          C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) (A * (1 - σ))) :
    (∑ j ∈ Finset.range J,
        (primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ -
            primitiveCharacterFamilyZeroCount (2 ^ j) σ) *
          (1 / 2 : ℝ) ^ j) ≤
      8 * C := by
  exact
    primitiveCharacterFamilyZeroCount_dyadic_inverse_height_sum_le_eight_of_rpow_density σ C
      (A * (1 - σ)) hσone hC hδ J hdensity

/--
Inputs: a real-part threshold, a nonnegative density constant, an exponent at most `1/2`, and a
power-form density bound at every dyadic height endpoint.

Claim: the inverse-height weighted zero counts over all dyadic bands form a summable sequence.

Proof: monotonicity makes every band count nonnegative; the endpoint density bound and the dyadic
power estimate dominate each weighted term by `2*C*(3/4)^j`.

Role: supplies the convergent high-real-part height sum needed when passing from finite truncations
of the explicit formula to an unbounded zero sum.
-/
theorem summable_primitiveCharacterFamilyZeroCount_dyadic_inverse_height_bands_of_rpow_density
    (σ C δ : ℝ) (hσ : σ ≤ 1) (hC : 0 ≤ C) (hδ : δ ≤ 1 / 2)
    (hdensity :
      ∀ j : ℕ,
        primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ ≤
          C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ) :
    Summable
      (fun j : ℕ =>
        (primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ -
            primitiveCharacterFamilyZeroCount (2 ^ j) σ) *
          (1 / 2 : ℝ) ^ j) := by
  apply Summable.of_nonneg_of_le
  · intro j
    have hscale : 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ j)
    have hmono := primitiveCharacterFamilyZeroCount_mono_cutoff (2 ^ j) (2 ^ (j + 1)) hscale σ hσ
    have hband :
      0 ≤
        primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ -
          primitiveCharacterFamilyZeroCount (2 ^ j) σ :=
      sub_nonneg.mpr hmono
    exact mul_nonneg hband (by positivity)
  · intro j
    have hlow := primitiveCharacterFamilyZeroCount_nonneg (2 ^ j) σ
    have hband := sub_le_self (primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ) hlow
    calc
      _ ≤ (C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ) * (1 / 2 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_right (le_trans hband (hdensity j)) (by positivity)
      _ = C * Real.rpow 2 (δ * ((j + 1 : ℕ) : ℝ)) * (1 / 2 : ℝ) ^ j := by rw [dyadic_height_rpow_eq]
      _ ≤ (C * (2 * (3 / 2 : ℝ) ^ j)) * (1 / 2 : ℝ) ^ j := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (dyadic_rpow_le_two_mul_three_halves δ hδ j) hC
        · positivity
      _ = 2 * C * (3 / 4 : ℝ) ^ j := by
        calc
          _ = (2 * C * (3 / 2 : ℝ) ^ j) * (1 / 2 : ℝ) ^ j := by ring
          _ = 2 * C * (3 / 4 : ℝ) ^ j := by
            rw [mul_assoc, ← mul_pow]
            norm_num only
  · exact
      (summable_geometric_of_lt_one (by norm_num only : (0 : ℝ) ≤ 3 / 4)
            (by norm_num only : (3 / 4 : ℝ) < 1)).mul_left
        (2 * C)

/-- Log-free density with `A(1-σ) ≤ 1/2` implies summability of the dyadic inverse-height bands. -/
theorem summable_primitiveCharacterFamilyZeroCount_dyadic_inverse_height_bands_of_log_free_density
    (A σ C : ℝ) (hσone : σ ≤ 1) (hδ : A * (1 - σ) ≤ 1 / 2) (hC : 0 ≤ C)
    (hdensity :
      ∀ j : ℕ,
        primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ ≤
          C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) (A * (1 - σ))) :
    Summable
      (fun j : ℕ =>
        (primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ -
            primitiveCharacterFamilyZeroCount (2 ^ j) σ) *
          (1 / 2 : ℝ) ^ j) := by
  exact
    summable_primitiveCharacterFamilyZeroCount_dyadic_inverse_height_bands_of_rpow_density σ C
      (A * (1 - σ)) hσone hC hδ hdensity

/--
Inputs: a real-part threshold at most one, a nonnegative constant, an exponent at most `1/2`, and
an endpoint power bound for the primitive-character family zero count at every dyadic height.

Claim: the sum over all dyadic height bands, weighted by inverse height, is at most `8*C`.

Proof: compare each nonnegative band with `2*C*(3/4)^j`, use summability of the geometric series,
and evaluate its sum.

Role: gives an untruncated inverse-height estimate for the high-real-part zero contribution used
with the explicit formula.
-/
theorem primitiveCharacterFamilyZeroCount_tsum_dyadic_inverse_height_bands_le_eight_of_rpow_density
    (σ C δ : ℝ) (hσ : σ ≤ 1) (hC : 0 ≤ C) (hδ : δ ≤ 1 / 2)
    (hdensity :
      ∀ j : ℕ,
        primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ ≤
          C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ) :
    ∑' j : ℕ,
        (primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ -
            primitiveCharacterFamilyZeroCount (2 ^ j) σ) *
          (1 / 2 : ℝ) ^ j ≤
      8 * C := by
  let f : ℕ → ℝ := fun j =>
    (primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ -
        primitiveCharacterFamilyZeroCount (2 ^ j) σ) *
      (1 / 2 : ℝ) ^ j
  let g : ℕ → ℝ := fun j => 2 * C * (3 / 4 : ℝ) ^ j
  have hf : Summable f := by
    dsimp only [f]
    exact
      summable_primitiveCharacterFamilyZeroCount_dyadic_inverse_height_bands_of_rpow_density σ C δ
        hσ hC hδ hdensity
  have hg : Summable g := by
    dsimp only [g]
    exact
      (summable_geometric_of_lt_one (by norm_num only : (0 : ℝ) ≤ 3 / 4)
            (by norm_num only : (3 / 4 : ℝ) < 1)).mul_left
        (2 * C)
  have hle : ∀ j, f j ≤ g j := by
    intro j
    dsimp only [f, g]
    have hlow := primitiveCharacterFamilyZeroCount_nonneg (2 ^ j) σ
    have hband := sub_le_self (primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ) hlow
    calc
      _ ≤ (C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ) * (1 / 2 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_right (le_trans hband (hdensity j)) (by positivity)
      _ = C * Real.rpow 2 (δ * ((j + 1 : ℕ) : ℝ)) * (1 / 2 : ℝ) ^ j := by rw [dyadic_height_rpow_eq]
      _ ≤ (C * (2 * (3 / 2 : ℝ) ^ j)) * (1 / 2 : ℝ) ^ j := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (dyadic_rpow_le_two_mul_three_halves δ hδ j) hC
        · positivity
      _ = 2 * C * (3 / 4 : ℝ) ^ j := by
        calc
          _ = (2 * C * (3 / 2 : ℝ) ^ j) * (1 / 2 : ℝ) ^ j := by ring
          _ = 2 * C * (3 / 4 : ℝ) ^ j := by
            rw [mul_assoc, ← mul_pow]
            norm_num only
  have htsum := Summable.tsum_le_tsum hle hf hg
  calc
    _ = ∑' j, f j := by rfl
    _ ≤ ∑' j, g j := htsum
    _ = (2 * C) * (1 - (3 / 4 : ℝ))⁻¹ := by
      dsimp only [g]
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one (by norm_num only : (0 : ℝ) ≤ 3 / 4)
          (by norm_num only : (3 / 4 : ℝ) < 1)]
    _ = 8 * C := by ring

/-- Log-free density with `A(1-σ) ≤ 1/2` bounds the full dyadic inverse-height sum by `8*C`. -/
theorem primitiveCharacterFamilyZeroCount_tsum_inverse_height_le_eight_of_density (A σ C : ℝ)
    (hσone : σ ≤ 1) (hδ : A * (1 - σ) ≤ 1 / 2) (hC : 0 ≤ C)
    (hdensity :
      ∀ j : ℕ,
        primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ ≤
          C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) (A * (1 - σ))) :
    ∑' j : ℕ,
        (primitiveCharacterFamilyZeroCount (2 ^ (j + 1)) σ -
            primitiveCharacterFamilyZeroCount (2 ^ j) σ) *
          (1 / 2 : ℝ) ^ j ≤
      8 * C := by
  exact
    primitiveCharacterFamilyZeroCount_tsum_dyadic_inverse_height_bands_le_eight_of_rpow_density σ C
      (A * (1 - σ)) hσone hC hδ hdensity

/--
Inputs: a real sequence indexed by the natural numbers and a finite cutoff.

Claim: the weighted sum of successive differences has the finite partial-summation identity
`sum Δaₙ/n = a_N/(N+1) - a_0 + sum aₙ/(n(n+1))` for indices `1 ≤ n ≤ N`.

Proof: induct on the cutoff, adding the final difference and combining the two adjacent rational
weights at each step.

Role: provides the discrete summation-by-parts formula used to estimate zero sums by cumulative
zero counts.
-/
theorem finite_sum_differences_div_succ_eq (a : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (a (k + 1) - a k) / (k + 1 : ℝ)) =
      a N / (N + 1 : ℝ) - a 0 + ∑ k ∈ Finset.range N, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_add]
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [Nat.cast_succ]
    have hden : (↑N + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hden]
    ring

/--
Inputs: a positive natural height cutoff and the primitive-character family zero count.

Claim: the sum of successive dyadic-independent height-count increments divided by their heights is
at most the terminal count divided by the cutoff plus the sum of cumulative counts divided by
squared heights.

Proof: apply `finite_sum_differences_div_succ_eq`, use the zero count at height zero, and bound
`1/(n(n+1))` by `1/n^2` termwise.

Role: bounds increments of the family sum when both its modulus and height cutoffs vary together.
-/
theorem primitiveCharacterFamilyZeroCount_partial_summation_le (T : ℕ) (hT : 1 ≤ T) (σ : ℝ) :
    (∑ k ∈ Finset.range T,
        (primitiveCharacterFamilyZeroCount (k + 1) σ - primitiveCharacterFamilyZeroCount k σ) /
          (k + 1 : ℝ)) ≤
      primitiveCharacterFamilyZeroCount T σ / (T : ℝ) +
        ∑ k ∈ Finset.range T, primitiveCharacterFamilyZeroCount (k + 1) σ / (k + 1 : ℝ) ^ 2 := by
  let a : ℕ → ℝ := fun n => primitiveCharacterFamilyZeroCount n σ
  have ha0 : a 0 = 0 := by
    dsimp only [a]
    classical simp only [primitiveCharacterFamilyZeroCount, Finset.univ_eq_empty, Finset.sum_empty]
  have hid := finite_sum_differences_div_succ_eq a T
  have hTposNat : 0 < T := lt_of_lt_of_le Nat.zero_lt_one hT
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hTposNat
  have hTden : (T : ℝ) ≤ (T : ℝ) + 1 := by linarith only
  have hterminal : a T / ((T : ℝ) + 1) ≤ a T / (T : ℝ) :=
    div_le_div_of_nonneg_left (primitiveCharacterFamilyZeroCount_nonneg T σ) hTpos hTden
  have hsum :
    (∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ))) ≤
      ∑ k ∈ Finset.range T, a (k + 1) / (k + 1 : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro k hk
    have hkpos : 0 < (k + 1 : ℝ) := by positivity
    have hden : (k + 1 : ℝ) ^ 2 ≤ (k + 1 : ℝ) * (k + 2 : ℝ) := by nlinarith only [hkpos]
    have hcount := primitiveCharacterFamilyZeroCount_nonneg (k + 1) σ
    exact div_le_div_of_nonneg_left hcount (sq_pos_of_pos hkpos) (by nlinarith only [hkpos])
  calc
    _ = a T / ((T : ℝ) + 1) + ∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
      rw [show a 0 = 0 from ha0] at hid
      dsimp only [a]
      linarith only [hid]
    _ ≤ a T / (T : ℝ) + ∑ k ∈ Finset.range T, a (k + 1) / (k + 1 : ℝ) ^ 2 :=
      add_le_add hterminal hsum

/-- Convert a real height bound on a completed zero count to an integer height endpoint. -/
noncomputable def completedZeroCountAtNatHeight {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (σ : ℝ) (n : ℕ) : ℝ :=
  PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ (n : ℝ)

/-- A completed zero count at an integer height is nonnegative with analytic multiplicity. -/
theorem completedZeroCountAtNatHeight_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (σ : ℝ) (n : ℕ) : 0 ≤ completedZeroCountAtNatHeight χ hχ σ n :=
  PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount_nonneg χ hχ σ (n : ℝ)

/-- Increasing the integer height cutoff cannot decrease a fixed completed zero count. -/
theorem completedZeroCountAtNatHeight_mono {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {σ : ℝ} (hσ : σ ≤ 1) {n m : ℕ} (hnm : n ≤ m) :
    completedZeroCountAtNatHeight χ hχ σ n ≤ completedZeroCountAtNatHeight χ hχ σ m := by
  exact
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount_mono_height χ hχ hσ
      (Nat.cast_nonneg n) (by exact_mod_cast hnm)

/--
Inputs: a nonprincipal character, a real-part threshold, and a positive integer height cutoff.

Claim: the height-increment sum of the multiplicity-weighted completed zero count, divided by each
integer height, is bounded by the terminal count divided by the cutoff plus the squared-height
sum of cumulative counts.

Proof: apply finite summation by parts, discard the nonnegative count at height zero, and bound
`1/(n(n+1))` by `1/n^2`.

Role: gives the fixed-character integer-height estimate used in the AGP explicit-formula argument.
-/
theorem completedZeroCountAtNatHeight_partial_summation_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (σ : ℝ) (T : ℕ) (hT : 1 ≤ T) :
    (∑ k ∈ Finset.range T,
        (completedZeroCountAtNatHeight χ hχ σ (k + 1) - completedZeroCountAtNatHeight χ hχ σ k) /
          (k + 1 : ℝ)) ≤
      completedZeroCountAtNatHeight χ hχ σ T / (T : ℝ) +
        ∑ k ∈ Finset.range T, completedZeroCountAtNatHeight χ hχ σ (k + 1) / (k + 1 : ℝ) ^ 2 := by
  let a : ℕ → ℝ := fun n => completedZeroCountAtNatHeight χ hχ σ n
  have hid := finite_sum_differences_div_succ_eq a T
  have hTposNat : 0 < T := lt_of_lt_of_le Nat.zero_lt_one hT
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hTposNat
  have hTden : (T : ℝ) ≤ (T : ℝ) + 1 := by linarith only
  have hterminal : a T / ((T : ℝ) + 1) ≤ a T / (T : ℝ) :=
    div_le_div_of_nonneg_left (completedZeroCountAtNatHeight_nonneg χ hχ σ T) hTpos hTden
  have hsum :
    (∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ))) ≤
      ∑ k ∈ Finset.range T, a (k + 1) / (k + 1 : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro k hk
    have hkpos : 0 < (k + 1 : ℝ) := by positivity
    have hden : (k + 1 : ℝ) ^ 2 ≤ (k + 1 : ℝ) * (k + 2 : ℝ) := by nlinarith only [hkpos]
    exact
      div_le_div_of_nonneg_left (completedZeroCountAtNatHeight_nonneg χ hχ σ (k + 1))
        (sq_pos_of_pos hkpos) (by nlinarith only [hkpos])
  have ha0 : 0 ≤ a 0 := completedZeroCountAtNatHeight_nonneg χ hχ σ 0
  have hid' :
    (∑ k ∈ Finset.range T, (a (k + 1) - a k) / (k + 1 : ℝ)) =
      a T / ((T : ℝ) + 1) - a 0 + ∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ)) :=
    hid
  have hremove :
    a T / ((T : ℝ) + 1) - a 0 + ∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ)) ≤
      a T / (T : ℝ) + ∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
    linarith only [ha0, hterminal]
  calc
    _ = a T / ((T : ℝ) + 1) - a 0 + ∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ)) :=
      by simpa only [a] using hid'
    _ ≤ a T / (T : ℝ) + ∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ)) := hremove
    _ = a T / (T : ℝ) + (∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ))) := by ring
    _ ≤ a T / (T : ℝ) + (∑ k ∈ Finset.range T, a (k + 1) / (k + 1 : ℝ) ^ 2) :=
      add_le_add_right hsum _
    _ = _ := by simp only [a]

/--
Inputs: a nonnegative real sequence and a positive integer cutoff.

Claim: the weighted sum of successive differences is bounded by the terminal count divided by the
cutoff and the cumulative counts weighted by reciprocal squared height.

Proof: apply the finite summation-by-parts identity, discard the nonnegative initial count, and
bound `1/(n(n+1))` by `1/n^2` termwise.

Role: packages the height estimate for application to individual characters and finite character
families.
-/
theorem finite_sum_differences_div_succ_le (a : ℕ → ℝ) (T : ℕ) (hT : 1 ≤ T) (ha : ∀ n, 0 ≤ a n) :
    (∑ k ∈ Finset.range T, (a (k + 1) - a k) / (k + 1 : ℝ)) ≤
      a T / (T : ℝ) + ∑ k ∈ Finset.range T, a (k + 1) / (k + 1 : ℝ) ^ 2 := by
  have hid := finite_sum_differences_div_succ_eq a T
  have hTposNat : 0 < T := lt_of_lt_of_le Nat.zero_lt_one hT
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hTposNat
  have hTden : (T : ℝ) ≤ (T : ℝ) + 1 := by linarith only
  have hterminal : a T / ((T : ℝ) + 1) ≤ a T / (T : ℝ) :=
    div_le_div_of_nonneg_left (ha T) hTpos hTden
  have hsum :
    (∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ))) ≤
      ∑ k ∈ Finset.range T, a (k + 1) / (k + 1 : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro k hk
    have hkpos : 0 < (k + 1 : ℝ) := by positivity
    have hden : (k + 1 : ℝ) ^ 2 ≤ (k + 1 : ℝ) * (k + 2 : ℝ) := by nlinarith only [hkpos]
    exact div_le_div_of_nonneg_left (ha (k + 1)) (sq_pos_of_pos hkpos) (by nlinarith only [hkpos])
  have hremove :
    a T / ((T : ℝ) + 1) - a 0 + ∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ)) ≤
      a T / (T : ℝ) + ∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
    linarith only [ha 0, hterminal]
  calc
    _ = a T / ((T : ℝ) + 1) - a 0 + ∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ)) :=
      hid
    _ ≤ a T / (T : ℝ) + ∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ)) := hremove
    _ = a T / (T : ℝ) + (∑ k ∈ Finset.range T, a (k + 1) / ((k + 1 : ℝ) * (k + 2 : ℝ))) := by ring
    _ ≤ a T / (T : ℝ) + (∑ k ∈ Finset.range T, a (k + 1) / (k + 1 : ℝ) ^ 2) :=
      add_le_add_right hsum _
    _ = _ := by ring

/--
Purpose: sum the analytic-multiplicity zero counts of all nonprincipal characters at a fixed
modulus and integer height.

Inputs: a nonzero modulus, a real-part threshold, and a natural height cutoff.

Output: the total completed zero count for the fixed modulus; the principal character contributes
zero so its pole is not included in the zero sum.

Role: gives the fixed-modulus family required by the explicit formula without varying the modulus
cutoff as the height changes.
-/
noncomputable def fixedModulusNonprincipalZeroCountAtNatHeight (q : ℕ) [NeZero q] (σ : ℝ) (n : ℕ) :
    ℝ := by
  classical
    exact
    ∑ χ : DirichletCharacter ℂ q, if hχ : χ ≠ 1 then completedZeroCountAtNatHeight χ hχ σ n else 0

/-- The fixed-modulus nonprincipal completed zero count is nonnegative. -/
theorem fixedModulusNonprincipalZeroCountAtNatHeight_nonneg (q : ℕ) [NeZero q] (σ : ℝ) (n : ℕ) :
    0 ≤ fixedModulusNonprincipalZeroCountAtNatHeight q σ n := by
  classical
  unfold fixedModulusNonprincipalZeroCountAtNatHeight
  apply Finset.sum_nonneg
  intro χ hχmem
  split_ifs with hχ
  · exact completedZeroCountAtNatHeight_nonneg χ hχ σ n
  · exact le_of_eq rfl

/-- The fixed-modulus zero count increases with the integer height when `σ ≤ 1`. -/
theorem fixedModulusNonprincipalZeroCountAtNatHeight_mono (q : ℕ) [NeZero q] {σ : ℝ} (hσ : σ ≤ 1)
    {n m : ℕ} (hnm : n ≤ m) :
    fixedModulusNonprincipalZeroCountAtNatHeight q σ n ≤
      fixedModulusNonprincipalZeroCountAtNatHeight q σ m := by
  classical
  unfold fixedModulusNonprincipalZeroCountAtNatHeight
  apply Finset.sum_le_sum
  intro χ hχmem
  split_ifs with hχ
  · exact completedZeroCountAtNatHeight_mono χ hχ hσ hnm
  · exact le_rfl

/-- Summation by parts for the fixed-modulus family of nonprincipal completed zeros. -/
theorem fixedModulusNonprincipalZeroCountAtNatHeight_partial_summation_le (q : ℕ) [NeZero q] (σ : ℝ)
    (T : ℕ) (hT : 1 ≤ T) :
    (∑ k ∈ Finset.range T,
        (fixedModulusNonprincipalZeroCountAtNatHeight q σ (k + 1) -
            fixedModulusNonprincipalZeroCountAtNatHeight q σ k) /
          (k + 1 : ℝ)) ≤
      fixedModulusNonprincipalZeroCountAtNatHeight q σ T / (T : ℝ) +
        ∑ k ∈ Finset.range T,
          fixedModulusNonprincipalZeroCountAtNatHeight q σ (k + 1) / (k + 1 : ℝ) ^ 2 := by
  exact
    finite_sum_differences_div_succ_le (fun n => fixedModulusNonprincipalZeroCountAtNatHeight q σ n)
      T hT (fun n => fixedModulusNonprincipalZeroCountAtNatHeight_nonneg q σ n)

/--
Purpose: aggregate the analytic-multiplicity zero counts of nonprincipal characters over all
positive moduli below `Q`, at a natural height.

Inputs: a conductor cutoff `Q`, a real-part threshold, and a height.

Output: the finite sum of the fixed-modulus counts for moduli `1` through `Q`.

Role: supplies a fixed-conductor-cutoff family for estimates whose height cutoff varies separately.
-/
noncomputable def fixedModulusFamilyNonprincipalZeroCountAtNatHeight (Q : ℕ) (σ : ℝ) (n : ℕ) :
    ℝ := by
  classical exact ∑ q ∈ Finset.range Q, fixedModulusNonprincipalZeroCountAtNatHeight (q + 1) σ n

/-- The fixed-cutoff family count is nonnegative. -/
theorem fixedModulusFamilyNonprincipalZeroCountAtNatHeight_nonneg (Q : ℕ) (σ : ℝ) (n : ℕ) :
    0 ≤ fixedModulusFamilyNonprincipalZeroCountAtNatHeight Q σ n := by
  classical
  unfold fixedModulusFamilyNonprincipalZeroCountAtNatHeight
  apply Finset.sum_nonneg
  intro q hq
  exact fixedModulusNonprincipalZeroCountAtNatHeight_nonneg (q + 1) σ n

/-- The fixed-cutoff family count increases with height when `σ ≤ 1`. -/
theorem fixedModulusFamilyNonprincipalZeroCountAtNatHeight_mono (Q : ℕ) {σ : ℝ} (hσ : σ ≤ 1)
    {n m : ℕ} (hnm : n ≤ m) :
    fixedModulusFamilyNonprincipalZeroCountAtNatHeight Q σ n ≤
      fixedModulusFamilyNonprincipalZeroCountAtNatHeight Q σ m := by
  classical
  unfold fixedModulusFamilyNonprincipalZeroCountAtNatHeight
  apply Finset.sum_le_sum
  intro q hq
  exact fixedModulusNonprincipalZeroCountAtNatHeight_mono (q + 1) hσ hnm

/-- Summation by parts for the family with a fixed modulus cutoff. -/
theorem fixedModulusFamilyNonprincipalZeroCountAtNatHeight_partial_summation_le (Q : ℕ) (σ : ℝ)
    (T : ℕ) (hT : 1 ≤ T) :
    (∑ k ∈ Finset.range T,
        (fixedModulusFamilyNonprincipalZeroCountAtNatHeight Q σ (k + 1) -
            fixedModulusFamilyNonprincipalZeroCountAtNatHeight Q σ k) /
          (k + 1 : ℝ)) ≤
      fixedModulusFamilyNonprincipalZeroCountAtNatHeight Q σ T / (T : ℝ) +
        ∑ k ∈ Finset.range T,
          fixedModulusFamilyNonprincipalZeroCountAtNatHeight Q σ (k + 1) / (k + 1 : ℝ) ^ 2 := by
  exact
    finite_sum_differences_div_succ_le
      (fun n => fixedModulusFamilyNonprincipalZeroCountAtNatHeight Q σ n) T hT
      (fun n => fixedModulusFamilyNonprincipalZeroCountAtNatHeight_nonneg Q σ n)

/--
Purpose: count zeros of primitive nonprincipal characters up to a fixed modulus cutoff and an
independently chosen natural height.

Inputs: a modulus cutoff, a real-part threshold, and an integer height.

Output: the sum of completed zero counts, with analytic multiplicity, over primitive characters
whose positive moduli do not exceed the cutoff.

Role: separates the conductor and height parameters in the family used by log-free density.
-/
noncomputable def primitiveCharacterFamilyZeroCountAtNatHeight (Q : ℕ) (σ : ℝ) (n : ℕ) : ℝ := by
  classical
    exact
    ∑ q : Fin Q,
      ∑ χ : DirichletCharacter ℂ (q.val + 1),
        if hχ : χ ≠ 1 then
          if hprim : χ.IsPrimitive then completedZeroCountAtNatHeight χ hχ σ n else 0
        else 0

/--
Purpose: express the primitive family zero count as a sum of finite zero occurrence counts.

Definition: sum the cardinalities of the multiplicity-indexed occurrence ledgers over primitive,
nonprincipal characters and their moduli.

Inputs: a modulus cutoff, a real-part threshold, and a natural height.

Output: a real-valued count that retains each zero's analytic multiplicity through distinct finite
indices.

Role: exposes a finite occurrence representation for the family count used by density estimates.
-/
noncomputable def primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight (Q : ℕ) (σ : ℝ) (n : ℕ) :
    ℝ := by
  classical
    exact
    ∑ q : Fin Q,
      ∑ χ : DirichletCharacter ℂ (q.val + 1),
        if hχ : χ ≠ 1 then
          if hprim : χ.IsPrimitive then
            (completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (n : ℝ) * Complex.I)
                ((1 : ℂ) + (n : ℝ) * Complex.I)).card
          else 0
        else 0

/--
Inputs: a modulus cutoff, real-part threshold, and natural height.

Claim: the existing primitive family zero count equals its multiplicity-indexed occurrence count.

Proof: unfold both finite sums and use the rectangle theorem equating each zero count with the
cardinality of its occurrence ledger.

Role: verifies that the finite family representation preserves analytic multiplicity exactly.
-/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_eq_occurrenceCount (Q : ℕ) (σ : ℝ) (n : ℕ) :
    primitiveCharacterFamilyZeroCountAtNatHeight Q σ n =
      primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ n := by
  classical
  unfold primitiveCharacterFamilyZeroCountAtNatHeight
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro χ hχmem
  by_cases hχ : χ ≠ 1
  · by_cases hprim : χ.IsPrimitive
    · simp only [dite_eq_left hχ, dite_eq_left hprim]
      rw [completedZeroCountAtNatHeight, completedZeroCount]
      exact
        completedZeroMultiplicityCountInRectangle_eq_occurrence_card χ hχ
          ((σ : ℂ) - (n : ℝ) * Complex.I) ((1 : ℂ) + (n : ℝ) * Complex.I)
    · simp only [dite_eq_left hχ, dite_eq_right hprim]
  · simp only [dite_eq_right hχ]

/--
Purpose: assemble every primitive-family completed zero occurrence into one finite ledger.

Definition: nest finite sums over conductors, characters, distinct zero values, and indices below
each zero's analytic order.

Inputs: a conductor cutoff, a real-part threshold, and a natural height.

Output: a finite set retaining the conductor, character, zero value, and multiplicity index, even
when different characters share a zero value.

Role: supplies a single finite counting domain for multiplicity-preserving family arguments.
-/
noncomputable def primitiveCharacterFamilyZeroOccurrenceLedger (Q : ℕ) (σ : ℝ) (n : ℕ) :
    Finset
      (Σ q : Fin Q,
        Σ χ : DirichletCharacter ℂ (q.val + 1),
          Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)) := by
  classical
    exact
    (Finset.univ : Finset (Fin Q)).sigma fun q =>
      (Finset.univ : Finset (DirichletCharacter ℂ (q.val + 1))).sigma fun χ =>
        if hχ : χ ≠ 1 then
          if hprim : χ.IsPrimitive then
            completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (n : ℝ) * Complex.I)
              ((1 : ℂ) + (n : ℝ) * Complex.I)
          else ∅
        else ∅

/--
Inputs: an element of the primitive-family occurrence ledger.

Claim: the element records a nonprincipal primitive character, a zero in its height rectangle,
and an index below that zero's analytic order.

Proof: decompose the nested finite sigma membership and eliminate the empty branches for
nonprimitive or principal characters.

Role: exposes the analytic zero represented by a ledger entry to later derivative estimates.
-/
theorem primitiveCharacterFamilyZeroOccurrenceLedger_mem_extract {Q : ℕ} {σ : ℝ} {n : ℕ}
    {x :
      Σ q : Fin Q,
        Σ χ : DirichletCharacter ℂ (q.val + 1),
          Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)}
    (hx : x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ n) :
    ∃ q χ ρ i,
      ∃ hχ : χ ≠ 1,
        x = ⟨q, ⟨χ, ⟨ρ, i⟩⟩⟩ ∧
          χ.IsPrimitive ∧
          ρ ∈
            completedZerosInRectangle χ hχ ((σ : ℂ) - (n : ℝ) * Complex.I)
              ((1 : ℂ) + (n : ℝ) * Complex.I) := by
  classical
  rcases x with ⟨q, χ, ρ, i⟩
  simp only [primitiveCharacterFamilyZeroOccurrenceLedger, Finset.mem_sigma] at hx
  rcases hx with ⟨_, ⟨_, hxi⟩⟩
  by_cases hχ : χ ≠ 1
  · by_cases hprim : χ.IsPrimitive
    · simp only [dite_eq_left hχ, dite_eq_left hprim] at hxi
      simp only [completedZeroMultiplicityOccurrences, Finset.mem_sigma] at hxi
      exact ⟨q, χ, ρ, i, hχ, rfl, hprim, hxi.1⟩
    · simp only [dite_eq_left hχ, dite_eq_right hprim] at hxi
      exact (Finset.notMem_empty _ hxi).elim
  · simp only [dite_eq_right hχ] at hxi
    exact (Finset.notMem_empty _ hxi).elim

/--
Inputs: an element of the primitive-family occurrence ledger.

Claim: its character has modulus greater than one and a positive completed-zero count at the
ledger's height cutoff.

Proof: use the extracted zero and multiplicity index to show the character occurrence set is
nonempty, then rewrite its cardinality as the analytic-multiplicity count.

Role: supplies the positive-count input for the scaled Turán derivative estimate.
-/
theorem primitiveCharacterFamilyZeroOccurrenceLedger_mem_positive_count {Q : ℕ} {σ : ℝ} {n : ℕ}
    {x :
      Σ q : Fin Q,
        Σ χ : DirichletCharacter ℂ (q.val + 1),
          Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)}
    (hx : x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ n) :
    ∃ q χ,
      ∃ hχ : χ ≠ 1,
        χ.IsPrimitive ∧
          1 < q.val + 1 ∧ ∃ ρ i, x = ⟨q, ⟨χ, ⟨ρ, i⟩⟩⟩ ∧ 0 < completedZeroCount χ hχ σ (n : ℝ) := by
  obtain ⟨q, χ, ρ, i, hχ, hxEq, hprim, hρ⟩ :=
    primitiveCharacterFamilyZeroOccurrenceLedger_mem_extract hx
  subst x
  let z : ℂ := (σ : ℂ) - (n : ℝ) * Complex.I
  let w : ℂ := (1 : ℂ) + (n : ℝ) * Complex.I
  have hmod : 1 < q.val + 1 := by
    by_contra hqnot
    have hqle : q.val + 1 ≤ 1 := Nat.le_of_not_gt hqnot
    have hqzero : q.val = 0 := Nat.eq_zero_of_le_zero (Nat.succ_le_succ_iff.mp hqle)
    have hsub : Subsingleton (DirichletCharacter ℂ (q.val + 1)) := by
      rw [hqzero]
      exact (inferInstance : Subsingleton (DirichletCharacter ℂ 1))
    exact hχ (@Subsingleton.elim (DirichletCharacter ℂ (q.val + 1)) hsub χ 1)
  have hocc :
    (⟨ρ, i⟩ : Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)) ∈
      completedZeroMultiplicityOccurrences χ hχ z w := by
    simp only [completedZeroMultiplicityOccurrences, Finset.mem_sigma]
    exact ⟨hρ, Finset.mem_univ _⟩
  have hcard : 0 < (completedZeroMultiplicityOccurrences χ hχ z w).card :=
    Finset.card_pos.mpr ⟨⟨ρ, i⟩, hocc⟩
  refine ⟨q, χ, hχ, hprim, hmod, ρ, i, rfl, ?_⟩
  rw [completedZeroCount, completedZeroMultiplicityCountInRectangle_eq_occurrence_card]
  exact_mod_cast hcard

/--
Inputs: a conductor cutoff, real-part threshold, and natural height.

Claim: the finite family occurrence ledger has cardinality equal to the multiplicity-indexed
family count.

Proof: expand the dependent finite sums over conductors and characters, then split the primitive
and nonprincipal conditions in each summand.

Role: realizes the existing family zero count as the cardinality of a finite type without losing
analytic multiplicity or character identity.
-/
theorem primitiveCharacterFamilyZeroOccurrenceLedger_card (Q : ℕ) (σ : ℝ) (n : ℕ) :
    ((primitiveCharacterFamilyZeroOccurrenceLedger Q σ n).card : ℝ) =
      primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ n := by
  classical
  simp only [primitiveCharacterFamilyZeroOccurrenceLedger, Finset.card_sigma, Nat.cast_sum,
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro χ hχmem
  by_cases hχ : χ ≠ 1
  · by_cases hprim : χ.IsPrimitive
    · simp only [dite_eq_left hχ, dite_eq_left hprim]
    · simp only [dite_eq_left hχ, dite_eq_right hprim, Finset.card_empty, Nat.cast_zero]
  · simp only [dite_eq_right hχ, Finset.card_empty, Nat.cast_zero]

/-- The primitive-family zero count is exactly the cardinality of its occurrence ledger. -/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_eq_occurrenceLedger_card (Q : ℕ) (σ : ℝ)
    (n : ℕ) :
    primitiveCharacterFamilyZeroCountAtNatHeight Q σ n =
      (primitiveCharacterFamilyZeroOccurrenceLedger Q σ n).card := by
  rw [primitiveCharacterFamilyZeroCountAtNatHeight_eq_occurrenceCount]
  exact (primitiveCharacterFamilyZeroOccurrenceLedger_card Q σ n).symm

/-- The separated primitive-family zero count is nonnegative. -/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_nonneg (Q : ℕ) (σ : ℝ) (n : ℕ) :
    0 ≤ primitiveCharacterFamilyZeroCountAtNatHeight Q σ n := by
  classical
  unfold primitiveCharacterFamilyZeroCountAtNatHeight
  apply Finset.sum_nonneg
  intro q hq
  apply Finset.sum_nonneg
  intro χ hχmem
  split_ifs with hχ hprim
  · exact completedZeroCountAtNatHeight_nonneg χ hχ σ n
  · exact le_of_eq rfl
  · exact le_of_eq rfl

/-- The separated primitive-family zero count increases with height when `σ ≤ 1`. -/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_mono (Q : ℕ) {σ : ℝ} (hσ : σ ≤ 1) {n m : ℕ}
    (hnm : n ≤ m) :
    primitiveCharacterFamilyZeroCountAtNatHeight Q σ n ≤
      primitiveCharacterFamilyZeroCountAtNatHeight Q σ m := by
  classical
  unfold primitiveCharacterFamilyZeroCountAtNatHeight
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro χ hχmem
  split_ifs with hχ hprim
  · exact completedZeroCountAtNatHeight_mono χ hχ hσ hnm
  · exact le_rfl
  · exact le_rfl

/-- At height `Q`, the separated family agrees definitionally with the original joint cutoff. -/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_eq (Q : ℕ) (σ : ℝ) :
    primitiveCharacterFamilyZeroCountAtNatHeight Q σ Q = primitiveCharacterFamilyZeroCount Q σ := by
  rfl

/--
Inputs: a fixed conductor cutoff `Q`, a larger common cutoff `T`, a height `n ≤ T`, and a real-part
threshold at most one.

Claim: the separated primitive-family zero count up to conductors `Q` and height `n` is bounded by
the original diagonal family count at cutoff `T`.

Proof: embed `Fin Q` into `Fin T`, enlarge each character's height by monotonicity, then add the
nonnegative contributions from the remaining moduli.

Role: lets a diagonal log-free density estimate control independently chosen conductor and height
cutoffs whenever both fit below a common endpoint.
-/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_le_diagonal (Q T n : ℕ) (σ : ℝ) (hσ : σ ≤ 1)
    (hQT : Q ≤ T) (hnT : n ≤ T) :
    primitiveCharacterFamilyZeroCountAtNatHeight Q σ n ≤ primitiveCharacterFamilyZeroCount T σ := by
  classical
  let e : Fin Q ↪ Fin T := Fin.castLEEmb hQT
  let f : Fin T → ℝ := fun j =>
    ∑ χ : DirichletCharacter ℂ (j.val + 1),
      if hχ : χ ≠ 1 then if hprim : χ.IsPrimitive then completedZeroCountAtNatHeight χ hχ σ T else 0
      else 0
  have hterm (j : Fin Q) :
    (∑ χ : DirichletCharacter ℂ (j.val + 1),
        if hχ : χ ≠ 1 then
          if hprim : χ.IsPrimitive then completedZeroCountAtNatHeight χ hχ σ n else 0
        else 0) ≤
      f (e j) := by
    dsimp only [f]
    have hjval : (e j).val = j.val := Fin.val_castLE hQT j
    rw [hjval]
    apply Finset.sum_le_sum
    intro χ hχmem
    split_ifs with hχ hprim
    · exact completedZeroCountAtNatHeight_mono χ hχ hσ hnT
    · exact le_rfl
    · exact le_rfl
  unfold primitiveCharacterFamilyZeroCountAtNatHeight
  change
    (∑ j : Fin Q,
        ∑ χ : DirichletCharacter ℂ (j.val + 1),
          if hχ : χ ≠ 1 then
            if hprim : χ.IsPrimitive then completedZeroCountAtNatHeight χ hχ σ n else 0
          else 0) ≤
      ∑ j : Fin T,
        ∑ χ : DirichletCharacter ℂ (j.val + 1),
          if hχ : χ ≠ 1 then
            if hprim : χ.IsPrimitive then completedZeroCountAtNatHeight χ hχ σ T else 0
          else 0
  calc
    _ ≤ ∑ j : Fin Q, f (e j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hterm j
    _ = ∑ j ∈ Finset.univ.map e, f j := by rw [← Finset.sum_map]
    _ ≤ ∑ j : Fin T, f j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_univ j
      · intro j hj hnot
        dsimp only [f]
        apply Finset.sum_nonneg
        intro χ hχmem
        split_ifs with hχ hprim
        · exact completedZeroCountAtNatHeight_nonneg χ hχ σ T
        · exact le_of_eq rfl
        · exact le_of_eq rfl

/-- Summation by parts for the primitive-character family with independent cutoffs. -/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_partial_summation_le (Q : ℕ) (σ : ℝ) (T : ℕ)
    (hT : 1 ≤ T) :
    (∑ k ∈ Finset.range T,
        (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (k + 1) -
            primitiveCharacterFamilyZeroCountAtNatHeight Q σ k) /
          (k + 1 : ℝ)) ≤
      primitiveCharacterFamilyZeroCountAtNatHeight Q σ T / (T : ℝ) +
        ∑ k ∈ Finset.range T,
          primitiveCharacterFamilyZeroCountAtNatHeight Q σ (k + 1) / (k + 1 : ℝ) ^ 2 := by
  exact
    finite_sum_differences_div_succ_le (fun n => primitiveCharacterFamilyZeroCountAtNatHeight Q σ n)
      T hT (fun n => primitiveCharacterFamilyZeroCountAtNatHeight_nonneg Q σ n)

/--
Inputs: a fixed conductor cutoff, a real-part threshold at most one, a nonnegative constant, and
a dyadic endpoint bound for the separated primitive-family zero count.

Claim: the finite inverse-height weighted sum of zero counts in dyadic height bands is at most
eight times the constant.

Proof: use height monotonicity to bound each band by its upper endpoint, then apply the geometric
dyadic summation estimate.

Role: aggregates zeros in height while keeping the conductor cutoff fixed.
-/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_dyadic_inverse_height_sum_le_eight (Q : ℕ)
    (σ C : ℝ) (hσ : σ ≤ 1) (hC : 0 ≤ C) (J : ℕ)
    (hdensity :
      ∀ j < J,
        primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) ≤ 2 * C * (3 / 2 : ℝ) ^ j) :
    (∑ j ∈ Finset.range J,
        (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) -
            primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ j)) *
          (1 / 2 : ℝ) ^ j) ≤
      8 * C := by
  apply finite_dyadic_inverse_height_sum_le_eight J C hC
  intro j hj
  have hscale : 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ j)
  have hmono := primitiveCharacterFamilyZeroCountAtNatHeight_mono Q hσ hscale
  have hnonneg := primitiveCharacterFamilyZeroCountAtNatHeight_nonneg Q σ (2 ^ j)
  exact le_trans (sub_le_self _ hnonneg) (hdensity j hj)

/--
Inputs: a fixed conductor cutoff, a density constant, an exponent at most one half, and a power
bound for the cumulative count at dyadic height endpoints.

Claim: the finite inverse-height weighted sum over dyadic height bands is at most eight times the
density constant.

Proof: convert the power bound to the geometric endpoint estimate and apply the fixed-cutoff
dyadic summation theorem.

Role: gives the fixed-conductor version of the height aggregation step under a prospective density
estimate.
-/
theorem
  primitiveCharacterFamilyZeroCountAtNatHeight_dyadic_inverse_height_sum_le_eight_of_rpow_density
    (Q : ℕ) (σ C δ : ℝ) (hσ : σ ≤ 1) (hC : 0 ≤ C) (hδ : δ ≤ 1 / 2) (J : ℕ)
    (hdensity :
      ∀ j < J,
        primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) ≤
          C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ) :
    (∑ j ∈ Finset.range J,
        (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) -
            primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ j)) *
          (1 / 2 : ℝ) ^ j) ≤
      8 * C := by
  apply
    primitiveCharacterFamilyZeroCountAtNatHeight_dyadic_inverse_height_sum_le_eight Q σ C hσ hC J
  intro j hj
  calc
    primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) ≤
        C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ :=
      hdensity j hj
    _ = C * Real.rpow 2 (δ * ((j + 1 : ℕ) : ℝ)) := by rw [dyadic_height_rpow_eq]
    _ ≤ 2 * C * (3 / 2 : ℝ) ^ j := by
      calc
        C * Real.rpow 2 (δ * ((j + 1 : ℕ) : ℝ)) ≤ C * (2 * (3 / 2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left (dyadic_rpow_le_two_mul_three_halves δ hδ j) hC
        _ = 2 * C * (3 / 2 : ℝ) ^ j := by ring

/-- The fixed-cutoff dyadic inverse-height estimate under a log-free density bound. -/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_dyadic_sum_le_eight_of_log_free_density (Q : ℕ)
    (A σ C : ℝ) (hσ : σ ≤ 1) (hδ : A * (1 - σ) ≤ 1 / 2) (hC : 0 ≤ C) (J : ℕ)
    (hdensity :
      ∀ j < J,
        primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) ≤
          C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) (A * (1 - σ))) :
    (∑ j ∈ Finset.range J,
        (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) -
            primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ j)) *
          (1 / 2 : ℝ) ^ j) ≤
      8 * C := by
  exact
    primitiveCharacterFamilyZeroCountAtNatHeight_dyadic_inverse_height_sum_le_eight_of_rpow_density
      Q σ C (A * (1 - σ)) hσ hC hδ J hdensity

/-!
The next estimate separates a fixed conductor cutoff from the height in the diagonal family
density bound. Its conductor loss is explicit and polynomial in `Q`.
-/

/--
Inputs: a fixed conductor cutoff, a height at least two, a nonnegative density exponent, and a
diagonal family density estimate.

Claim: the separated family zero count is bounded by the density constant times the height to the
exponent and the conductor factor `(Q + 1)^δ`.

Proof: enlarge both cutoffs to `max Q n`, bound this by `(Q + 1) * n`, and apply monotonicity and
multiplicativity of real powers for a nonnegative exponent.

Role: supplies the fixed-cutoff input for dyadic height summation directly from the diagonal family
density theorem.
-/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_le_rpow_of_diagonal_rpow_density (Q n : ℕ)
    (σ C δ : ℝ) (hσ : σ ≤ 1) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hn2 : 2 ≤ n)
    (hdensity : ∀ T : ℕ, 2 ≤ T → primitiveCharacterFamilyZeroCount T σ ≤ C * Real.rpow (T : ℝ) δ) :
    primitiveCharacterFamilyZeroCountAtNatHeight Q σ n ≤
      (C * Real.rpow ((Q + 1 : ℕ) : ℝ) δ) * Real.rpow (n : ℝ) δ := by
  let T : ℕ := max Q n
  have hT2 : 2 ≤ T := by
    dsimp only [T]
    exact le_trans hn2 (Nat.le_max_right Q n)
  have hQT : Q ≤ T := by
    dsimp only [T]
    exact Nat.le_max_left Q n
  have hnT : n ≤ T := by
    dsimp only [T]
    exact Nat.le_max_right Q n
  have hn1 : 1 ≤ n := le_trans (by norm_num only : (1 : ℕ) ≤ 2) hn2
  have hTbound : T ≤ (Q + 1) * n := by
    dsimp only [T]
    apply max_le
    · calc
        Q ≤ Q * n := Nat.le_mul_of_pos_right Q hn1
        _ ≤ (Q + 1) * n := Nat.mul_le_mul_right n (Nat.le_succ Q)
    · calc
        n ≤ n * (Q + 1) := Nat.le_mul_of_pos_right n (Nat.succ_pos Q)
        _ = (Q + 1) * n := Nat.mul_comm _ _
  have hTboundReal : (T : ℝ) ≤ (((Q + 1) * n : ℕ) : ℝ) := by exact_mod_cast hTbound
  have hpow : Real.rpow (T : ℝ) δ ≤ Real.rpow ((Q + 1 : ℕ) : ℝ) δ * Real.rpow (n : ℝ) δ := by
    calc
      Real.rpow (T : ℝ) δ ≤ Real.rpow (((Q + 1) * n : ℕ) : ℝ) δ :=
        Real.rpow_le_rpow (by exact_mod_cast Nat.zero_le T) hTboundReal hδ
      _ = Real.rpow (((Q + 1 : ℕ) : ℝ) * (n : ℝ)) δ := by rw [Nat.cast_mul]
      _ = Real.rpow ((Q + 1 : ℕ) : ℝ) δ * Real.rpow (n : ℝ) δ :=
        Real.mul_rpow (by exact_mod_cast Nat.zero_le (Q + 1)) (by exact_mod_cast Nat.zero_le n)
  have hdiagonal := primitiveCharacterFamilyZeroCountAtNatHeight_le_diagonal Q T n σ hσ hQT hnT
  calc
    primitiveCharacterFamilyZeroCountAtNatHeight Q σ n ≤ primitiveCharacterFamilyZeroCount T σ := by
      simpa only [T] using hdiagonal
    _ ≤ C * Real.rpow (T : ℝ) δ := hdensity T hT2
    _ ≤ C * (Real.rpow ((Q + 1 : ℕ) : ℝ) δ * Real.rpow (n : ℝ) δ) :=
      mul_le_mul_of_nonneg_left hpow hC
    _ = (C * Real.rpow ((Q + 1 : ℕ) : ℝ) δ) * Real.rpow (n : ℝ) δ := by ring

/--
Inputs: a conductor cutoff, an exponent at most one half, and a diagonal family density bound.

Claim: the inverse-height dyadic zero sum for the fixed conductor cutoff is bounded by the density
constant multiplied by the conductor factor `(Q + 1)^δ`.

Proof: for each dyadic height `n`, enlarge the family cutoff to `max Q n`, apply the diagonal
density estimate, and dominate this cutoff by `(Q + 1) * n`. Then use the fixed-cutoff dyadic
summation bound.

Role: converts the joint conductor-height density interface into the separated-height estimate
used when summing explicit-formula zero contributions.
-/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_dyadic_sum_le_eight_of_diagonal_rpow_density
    (Q J : ℕ) (σ C δ : ℝ) (hσ : σ ≤ 1) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hdensity : ∀ T : ℕ, 2 ≤ T → primitiveCharacterFamilyZeroCount T σ ≤ C * Real.rpow (T : ℝ) δ) :
    (∑ j ∈ Finset.range J,
        (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) -
            primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ j)) *
          (1 / 2 : ℝ) ^ j) ≤
      8 * (C * Real.rpow ((Q + 1 : ℕ) : ℝ) δ) := by
  let C' : ℝ := C * Real.rpow ((Q + 1 : ℕ) : ℝ) δ
  have hC' : 0 ≤ C' := by
    dsimp only [C']
    exact mul_nonneg hC (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le (Q + 1)) _)
  have hdensityQ :
    ∀ j < J,
      primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) ≤
        C' * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ := by
    intro j hj
    have hcount :=
      primitiveCharacterFamilyZeroCountAtNatHeight_le_rpow_of_diagonal_rpow_density Q (2 ^ (j + 1))
        σ C δ hσ hC hδ (Nat.le_pow (Nat.succ_pos j)) hdensity
    simpa only [C'] using hcount
  have hsum :=
    primitiveCharacterFamilyZeroCountAtNatHeight_dyadic_inverse_height_sum_le_eight_of_rpow_density
      Q σ C' δ hσ hC' hδhalf J hdensityQ
  simpa only [C'] using hsum

/--
Inputs: a fixed conductor cutoff, a density exponent at most one half, and power bounds for the
fixed-cutoff zero counts at all dyadic heights.

Claim: the inverse-height weighted sum over every dyadic height band is bounded by eight times the
density constant.

Proof: dominate each band by a constant multiple of `(3/4)^j`, establish summability of the band
series, and compare its sum with the geometric majorant.

Role: is the infinite-height counterpart of the finite fixed-cutoff summation estimate.
-/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_tsum_inverse_height_le_eight_of_rpow_density
    (Q : ℕ) (σ C δ : ℝ) (hσ : σ ≤ 1) (hC : 0 ≤ C) (hδ : δ ≤ 1 / 2)
    (hdensity :
      ∀ j : ℕ,
        primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) ≤
          C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ) :
    ∑' j : ℕ,
        (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) -
            primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ j)) *
          (1 / 2 : ℝ) ^ j ≤
      8 * C := by
  let f : ℕ → ℝ := fun j =>
    (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) -
        primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ j)) *
      (1 / 2 : ℝ) ^ j
  let g : ℕ → ℝ := fun j => 2 * C * (3 / 4 : ℝ) ^ j
  have hle : ∀ j, f j ≤ g j := by
    intro j
    dsimp only [f, g]
    have hlow := primitiveCharacterFamilyZeroCountAtNatHeight_nonneg Q σ (2 ^ j)
    have hband := sub_le_self (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1))) hlow
    calc
      _ ≤ (C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ) * (1 / 2 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_right (le_trans hband (hdensity j))
          (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) j)
      _ = C * Real.rpow 2 (δ * ((j + 1 : ℕ) : ℝ)) * (1 / 2 : ℝ) ^ j := by rw [dyadic_height_rpow_eq]
      _ ≤ (C * (2 * (3 / 2 : ℝ) ^ j)) * (1 / 2 : ℝ) ^ j := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (dyadic_rpow_le_two_mul_three_halves δ hδ j) hC
        · exact pow_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) j
      _ = 2 * C * (3 / 4 : ℝ) ^ j := by
        calc
          _ = (2 * C * (3 / 2 : ℝ) ^ j) * (1 / 2 : ℝ) ^ j := by ring
          _ = 2 * C * (3 / 4 : ℝ) ^ j := by
            rw [mul_assoc, ← mul_pow]
            norm_num only
  have hg : Summable g := by
    dsimp only [g]
    exact
      (summable_geometric_of_lt_one (by norm_num only : (0 : ℝ) ≤ 3 / 4)
            (by norm_num only : (3 / 4 : ℝ) < 1)).mul_left
        (2 * C)
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le
    · intro j
      dsimp only [f]
      have hscale : 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ j)
      have hmono := primitiveCharacterFamilyZeroCountAtNatHeight_mono Q hσ hscale
      have hband :
        0 ≤
          primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) -
            primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ j) :=
        sub_nonneg.mpr hmono
      exact mul_nonneg hband (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) j)
    · exact hle
    · exact hg
  have htsum := Summable.tsum_le_tsum hle hf hg
  calc
    _ = ∑' j, f j := by rfl
    _ ≤ ∑' j, g j := htsum
    _ = (2 * C) * (1 - (3 / 4 : ℝ))⁻¹ := by
      dsimp only [g]
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one (by norm_num only : (0 : ℝ) ≤ 3 / 4)
          (by norm_num only : (3 / 4 : ℝ) < 1)]
    _ = 8 * C := by ring

/--
Inputs: a fixed conductor cutoff and a diagonal log-free family density estimate with exponent at
most one half.

Claim: the full inverse-height dyadic sum for that conductor cutoff is bounded by eight times the
density constant and the conductor factor `(Q + 1)^δ`.

Proof: transfer each fixed-cutoff endpoint count to the diagonal cutoff `max Q n`, apply the
polynomial cutoff comparison, and invoke the infinite dyadic summation estimate.

Role: connects a diagonal family density theorem to the all-height zero sum for any fixed modulus
range.
-/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_tsum_le_eight_of_diagonal_density (Q : ℕ)
    (σ C δ : ℝ) (hσ : σ ≤ 1) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hdensity : ∀ T : ℕ, 2 ≤ T → primitiveCharacterFamilyZeroCount T σ ≤ C * Real.rpow (T : ℝ) δ) :
    ∑' j : ℕ,
        (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) -
            primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ j)) *
          (1 / 2 : ℝ) ^ j ≤
      8 * (C * Real.rpow ((Q + 1 : ℕ) : ℝ) δ) := by
  let C' : ℝ := C * Real.rpow ((Q + 1 : ℕ) : ℝ) δ
  have hC' : 0 ≤ C' := by
    dsimp only [C']
    exact mul_nonneg hC (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le (Q + 1)) _)
  have hdensityQ :
    ∀ j : ℕ,
      primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) ≤
        C' * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ := by
    intro j
    have hcount :=
      primitiveCharacterFamilyZeroCountAtNatHeight_le_rpow_of_diagonal_rpow_density Q (2 ^ (j + 1))
        σ C δ hσ hC hδ (Nat.le_pow (Nat.succ_pos j)) hdensity
    simpa only [C'] using hcount
  have hsum :=
    primitiveCharacterFamilyZeroCountAtNatHeight_tsum_inverse_height_le_eight_of_rpow_density Q σ C'
      δ hσ hC' hδhalf hdensityQ
  simpa only [C'] using hsum

/--
Inputs: a fixed conductor cutoff, a density exponent at most one, and a dyadic endpoint bound for
the separated zero count.

Claim: the finite inverse-height sum is at most twice the density constant times the number of
dyadic bands.

Proof: since `δ ≤ 1`, each endpoint power is at most the endpoint height. After multiplication by
the inverse-height weight, each band contributes at most `2*C`.

Role: gives the logarithmic-in-height bound used for the intermediate real-part range of a
log-free density argument.
-/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_dyadic_sum_le_two_mul_of_rpow_density (Q J : ℕ)
    (σ C δ : ℝ) (hC : 0 ≤ C) (hδ : δ ≤ 1)
    (hdensity :
      ∀ j < J,
        primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) ≤
          C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ) :
    (∑ j ∈ Finset.range J,
        (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) -
            primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ j)) *
          (1 / 2 : ℝ) ^ j) ≤
      2 * C * J := by
  have hconst : (∑ j ∈ Finset.range J, (2 * C : ℝ)) = 2 * C * J := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  calc
    _ ≤ ∑ j ∈ Finset.range J, (2 * C : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hlow := primitiveCharacterFamilyZeroCountAtNatHeight_nonneg Q σ (2 ^ j)
      have hband :=
        sub_le_self (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1))) hlow
      have hpower : Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ ≤ (2 ^ (j + 1) : ℕ) := by
        calc
          Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ = Real.rpow 2 (δ * ((j + 1 : ℕ) : ℝ)) :=
            dyadic_height_rpow_eq δ j
          _ ≤ Real.rpow 2 (1 * ((j + 1 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num only)
              (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg (j + 1)))
          _ = Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) 1 := (dyadic_height_rpow_eq 1 j).symm
          _ = (2 ^ (j + 1) : ℕ) := Real.rpow_one _
      have hcount :
        primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) ≤ C * (2 ^ (j + 1) : ℕ) := by
        calc
          _ ≤ C * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ := hdensity j (Finset.mem_range.mp hj)
          _ ≤ C * (2 ^ (j + 1) : ℕ) := mul_le_mul_of_nonneg_left hpower hC
      calc
        _ ≤ (C * (2 ^ (j + 1) : ℕ)) * (1 / 2 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right (le_trans hband hcount)
            (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) j)
        _ = 2 * C := by
          rw [Nat.cast_pow, pow_succ]
          calc
            _ = 2 * C * ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j) := by ring
            _ = 2 * C * ((2 : ℝ) * (1 / 2 : ℝ)) ^ j := by rw [← mul_pow]
            _ = 2 * C := by norm_num only [one_pow, mul_one]
    _ = 2 * C * J := hconst

/-- The finite logarithmic height bound under a diagonal density estimate. -/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_dyadic_sum_le_two_mul_of_diagonal_density
    (Q J : ℕ) (σ C δ : ℝ) (hσ : σ ≤ 1) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hdensity : ∀ T : ℕ, 2 ≤ T → primitiveCharacterFamilyZeroCount T σ ≤ C * Real.rpow (T : ℝ) δ) :
    (∑ j ∈ Finset.range J,
        (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) -
            primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ j)) *
          (1 / 2 : ℝ) ^ j) ≤
      2 * (C * Real.rpow ((Q + 1 : ℕ) : ℝ) δ) * J := by
  let C' : ℝ := C * Real.rpow ((Q + 1 : ℕ) : ℝ) δ
  have hC' : 0 ≤ C' := by
    dsimp only [C']
    exact mul_nonneg hC (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le (Q + 1)) _)
  have hdensityQ :
    ∀ j < J,
      primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) ≤
        C' * Real.rpow ((2 ^ (j + 1) : ℕ) : ℝ) δ := by
    intro j hj
    have hcount :=
      primitiveCharacterFamilyZeroCountAtNatHeight_le_rpow_of_diagonal_rpow_density Q (2 ^ (j + 1))
        σ C δ hσ hC hδ (Nat.le_pow (Nat.succ_pos j)) hdensity
    simpa only [C'] using hcount
  have hsum :=
    primitiveCharacterFamilyZeroCountAtNatHeight_dyadic_sum_le_two_mul_of_rpow_density Q J σ C' δ
      hC' hδone hdensityQ
  simpa only [C'] using hsum

/--
Inputs: a nonnegative exponent parameter `A`, a threshold `σ ≤ 1`, and a diagonal density estimate
with exponent `A * (1 - σ) ≤ 1`.

Claim: the finite inverse-height sum for a fixed conductor cutoff is at most
`2*C*(Q+1)^(A*(1-σ))*J` over `J` dyadic bands.

Proof: apply the diagonal-density transfer with `δ = A*(1-σ)` and use `A ≥ 0`, `σ ≤ 1` to verify
the nonnegative-exponent condition.

Role: gives the intermediate real-part range estimate in the parameters used by the log-free
family density theorem.
-/
theorem primitiveCharacterFamilyZeroCountAtNatHeight_dyadic_sum_le_two_mul_of_log_free_density
    (Q J : ℕ) (A σ C : ℝ) (hA : 0 ≤ A) (hσ : σ ≤ 1) (hC : 0 ≤ C) (hδone : A * (1 - σ) ≤ 1)
    (hdensity :
      ∀ T : ℕ,
        2 ≤ T → primitiveCharacterFamilyZeroCount T σ ≤ C * Real.rpow (T : ℝ) (A * (1 - σ))) :
    (∑ j ∈ Finset.range J,
        (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) -
            primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ j)) *
          (1 / 2 : ℝ) ^ j) ≤
      2 * (C * Real.rpow ((Q + 1 : ℕ) : ℝ) (A * (1 - σ))) * J := by
  have hδnonneg : 0 ≤ A * (1 - σ) := mul_nonneg hA (sub_nonneg.mpr hσ)
  exact
    primitiveCharacterFamilyZeroCountAtNatHeight_dyadic_sum_le_two_mul_of_diagonal_density Q J σ C
      (A * (1 - σ)) hσ hC hδnonneg hδone hdensity

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
