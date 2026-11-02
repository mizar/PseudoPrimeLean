/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.CharacterWeights

/-! # Arbitrary weights on a quadratic character triple

The finite character identities here allow arbitrary ambient moduli, weights and quadratic
characters. They do not choose a Mellin kernel, analytic scale, conductor allowance, or witness
coefficient. Concrete deficit comparisons and numerical choices belong to their application.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Assign arbitrary real weights to two characters and their product.
Input: characters and three weights; no analytic or primality assumptions are made.
Output: the selected weight, or zero away from the three-character family.
Role: finite character traces and conductor costs independent of any kernel choice. -/
noncomputable def quadraticTripleWeight {q : ℕ} (a b : DirichletCharacter ℂ q) (wa wb wc : ℝ)
    (χ : DirichletCharacter ℂ q) : ℝ :=
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  if χ = a then wa else if χ = b then wb else if χ = a * b then wc else 0

/-- Distinct selected characters receive their prescribed weights.
Input: the three pairwise inequalities and arbitrary real weights.
Proof: evaluate the conditional branches. Role: expand finite weighted traces and costs. -/
theorem quadraticTripleWeight_values {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha : a ≠ a * b) (hb : b ≠ a * b) (wa wb wc : ℝ) :
    quadraticTripleWeight a b wa wb wc a = wa ∧
      quadraticTripleWeight a b wa wb wc b = wb ∧ quadraticTripleWeight a b wa wb wc (a * b) = wc :=
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  ⟨ite_eq_left rfl, (ite_eq_right hab.symm).trans (ite_eq_left rfl),
    (ite_eq_right ha.symm).trans ((ite_eq_right hb.symm).trans (ite_eq_left rfl))⟩

/-- Nonnegative input weights define nonnegative weights on every character.
Input: three nonnegative real weights. Claim: every assigned value is nonnegative.
Proof: evaluate the selected branch. Role: apply finite nonnegative character sums. -/
theorem quadraticTripleWeight_nonneg {q : ℕ} (a b : DirichletCharacter ℂ q) {wa wb wc : ℝ}
    (hwa : 0 ≤ wa) (hwb : 0 ≤ wb) (hwc : 0 ≤ wc) (χ : DirichletCharacter ℂ q) :
    0 ≤ quadraticTripleWeight a b wa wb wc χ :=
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  if ha : χ = a then (show quadraticTripleWeight a b wa wb wc χ = wa from ite_eq_left ha).symm ▸ hwa
  else
    if hb : χ = b then
      (show quadraticTripleWeight a b wa wb wc χ = wb from
            (ite_eq_right ha).trans (ite_eq_left hb)).symm ▸
        hwb
    else
      if hc : χ = a * b then
        (show quadraticTripleWeight a b wa wb wc χ = wc from
              (ite_eq_right ha).trans ((ite_eq_right hb).trans (ite_eq_left hc))).symm ▸
          hwc
      else
        (show quadraticTripleWeight a b wa wb wc χ = 0 from
              (ite_eq_right ha).trans ((ite_eq_right hb).trans (ite_eq_right hc))).symm ▸
          le_refl 0

/-- Expand a weighted three-character sum against an arbitrary real test function.
Input: three distinct selected characters, their real weights and a test function.
Claim: the finite sum is the three displayed terms. Proof: expand the finite set.
Role: share trace, total-weight and primitive-conductor identities. -/
theorem quadraticTripleWeight_sum {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha : a ≠ a * b) (hb : b ≠ a * b) (wa wb wc : ℝ) (f : DirichletCharacter ℂ q → ℝ) :
    (∑ χ ∈ quadraticTriple a b, quadraticTripleWeight a b wa wb wc χ * f χ) =
      wa * f a + wb * f b + wc * f (a * b) := by
  classical
  have hA : a ∉ ({b, a * b} : Finset (DirichletCharacter ℂ q)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, hab, ha, or_self, not_false_eq_true]
  have hB : b ∉ ({a * b} : Finset (DirichletCharacter ℂ q)) := by
    simpa only [Finset.mem_singleton] using hb
  have hv := quadraticTripleWeight_values a b hab ha hb wa wb wc
  rw [quadraticTriple, Finset.sum_insert hA, Finset.sum_insert hB, Finset.sum_singleton, hv.1,
    hv.2.1, hv.2.2, ← add_assoc]

/-- The three prescribed weights sum to their total.
Input: three distinct selected characters and arbitrary real weights.
Proof: specialize the finite sum to one. Role: normalize character-weight budgets. -/
theorem quadraticTripleWeight_total {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha : a ≠ a * b) (hb : b ≠ a * b) (wa wb wc : ℝ) :
    characterWeightTotal (quadraticTriple a b) (quadraticTripleWeight a b wa wb wc) =
      wa + wb + wc :=
  (show
        characterWeightTotal (quadraticTriple a b) (quadraticTripleWeight a b wa wb wc) =
          ∑ χ ∈ quadraticTriple a b, quadraticTripleWeight a b wa wb wc χ * (1 : ℝ)
        from Finset.sum_congr rfl (fun _χ _ ↦ (mul_one _).symm)).trans
    ((quadraticTripleWeight_sum a b hab ha hb wa wb wc (fun _ ↦ 1)).trans
      (congrArg₂ (· + ·) (congrArg₂ (· + ·) (mul_one wa) (mul_one wb)) (mul_one wc)))

/-- The exact primitive-conductor cost retains each character's own logarithm.
Input: three distinct selected characters and arbitrary real weights.
Proof: specialize the finite sum to conductor logarithms.
Role: compare conductor savings without replacing them by the ambient modulus. -/
theorem quadraticTripleWeight_cost {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha : a ≠ a * b) (hb : b ≠ a * b) (wa wb wc : ℝ) :
    weightedConductorLogSum (quadraticTriple a b) (quadraticTripleWeight a b wa wb wc) =
      wa * Real.log a.conductor + wb * Real.log b.conductor + wc * Real.log (a * b).conductor :=
  quadraticTripleWeight_sum a b hab ha hb wa wb wc (fun χ ↦ Real.log χ.conductor)

/-- The weighted real trace equals the three explicit character values.
Input: three distinct selected characters, arbitrary real weights and an ambient residue.
Proof: specialize the finite sum to real character values.
Role: certify trace penalties independently of analytic estimates. -/
theorem quadraticTripleTrace_eq {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha : a ≠ a * b) (hb : b ≠ a * b) (wa wb wc : ℝ) (z : ZMod q) :
    weightedCharacterTrace (quadraticTriple a b) (quadraticTripleWeight a b wa wb wc) z =
      wa * (a z).re + wb * (b z).re + wc * ((a * b) z).re :=
  quadraticTripleWeight_sum a b hab ha hb wa wb wc (fun χ ↦ (χ z).re)

/-- A nonnegative quadratic triple has trace penalty at most its total minus twice the minimum.
Input: quadratic characters, pairwise distinctness, nonnegative weights and any residue.
Claim: the displayed lower bound holds also at nonunits.
Proof: inspect the four quadratic sign patterns and use the minimum weight.
Role: provide the exact normalized trace penalty for weighted character criteria. -/
theorem quadraticTripleTrace_lower {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha : a ≠ a * b) (hb : b ≠ a * b) (hqa : a.IsQuadratic) (hqb : b.IsQuadratic) {wa wb wc : ℝ}
    (hwa : 0 ≤ wa) (hwb : 0 ≤ wb) (hwc : 0 ≤ wc) (z : ZMod q) :
    -(wa + wb + wc) + 2 * min wa (min wb wc) ≤
      weightedCharacterTrace (quadraticTriple a b) (quadraticTripleWeight a b wa wb wc) z := by
  classical
  have hma := min_le_left wa (min wb wc)
  have hmb := (min_le_right wa (min wb wc)).trans (min_le_left wb wc)
  have hmc := (min_le_right wa (min wb wc)).trans (min_le_right wb wc)
  rw [quadraticTripleTrace_eq a b hab ha hb]
  by_cases hu : IsUnit z
  · rcases hqa z with ha0 | ha1 | han
    · exact False.elim ((MulChar.apply_ne_zero_iff.mpr hu) ha0)
    · rcases hqb z with hb0 | hb1 | hbn
      · exact False.elim ((MulChar.apply_ne_zero_iff.mpr hu) hb0)
      · rw [MulChar.mul_apply, ha1, hb1]
        norm_num only [one_mul, Complex.one_re]
        linarith only [hma, hwb, hwc]
      · rw [MulChar.mul_apply, ha1, hbn]
        norm_num only [one_mul, Complex.one_re, Complex.neg_re]
        linarith only [hma]
    · rcases hqb z with hb0 | hb1 | hbn
      · exact False.elim ((MulChar.apply_ne_zero_iff.mpr hu) hb0)
      · rw [MulChar.mul_apply, han, hb1]
        norm_num only [mul_one, Complex.one_re, Complex.neg_re]
        linarith only [hmb]
      · rw [MulChar.mul_apply, han, hbn]
        norm_num only [neg_mul_neg, one_mul, Complex.one_re, Complex.neg_re]
        linarith only [hmc]
  · rw [MulChar.map_nonunit a hu, MulChar.map_nonunit b hu, MulChar.map_nonunit (a * b) hu]
    simp only [Complex.zero_re, mul_zero, add_zero]
    linarith only [hwa, hmb, hmc]

end PseudoPrime.NumberTheory
