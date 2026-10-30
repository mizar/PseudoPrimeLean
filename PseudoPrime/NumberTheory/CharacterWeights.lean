/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.SubgroupAnnihilator
public import PseudoPrime.NumberTheory.DirichletCharacter
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Finite character weights and exact conductor sums -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Sum the real weights over a finite family of ambient Dirichlet characters.
Nonnegative weights make this total nonnegative; it is the identity value
of the weighted character trace for annihilator families. -/
noncomputable def characterWeightTotal {q : ℕ} (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℝ) : ℝ :=
  ∑ χ ∈ S, w χ

/-- Evaluate the finite real weighted character trace at an ambient residue.
The weights are real and need not be normalized. For nonnegative weights
its upper bound is their total, while a sharper lower bound is supplied separately. -/
noncomputable def weightedCharacterTrace {q : ℕ} (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℝ) (z : ZMod q) : ℝ :=
  ∑ χ ∈ S, w χ * (χ z).re

/-- Nonnegative weights have nonnegative total. Sum their pointwise signs.
This supplies the elementary weight budget for later trace comparisons. -/
theorem characterWeightTotal_nonneg {q : ℕ} {S : Finset (DirichletCharacter ℂ q)}
    {w : DirichletCharacter ℂ q → ℝ} (hw : ∀ χ ∈ S, 0 ≤ w χ) : 0 ≤ characterWeightTotal S w := by
  exact Finset.sum_nonneg hw

/-- The real weighted trace never exceeds the total of nonnegative weights.
Bound each character's real part by its norm and then by one. -/
theorem weightedCharacterTrace_le_total {q : ℕ} {S : Finset (DirichletCharacter ℂ q)}
    {w : DirichletCharacter ℂ q → ℝ} (hw : ∀ χ ∈ S, 0 ≤ w χ) (z : ZMod q) :
    weightedCharacterTrace S w z ≤ characterWeightTotal S w := by
  apply Finset.sum_le_sum
  intro χ hχ
  exact
    mul_le_of_le_one_right (hw χ hχ)
      ((Complex.re_le_norm (χ z)).trans (DirichletCharacter.norm_le_one χ z))

/-- The real weighted trace is at least minus the total of nonnegative weights.
Use the absolute real-part bound. Concrete quotient certificates can replace
this coarse lower bound by a smaller negative penalty. -/
theorem neg_total_le_weightedCharacterTrace {q : ℕ} {S : Finset (DirichletCharacter ℂ q)}
    {w : DirichletCharacter ℂ q → ℝ} (hw : ∀ χ ∈ S, 0 ≤ w χ) (z : ZMod q) :
    -characterWeightTotal S w ≤ weightedCharacterTrace S w z := by
  rw [characterWeightTotal, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro χ hχ
  have he :=
    (abs_le.mp ((Complex.abs_re_le_norm (χ z)).trans (DirichletCharacter.norm_le_one χ z))).1
  have hm := mul_le_mul_of_nonneg_left he (hw χ hχ)
  simpa only [mul_neg, mul_one] using hm

/-- Sum weight times log primitive conductor over a finite ambient character
family. The weights are retained individually, rather than replaced by their
total or the ambient logarithm. This is the analytic budget in the weighted criterion. -/
noncomputable def weightedConductorLogSum {q : ℕ} (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℝ) : ℝ :=
  ∑ χ ∈ S, w χ * Real.log χ.conductor

/-- Give two quadratic characters equal weight (1-t)/2 and their product
weight t, with zero weight elsewhere. Distinctness assumptions in consumers
ensure these are three separate terms. For 0<=t<=1 the weights are nonnegative. -/
noncomputable def quadraticPairWeight {q : ℕ} (a b : DirichletCharacter ℂ q) (t : ℝ)
    (χ : DirichletCharacter ℂ q) : ℝ := by
  classical
    exact if χ = a then (1 - t) / 2 else if χ = b then (1 - t) / 2 else if χ = a * b then t else 0

/-- For t between zero and one, every weight in the three-character profile
is nonnegative. Split its three explicit branches. This supplies the analytic
weighted-conductor upper bound without assuming equal character conductors. -/
theorem quadraticPairWeight_nonneg {q : ℕ} (a b : DirichletCharacter ℂ q) {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t ≤ 1) (χ : DirichletCharacter ℂ q) : 0 ≤ quadraticPairWeight a b t χ := by
  classical
  dsimp only [quadraticPairWeight]
  split_ifs
  · exact div_nonneg (sub_nonneg.mpr ht1) (by norm_num only)
  · exact div_nonneg (sub_nonneg.mpr ht1) (by norm_num only)
  · exact ht
  · exact le_refl 0

/-- When a, b and a*b are distinct, the three selected weights have their
stated values. Resolve the finite profile branches explicitly for later sums. -/
theorem quadraticPairWeight_values {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha : a ≠ a * b) (hb : b ≠ a * b) (t : ℝ) :
    quadraticPairWeight a b t a = (1 - t) / 2 ∧
      quadraticPairWeight a b t b = (1 - t) / 2 ∧ quadraticPairWeight a b t (a * b) = t := by
  classical
    simp only [quadraticPairWeight, ite_true, and_self, ite_eq_right (Ne.symm hab),
    ite_eq_right (Ne.symm ha), ite_eq_right (Ne.symm hb)]

/-- The finite character family consisting of a, b and a*b.
Consumers assert their distinctness when normalizing its weights.
This small quotient-level family requires no enumeration of ambient inputs. -/
noncomputable def quadraticTriple {q : ℕ} (a b : DirichletCharacter ℂ q) :
    Finset (DirichletCharacter ℂ q) := by classical exact {a, b, a * b}

/-- For three distinct selected characters, expand the weighted trace into
its three explicit real character values. This identifies the profile before
checking the four possible quadratic unit-value patterns. -/
theorem quadraticPairTrace_eq {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b) (ha : a ≠ a * b)
    (hb : b ≠ a * b) (t : ℝ) (z : ZMod q) :
    weightedCharacterTrace (quadraticTriple a b) (quadraticPairWeight a b t) z =
      (1 - t) / 2 * (a z).re + (1 - t) / 2 * (b z).re + t * ((a * b) z).re := by
  classical
  have hA : a ∉ ({b, a * b} : Finset (DirichletCharacter ℂ q)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, hab, ha, or_self, not_false_eq_true]
  have hB : b ∉ ({a * b} : Finset (DirichletCharacter ℂ q)) := by
    simpa only [Finset.mem_singleton] using hb
  have hv := quadraticPairWeight_values a b hab ha hb t
  rw [weightedCharacterTrace, quadraticTriple, Finset.sum_insert hA, Finset.sum_insert hB,
    Finset.sum_singleton, hv.1, hv.2.1, hv.2.2]
  ring

/-- For quadratic a and b and nonnegative t, the three-character trace is
at least minus max(t,1-2*t). At units inspect the four sign patterns; at
nonunits every character vanishes. This is a proved global trace certificate. -/
theorem quadraticPairTrace_lower {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha : a ≠ a * b) (hb : b ≠ a * b) (hqa : a.IsQuadratic) (hqb : b.IsQuadratic) {t : ℝ}
    (ht : 0 ≤ t) (z : ZMod q) :
    -max t (1 - 2 * t) ≤
      weightedCharacterTrace (quadraticTriple a b) (quadraticPairWeight a b t) z := by
  classical
  have hm₁ := le_max_left t (1 - 2 * t)
  have hm₂ := le_max_right t (1 - 2 * t)
  rw [quadraticPairTrace_eq a b hab ha hb]
  by_cases hu : IsUnit z
  · rcases hqa z with ha0 | ha1 | han
    · exact False.elim ((MulChar.apply_ne_zero_iff.mpr hu) ha0)
    · rcases hqb z with hb0 | hb1 | hbn
      · exact False.elim ((MulChar.apply_ne_zero_iff.mpr hu) hb0)
      · rw [MulChar.mul_apply, ha1, hb1]
        norm_num only [one_mul, Complex.one_re]
        linarith only [ht, hm₁]
      · rw [MulChar.mul_apply, ha1, hbn]
        norm_num only [one_mul, Complex.one_re, Complex.neg_re]
        linarith only [hm₁]
    · rcases hqb z with hb0 | hb1 | hbn
      · exact False.elim ((MulChar.apply_ne_zero_iff.mpr hu) hb0)
      · rw [MulChar.mul_apply, han, hb1]
        norm_num only [mul_one, Complex.one_re, Complex.neg_re]
        linarith only [hm₁]
      · rw [MulChar.mul_apply, han, hbn]
        norm_num only [neg_mul_neg, one_mul, Complex.one_re, Complex.neg_re]
        linarith only [hm₂]
  · rw [MulChar.map_nonunit a hu, MulChar.map_nonunit b hu, MulChar.map_nonunit (a * b) hu]
    simp only [Complex.zero_re, mul_zero, add_zero]
    linarith only [ht, hm₁]

/-- For three distinct selected characters, the profile weights sum to one.
Expand the three terms and cancel their affine coefficients. This normalizes
the analytic allowance independently of t and the ambient modulus. -/
theorem quadraticPairWeight_total {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha : a ≠ a * b) (hb : b ≠ a * b) (t : ℝ) :
    characterWeightTotal (quadraticTriple a b) (quadraticPairWeight a b t) = 1 := by
  classical
  have hA : a ∉ ({b, a * b} : Finset (DirichletCharacter ℂ q)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, hab, ha, or_self, not_false_eq_true]
  have hB : b ∉ ({a * b} : Finset (DirichletCharacter ℂ q)) := by
    simpa only [Finset.mem_singleton] using hb
  have hv := quadraticPairWeight_values a b hab ha hb t
  rw [characterWeightTotal, quadraticTriple, Finset.sum_insert hA, Finset.sum_insert hB,
    Finset.sum_singleton, hv.1, hv.2.1, hv.2.2]
  ring

/-- Retain the exact weighted primitive-conductor logarithms of the three
selected characters. Expand the finite sum without replacing the individual
conductors by the ambient level or an unweighted average. -/
theorem quadraticPairWeight_cost {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha : a ≠ a * b) (hb : b ≠ a * b) (t : ℝ) :
    weightedConductorLogSum (quadraticTriple a b) (quadraticPairWeight a b t) =
      (1 - t) / 2 * Real.log a.conductor + (1 - t) / 2 * Real.log b.conductor +
        t * Real.log (a * b).conductor := by
  classical
  have hA : a ∉ ({b, a * b} : Finset (DirichletCharacter ℂ q)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, hab, ha, or_self, not_false_eq_true]
  have hB : b ∉ ({a * b} : Finset (DirichletCharacter ℂ q)) := by
    simpa only [Finset.mem_singleton] using hb
  have hv := quadraticPairWeight_values a b hab ha hb t
  rw [weightedConductorLogSum, quadraticTriple, Finset.sum_insert hA, Finset.sum_insert hB,
    Finset.sum_singleton, hv.1, hv.2.1, hv.2.2]
  ring

/-- If a and b annihilate H, all three selected characters annihilate H.
Use multiplicative closure of the annihilator for a*b. This connects the
concrete finite weight profile to the actual prime-comparison theorem. -/
theorem quadraticTriple_annihilates {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (a b : DirichletCharacter ℂ q) (ha : a ∈ subgroupAnnihilator H)
    (hb : b ∈ subgroupAnnihilator H) : ∀ χ ∈ quadraticTriple a b, χ ∈ subgroupAnnihilator H := by
  classical
  intro χ hχ
  simp only [quadraticTriple, Finset.mem_insert, Finset.mem_singleton] at hχ
  rcases hχ with h | h | h
  · exact h ▸ ha
  · exact h ▸ hb
  · exact h ▸ (subgroupAnnihilator H).mul_mem ha hb

/-- For distinct characters with coprime conductors at a nonzero ambient level,
the weighted conductor logarithm is (1+t)/2 times the two conductor logs.
Use exact multiplicativity of conductor and the logarithm of a positive product. -/
theorem quadraticPairWeight_cost_coprime {q : ℕ} [NeZero q] (a b : DirichletCharacter ℂ q)
    (hab : a ≠ b) (ha : a ≠ a * b) (hb : b ≠ a * b) (hc : Nat.Coprime a.conductor b.conductor)
    (t : ℝ) :
    weightedConductorLogSum (quadraticTriple a b) (quadraticPairWeight a b t) =
      (1 + t) / 2 * (Real.log a.conductor + Real.log b.conductor) := by
  rw [quadraticPairWeight_cost a b hab ha hb, conductor_mul_of_coprime a b hc, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr a.conductor_ne_zero)
      (Nat.cast_ne_zero.mpr b.conductor_ne_zero)]
  ring

end PseudoPrime.NumberTheory
