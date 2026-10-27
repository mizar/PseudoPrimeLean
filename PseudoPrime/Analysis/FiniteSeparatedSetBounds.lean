/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # Cardinality bounds for separated finite sets -/

@[expose] public section

namespace PseudoPrime.Analysis.FiniteSeparatedSetBounds

/--
Inputs: a finite set of real points, an interval start and length, and a lower bound for the
distance between distinct points.

Claim: a half-open interval of that length contains at most one point from the set.

Proof: two distinct points in the interval would have distance strictly less than the interval
length, contradicting the separation hypothesis.

Role: bounds the number of frequencies in one side of a circular-distance shell.
-/
theorem finset_card_le_one_of_interval_separated (s : Finset ℝ) (a δ : ℝ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) (hinterval : ∀ x ∈ s, a ≤ x ∧ x < a + δ) :
    s.card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  have hdistance := hsep x hx y hy hxy
  obtain ⟨hxlo, hxhi⟩ := hinterval x hx
  obtain ⟨hylo, hyhi⟩ := hinterval y hy
  have hdiff : |x - y| < δ := by
    rw [abs_lt]
    constructor <;> linarith only [hxlo, hxhi, hylo, hyhi]
  exact (not_lt_of_ge hdistance) hdiff

/--
Inputs: a finite set of real points, an interval start and length, and a lower bound for the
distance between distinct points.

Claim: an interval open on the left and closed on the right contains at most one point from the
set.

Proof: two distinct points in the interval would have distance strictly less than its length,
contradicting the separation hypothesis.

Role: counts the negative side of the endpoint-adjusted signed distance shells.
-/
theorem finset_card_le_one_of_right_closed_interval_separated (s : Finset ℝ) (a δ : ℝ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) (hinterval : ∀ x ∈ s, a < x ∧ x ≤ a + δ) :
    s.card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  have hdistance := hsep x hx y hy hxy
  obtain ⟨hxlo, hxhi⟩ := hinterval x hx
  obtain ⟨hylo, hyhi⟩ := hinterval y hy
  have hdiff : |x - y| < δ := by
    rw [abs_lt]
    constructor <;> linarith only [hxlo, hxhi, hylo, hyhi]
  exact (not_lt_of_ge hdistance) hdiff

/--
Inputs: a finite set of real points covered by two half-open intervals of equal width, with the
same pairwise separation lower bound.

Claim: the set contains at most two points.

Proof: partition the set according to the first interval, then apply
`finset_card_le_one_of_interval_separated` to each part.

Role: bounds both signed sides of a circular-distance shell.
-/
theorem finset_card_le_two_of_two_interval_cover (s : Finset ℝ) (a b δ : ℝ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|)
    (hcover : ∀ x ∈ s, (a ≤ x ∧ x < a + δ) ∨ (b ≤ x ∧ x < b + δ)) : s.card ≤ 2 := by
  classical
  let p : ℝ → Prop := fun x => a ≤ x ∧ x < a + δ
  let s₁ := s.filter p
  let s₂ := s.filter fun x => ¬p x
  have hsplit : s₁.card + s₂.card = s.card := by
    dsimp only [s₁, s₂]
    exact Finset.card_filter_add_card_filter_not (s := s) (p := p)
  have hcard₁ : s₁.card ≤ 1 := by
    dsimp only [s₁]
    apply finset_card_le_one_of_interval_separated (s.filter p) a δ
    · intro x hx y hy hxy
      exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
  have hcard₂ : s₂.card ≤ 1 := by
    dsimp only [s₂]
    apply finset_card_le_one_of_interval_separated (s.filter fun x => ¬p x) b δ
    · intro x hx y hy hxy
      exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxs, hn⟩
      rcases hcover x hxs with hfirst | hsecond
      · exact False.elim (hn hfirst)
      · exact hsecond
  calc
    s.card = s₁.card + s₂.card := hsplit.symm
    _ ≤ 1 + 1 := Nat.add_le_add hcard₁ hcard₂
    _ = 2 := by norm_num only

/--
Inputs: a finite set of pairwise separated real points covered by a half-open interval and an
open-left, closed-right interval of equal width.

Claim: the set has at most two elements.

Proof: partition the set by membership in the first interval and apply the corresponding
one-interval bound to each part.

Role: counts the two signed sides of floor-indexed circular-distance shells without endpoint gaps.
-/
theorem finset_card_le_two_of_mixed_interval_cover (s : Finset ℝ) (a b δ : ℝ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|)
    (hcover : ∀ x ∈ s, (a ≤ x ∧ x < a + δ) ∨ (b < x ∧ x ≤ b + δ)) : s.card ≤ 2 := by
  classical
  let p : ℝ → Prop := fun x => a ≤ x ∧ x < a + δ
  let s₁ := s.filter p
  let s₂ := s.filter fun x => ¬p x
  have hsplit : s₁.card + s₂.card = s.card := by
    dsimp only [s₁, s₂]
    exact Finset.card_filter_add_card_filter_not (s := s) (p := p)
  have hcard₁ : s₁.card ≤ 1 := by
    dsimp only [s₁]
    apply finset_card_le_one_of_interval_separated (s.filter p) a δ
    · intro x hx y hy hxy
      exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
  have hcard₂ : s₂.card ≤ 1 := by
    dsimp only [s₂]
    apply finset_card_le_one_of_right_closed_interval_separated (s.filter fun x => ¬p x) b δ
    · intro x hx y hy hxy
      exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxs, hn⟩
      rcases hcover x hxs with hfirst | hsecond
      · exact False.elim (hn hfirst)
      · exact hsecond
  calc
    s.card = s₁.card + s₂.card := hsplit.symm
    _ ≤ 1 + 1 := Nat.add_le_add hcard₁ hcard₂
    _ = 2 := by norm_num only

/--
Inputs: a finite set of real representatives with pairwise circular separation at least `δ`,
and a cover by two half-open intervals of width `δ`.

Claim: the set has at most two elements.

Proof: circular separation implies ordinary separation by `δ`; apply the two-interval bound.

Role: bounds the number of signed representatives in one circular-distance shell.
-/
theorem finset_card_le_two_of_circular_separation (s : Finset ℝ) (a b δ : ℝ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ min |x - y| (1 - |x - y|))
    (hcover : ∀ x ∈ s, (a ≤ x ∧ x < a + δ) ∨ (b ≤ x ∧ x < b + δ)) : s.card ≤ 2 := by
  apply finset_card_le_two_of_two_interval_cover s a b δ
  · intro x hx y hy hxy
    exact (hsep x hx y hy hxy).trans (min_le_left _ _)
  · exact hcover

end PseudoPrime.Analysis.FiniteSeparatedSetBounds
