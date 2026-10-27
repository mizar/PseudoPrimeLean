/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ConductorSumComparison

/-! # Conductor cost from a three-character annihilator classification

An exact enumeration gives index four, and pairwise product conductors give
the unnormalized conductor-log cost 2 log n.
The enumeration and conductor identities remain explicit arithmetic inputs.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open Classical in
/-- A subgroup whose nonprincipal annihilator consists of three distinct characters
has index four. Count the erased finite set and use finite character duality.
This converts a character classification into the index needed by the Gaussian branch. -/
theorem index_four_of_three_nonprincipal_annihilator {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (a b c : NumberTheory.subgroupAnnihilator H) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H) = {a, b, c}) :
    H.index = 4 := by
  classical
  have habc : a ∉ ({b, c} : Finset (NumberTheory.subgroupAnnihilator H)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, hab, hac, or_self, not_false_eq_true]
  have hbc' : b ∉ ({c} : Finset (NumberTheory.subgroupAnnihilator H)) := by
    simp only [Finset.mem_singleton, hbc, not_false_eq_true]
  have hcard := Finset.card_erase_add_one (Finset.mem_univ (1 : NumberTheory.subgroupAnnihilator H))
  rw [hs, Finset.card_insert_of_notMem habc, Finset.card_insert_of_notMem hbc',
    Finset.card_singleton, Finset.card_univ, NumberTheory.card_subgroupAnnihilator] at hcard
  exact hcard.symm

open Classical in
/-- If the three distinct nonprincipal annihilator characters have conductors
p*q, p*r and q*r, and n=p*q*r with positive factors, their conductor-log sum
is exactly twice log n. Expand the classified finite sum and each product logarithm.
This supplies the conductor saving for the Gaussian three-character branch. -/
theorem subgroupConductorLogSum_eq_twice_log_of_three_conductors {n p q r : ℕ} [NeZero n]
    (H : Subgroup (ZMod n)ˣ) (a b c : NumberTheory.subgroupAnnihilator H) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hs : Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H) = {a, b, c})
    (ha : a.val.conductor = p * q) (hb : b.val.conductor = p * r) (hc : c.val.conductor = q * r)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hn : n = p * q * r) :
    subgroupConductorLogSum H = 2 * Real.log n := by
  classical
  have habc : a ∉ ({b, c} : Finset (NumberTheory.subgroupAnnihilator H)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, hab, hac, or_self, not_false_eq_true]
  have hbc' : b ∉ ({c} : Finset (NumberTheory.subgroupAnnihilator H)) := by
    simp only [Finset.mem_singleton, hbc, not_false_eq_true]
  rw [subgroupConductorLogSum, hs, Finset.sum_insert habc, Finset.sum_insert hbc',
    Finset.sum_singleton, ha, hb, hc, hn]
  have hp0 : (p : ℝ) ≠ 0 := (Nat.cast_pos.mpr hp).ne'
  have hq0 : (q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hq).ne'
  have hr0 : (r : ℝ) ≠ 0 := (Nat.cast_pos.mpr hr).ne'
  simp only [Nat.cast_mul]
  rw [Real.log_mul hp0 hq0, Real.log_mul hp0 hr0, Real.log_mul hq0 hr0,
    Real.log_mul (mul_ne_zero hp0 hq0) hr0, Real.log_mul hp0 hq0]
  ring

/-- Characters with conductors p*q, p*r and q*r are pairwise distinct when
p,q,r are positive and pairwise distinct. Equality of characters would equate
conductors; cancel the common positive factor. This verifies distinctness of the
three nonprincipal characters without a separate character-level assumption. -/
theorem three_characters_ne_of_pairwise_product_conductors {n p q r : ℕ} [NeZero n]
    (H : Subgroup (ZMod n)ˣ) (a b c : NumberTheory.subgroupAnnihilator H)
    (ha : a.val.conductor = p * q) (hb : b.val.conductor = p * r) (hc : c.val.conductor = q * r)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have hab : a ≠ b := by
    intro h
    have he := congrArg (fun d : NumberTheory.subgroupAnnihilator H ↦ d.val.conductor) h
    rw [ha, hb] at he
    exact hqr (Nat.eq_of_mul_eq_mul_left hp he)
  have hac : a ≠ c := by
    intro h
    have he := congrArg (fun d : NumberTheory.subgroupAnnihilator H ↦ d.val.conductor) h
    rw [ha, hc, Nat.mul_comm p q] at he
    exact hpr (Nat.eq_of_mul_eq_mul_left hq he)
  have hbc : b ≠ c := by
    intro h
    have he := congrArg (fun d : NumberTheory.subgroupAnnihilator H ↦ d.val.conductor) h
    rw [hb, hc] at he
    exact hpq (Nat.eq_of_mul_eq_mul_right hr he)
  exact ⟨hab, hac, hbc⟩

open Classical in
/-- At index four, three pairwise distinct nonprincipal annihilator characters
exhaust the nonprincipal finite set. Insert the three known members, count them,
and use finite character duality to prove equality. This removes the enumeration
premise when membership, nonprincipality and index are established arithmetically. -/
theorem nonprincipal_annihilator_eq_three_of_index_four {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hi : H.index = 4) (a b c : NumberTheory.subgroupAnnihilator H) (ha : a ≠ 1) (hb : b ≠ 1)
    (hc : c ≠ 1) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H) = {a, b, c} := by
  classical
  have habc : a ∉ ({b, c} : Finset (NumberTheory.subgroupAnnihilator H)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, hab, hac, or_self, not_false_eq_true]
  have hbc' : b ∉ ({c} : Finset (NumberTheory.subgroupAnnihilator H)) := by
    simp only [Finset.mem_singleton, hbc, not_false_eq_true]
  have hsub : ({a, b, c} : Finset (NumberTheory.subgroupAnnihilator H)) ⊆ Finset.univ.erase 1 := by
    intro d hd
    rcases Finset.mem_insert.mp hd with hd | hd
    · subst d
      exact Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩
    · rcases Finset.mem_insert.mp hd with hd | hd
      · subst d
        exact Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩
      · have hd := Finset.mem_singleton.mp hd
        subst d
        exact Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩
  apply (Finset.eq_of_subset_of_card_le hsub _).symm
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    NumberTheory.card_subgroupAnnihilator, hi, Finset.card_insert_of_notMem habc,
    Finset.card_insert_of_notMem hbc', Finset.card_singleton]

end PseudoPrime.LLS.PaperStatements
