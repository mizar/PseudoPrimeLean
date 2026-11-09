/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltSearch

/-! # Reordered candidate search for uniform Korselt triples -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Enumerate the same factor-range candidates by choosing the middle prime
before the quotient parameter. Primality and equal two-adic valuations filter
the middle factor once before its possible quotient parameters are checked. -/
def korseltFastRange (lo len : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range' lo len).flatMap fun p ↦
    if p.Prime then
      (List.range (Nat.sqrt ((2 ^ 22) / p) + 1)).flatMap fun d ↦
        if p < d + 1 ∧ (d + 1).Prime ∧ padicValNat 2 (p - 1) = padicValNat 2 d then
          (List.range p).filterMap fun a ↦
            if korseltCandidateGood p a d then some (p, a, d) else none
        else []
    else []

/-- Every candidate from the original factor-range enumeration occurs in the
reordered enumeration. The candidate predicate already entails the early
primality and valuation tests, so reordering discards no valid tuple. -/
theorem korselt_range_subset_fast {lo len : ℕ} {x : ℕ × ℕ × ℕ}
    (hm : x ∈ korseltCandidateRange lo len) : x ∈ korseltFastRange lo len := by
  unfold korseltCandidateRange at hm
  obtain ⟨p, hp, hpdata⟩ := List.mem_flatMap.mp hm
  by_cases hprime : p.Prime
  · rw [ite_eq_left hprime] at hpdata
    obtain ⟨a, ha, hadata⟩ := List.mem_flatMap.mp hpdata
    obtain ⟨d, hd, heq⟩ := List.mem_filterMap.mp hadata
    by_cases hgood : korseltCandidateGood p a d = true
    · simp only [hgood, reduceIte, Option.some.injEq] at heq
      subst x
      have hcond := hgood
      simp only [korseltCandidateGood, decide_eq_true_eq] at hcond
      have hpre : p < d + 1 ∧ (d + 1).Prime ∧ padicValNat 2 (p - 1) = padicValNat 2 d := by
        simpa only [Nat.add_sub_cancel] using
          ⟨hcond.1, hcond.2.2.2.2.2.1, hcond.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
      unfold korseltFastRange
      apply List.mem_flatMap.mpr
      refine ⟨p, hp, ?_⟩
      rw [ite_eq_left hprime]
      apply List.mem_flatMap.mpr
      refine ⟨d, hd, ?_⟩
      rw [ite_eq_left hpre]
      apply List.mem_filterMap.mpr
      refine ⟨a, ha, ?_⟩
      rw [hgood]
      rfl
    · have hf : korseltCandidateGood p a d = false := Bool.eq_false_iff.mpr hgood
      simp only [hf, Bool.false_eq_true, reduceIte] at heq
      cases heq
  · simp only [hprime, reduceIte, List.not_mem_nil] at hpdata

/-- An empty reordered search proves the corresponding original candidate
range empty. This transfers each efficient finite certificate to the existing
complete-search and classification theorems. -/
theorem korselt_range_empty_of_fast {lo len : ℕ} (h : korseltFastRange lo len = []) :
    korseltCandidateRange lo len = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  have hf := korselt_range_subset_fast hx
  rw [h] at hf
  exact List.not_mem_nil hf

end PseudoPrime.PrimeTestBounds.MillerRabin
