/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030KorseltBelow50
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Korselt50to60

/-! # Combined uniform Korselt search below smallest factor 60 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An empty next factor range leaves the accumulated candidate list unchanged.
This connects separately checked blocks without repeating their evaluation. -/
theorem target030_rows_add_empty (m n : ℕ) (h : target030CandidateRange m n = []) :
    target030CandidateRows (m + n) = target030CandidateRows m := by
  have hsplit := target030CandidateRows_split m n
  have hzero : target030CandidateRange 0 m = target030CandidateRows m := by
    simp only [target030CandidateRange, target030CandidateRows, List.range_eq_range']
  rw [hzero, h, List.append_nil] at hsplit
  exact hsplit

/-- The empty block from 50 to 59 adds no candidate to the search below 50. -/
theorem target030_candidates_below60 : target030CandidateRows 60 = target030CandidateRows 50 := by
  simpa only using target030_rows_add_empty 50 10 target030_candidates_50to60

/-- A bounded uniform Korselt triple with ordered smallest factor below 60 is
one of the six explicit products already found below 50. -/
theorem uniformKorselt_below60_cases {n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < 60) :
    n ∈ [8911, 314821, 29341, 1024651, 410041, 1152271] := by
  obtain ⟨hpb, a, ha, hap, hdiv, hadiv, hrform⟩ :=
    uniformKorselt_finite_parameters hn hp hq hrp hpq hqr hu hbound
  have hm : (p, a, q - 1) ∈ target030CandidateRows 60 :=
    uniformKorselt_candidate_mem hu hn hp hq hrp hpq hqr hbound hsmall ha hap hdiv hadiv hrform
  rw [target030_candidates_below60, target030_candidates_below50] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  have hp50 : p < 50 := by
    rcases hm with h | h | h | h | h | h
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
  exact uniformKorselt_below50_cases hu hbound hn hp hq hrp hpq hqr hp50

end PseudoPrime.PrimeTestBounds.MillerRabin
