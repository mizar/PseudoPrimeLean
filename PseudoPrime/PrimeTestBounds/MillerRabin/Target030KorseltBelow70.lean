/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030KorseltBelow60
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Korselt60to70

/-! # Uniform Korselt classification with extensible search bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The empty factor range from 60 to 69 leaves the six-candidate list unchanged. -/
theorem target030_candidates_below70 : target030CandidateRows 70 = target030CandidateRows 50 := by
  have h := target030_rows_add_empty 60 10 target030_candidates_60to70
  norm_num only at h
  exact h.trans target030_candidates_below60

/-- Whenever a checked search bound adds no new candidate beyond 50, every
bounded uniform Korselt triple below that factor bound is one of the six known
products. This allows subsequent empty blocks to reuse the classification. -/
theorem uniformKorselt_cases_of_rows {N n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < N)
    (hrows : target030CandidateRows N = target030CandidateRows 50) :
    n ∈ [8911, 314821, 29341, 1024651, 410041, 1152271] := by
  obtain ⟨hpb, a, ha, hap, hdiv, hadiv, hrform⟩ :=
    uniformKorselt_finite_parameters hn hp hq hrp hpq hqr hu hbound
  have hm : (p, a, q - 1) ∈ target030CandidateRows N :=
    uniformKorselt_candidate_mem hu hn hp hq hrp hpq hqr hbound hsmall ha hap hdiv hadiv hrform
  rw [hrows, target030_candidates_below50] at hm
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

/-- A bounded uniform Korselt triple with ordered smallest factor below 70 is
one of the six explicit products from the completed smaller-factor blocks. -/
theorem uniformKorselt_below70_cases {n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < 70) :
    n ∈ [8911, 314821, 29341, 1024651, 410041, 1152271] :=
  uniformKorselt_cases_of_rows hu hbound hn hp hq hrp hpq hqr hsmall target030_candidates_below70

end PseudoPrime.PrimeTestBounds.MillerRabin
