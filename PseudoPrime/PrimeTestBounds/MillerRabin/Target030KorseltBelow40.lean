/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030KorseltSmall
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Korselt20to40

/-! # Combined uniform Korselt search below smallest factor 40 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The two certified factor ranges give exactly four candidate parameters
below 40. The range-splitting identity combines their independent checks. -/
theorem target030_candidates_below40 :
    target030CandidateRows 40 = [(7, 2, 18), (13, 2, 60), (13, 8, 36), (19, 14, 198)] := by
  have hsplit := target030CandidateRows_split 20 20
  norm_num only at hsplit
  have hzero : target030CandidateRange 0 20 = target030CandidateRows 20 := by
    simp only [target030CandidateRange, target030CandidateRows, List.range_eq_range']
  rw [hzero, target030_candidates_20to40, List.append_nil, target030_candidates_below20] at hsplit
  exact hsplit

/-- A bounded uniform Korselt triple with ordered smallest factor below 40 is
one of the four products from the first search block. The second block has no
candidates, so the earlier classification applies. -/
theorem uniformKorselt_below40_cases {n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < 40) :
    n = 8911 ∨ n = 29341 ∨ n = 314821 ∨ n = 1024651 := by
  obtain ⟨hpb, a, ha, hap, hdiv, hadiv, hrform⟩ :=
    uniformKorselt_finite_parameters hn hp hq hrp hpq hqr hu hbound
  have hm : (p, a, q - 1) ∈ target030CandidateRows 40 :=
    uniformKorselt_candidate_mem hu hn hp hq hrp hpq hqr hbound hsmall ha hap hdiv hadiv hrform
  rw [target030_candidates_below40] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  have hp20 : p < 20 := by
    rcases hm with h | h | h | h
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
  exact uniformKorselt_below20_cases hu hbound hn hp hq hrp hpq hqr hp20

end PseudoPrime.PrimeTestBounds.MillerRabin
